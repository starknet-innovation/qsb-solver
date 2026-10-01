"""Compare all legacy hash-type branches with pinned Core 27.2 vectors.

The preimage is built from independently parsed raw transaction fields rather
than the app's serializer. This is differential evidence, not a proof of C++
refinement or of behavior for every transaction and scriptCode.
"""

import argparse
import hashlib
import json
import struct
import sys
from pathlib import Path


CORE_VECTORS_SHA256 = "52cf23c2076e7f129c71d5508631d3e5ae3be1b1cb0585c0e23bbb4bb373e924"
SIMPLE_SCRIPT_OPS = {0x00, 0x51, 0x52, 0x53, 0xac, 0x63, 0x65, 0x6a, 0xab}


class Reader:
    def __init__(self, data: bytes):
        self.data = data
        self.offset = 0

    def take(self, n: int) -> bytes:
        if n < 0 or self.offset + n > len(self.data):
            raise ValueError("truncated transaction")
        chunk = self.data[self.offset:self.offset + n]
        self.offset += n
        return chunk

    def uint(self, n: int) -> int:
        return int.from_bytes(self.take(n), "little")

    def compact_size(self) -> int:
        marker = self.uint(1)
        if marker < 253:
            return marker
        width, minimum = {253: (2, 253), 254: (4, 65536), 255: (8, 4294967296)}[marker]
        value = self.uint(width)
        if value < minimum:
            raise ValueError("noncanonical CompactSize")
        return value

    def script(self) -> bytes:
        return self.take(self.compact_size())


def parse_legacy_tx(raw: bytes):
    """Return raw wire fields, rejecting witness markers and trailing bytes."""
    r = Reader(raw)
    version = r.uint(4)
    input_count = r.compact_size()
    if input_count == 0:
        raise ValueError("zero inputs or witness serialization")
    inputs = []
    for _ in range(input_count):
        inputs.append((r.take(32), r.uint(4), r.script(), r.uint(4)))
    outputs = []
    for _ in range(r.compact_size()):
        outputs.append((r.take(8), r.script()))
    locktime = r.uint(4)
    if r.offset != len(raw):
        raise ValueError("trailing transaction bytes")
    return version, inputs, outputs, locktime


def source_shaped_preimage(fields, input_index: int, script_code: bytes,
                           hash_type: int) -> bytes | None:
    """Write Core's legacy branches, returning None for the SINGLE bug."""
    version, inputs, outputs, locktime = fields
    if not 0 <= input_index < len(inputs):
        raise ValueError("invalid signed input index")
    base = hash_type & 31
    if base == 3 and input_index >= len(outputs):
        return None
    chosen = [inputs[input_index]] if hash_type & 128 else inputs
    data = struct.pack("<I", version) + compact_size(len(chosen))
    for i, (txid, vout, _, sequence) in enumerate(chosen):
        original_index = input_index if hash_type & 128 else i
        script = script_code if original_index == input_index else b""
        if original_index != input_index and base in (2, 3):
            sequence = 0
        data += txid + struct.pack("<I", vout)
        data += compact_size(len(script)) + script + struct.pack("<I", sequence)
    if base == 2:
        data += compact_size(0)
    elif base == 3:
        data += compact_size(input_index + 1)
        data += (b"\xff" * 8 + b"\x00") * input_index
        amount, script = outputs[input_index]
        data += amount + compact_size(len(script)) + script
    else:
        data += compact_size(len(outputs))
        for amount, script in outputs:
            data += amount + compact_size(len(script)) + script
    return data + struct.pack("<II", locktime, hash_type)


def compact_size(value: int) -> bytes:
    if value < 253:
        return bytes((value,))
    if value <= 0xffff:
        return b"\xfd" + struct.pack("<H", value)
    if value <= 0xffffffff:
        return b"\xfe" + struct.pack("<I", value)
    return b"\xff" + struct.pack("<Q", value)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--vectors", type=Path, required=True)
    parser.add_argument("--app-root", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    pinned = json.loads((root / "evidence/source-inventory.json").read_text())["app"]
    app_file = args.app_root / "worker/cpu/bitcoin_tx.py"
    app_hash = hashlib.sha256(app_file.read_bytes()).hexdigest()
    assert app_hash == pinned["files"]["worker/cpu/bitcoin_tx.py"]
    sys.path.insert(0, str(app_file.parent))
    import bitcoin_tx as bt

    vector_bytes = args.vectors.read_bytes()
    assert hashlib.sha256(vector_bytes).hexdigest() == CORE_VECTORS_SHA256
    rows = json.loads(vector_bytes)
    assert rows[0] == ["raw_transaction, script, input_index, hashType, signature_hash (result)"]
    assert len(rows) == 501
    checked = []
    script_with_separator = 0
    branches = {"all_like": 0, "none": 0, "single": 0, "single_bug": 0}
    anyone_can_pay = 0
    for index, row in enumerate(rows[1:], 1):
        assert len(row) == 5
        raw_hex, script_hex, input_index, signed_hash_type, expected_hex = row
        hash_type = signed_hash_type & 0xffffffff
        fields = parse_legacy_tx(bytes.fromhex(raw_hex))
        script = bytes.fromhex(script_hex)
        # RandomScript in this pinned Core corpus emits only these one-byte
        # opcodes. Hence removing 0xab here removes complete CODESEPARATOR
        # opcodes, never pushed data.
        assert set(script) <= SIMPLE_SCRIPT_OPS
        script_code = script.replace(b"\xab", b"")
        script_with_separator += b"\xab" in script
        preimage = source_shaped_preimage(fields, input_index, script_code, hash_type)
        digest = (b"\x01" + b"\x00" * 31) if preimage is None else hashlib.sha256(
            hashlib.sha256(preimage).digest()).digest()
        # uint256::GetHex prints the digest's internal bytes in reverse order.
        assert digest[::-1].hex() == expected_hex, (index, digest.hex(), expected_hex)

        version, inputs, outputs, locktime = fields
        tx = bt.Transaction(version, locktime)
        for txid, vout, sig_script, sequence in inputs:
            tx.add_input(bt.TxIn(txid, vout, sig_script, sequence))
        for amount, output_script in outputs:
            tx.add_output(bt.TxOut(int.from_bytes(amount, "little", signed=True), output_script))
        assert tx.serialize().hex() == raw_hex
        assert tx.sighash(input_index, script_code, hash_type) == int.from_bytes(digest, "big")
        base = hash_type & 31
        branch = "single_bug" if preimage is None else (
            "none" if base == 2 else "single" if base == 3 else "all_like")
        branches[branch] += 1
        anyone_can_pay += bool(hash_type & 128)
        checked.append({"core_index": index, "hash_type_u32": hash_type,
                         "input_count": len(inputs), "output_count": len(outputs),
                         "script_has_codeseparator": b"\xab" in script,
                         "branch": branch, "anyone_can_pay": bool(hash_type & 128),
                         "preimage_sha256": None if preimage is None else hashlib.sha256(preimage).hexdigest()})

    assert len(checked) == 500
    report = {
        "scope": "Core 27.2 legacy hash types in the pinned 500-vector corpus; source-shaped independent preimages and pinned app",
        "core_source_url": "https://github.com/bitcoin/bitcoin/blob/v27.2/src/test/data/sighash.json",
        "core_harness_url": "https://github.com/bitcoin/bitcoin/blob/v27.2/src/test/sighash_tests.cpp",
        "core_vectors_sha256": CORE_VECTORS_SHA256,
        "app_revision": pinned["revision"],
        "app_serializer_sha256": app_hash,
        "total_vectors": len(rows) - 1,
        "checked_vectors": len(checked),
        "branches": branches,
        "anyone_can_pay_vectors": anyone_can_pay,
        "literal_hash_type_one_vectors": sum(row[3] == 1 for row in rows[1:]),
        "with_codeseparator": script_with_separator,
        "with_multiple_inputs": sum(row["input_count"] > 1 for row in checked),
        "with_multiple_outputs": sum(row["output_count"] > 1 for row in checked),
        "first_checked": checked[:5],
        "last_checked": checked[-5:],
        "result": "all 500 Core expected digests match independent source-shaped bytes and pinned app sighash",
    }
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({key: report[key] for key in (
        "total_vectors", "checked_vectors", "branches", "anyone_can_pay_vectors",
        "with_codeseparator", "result")}, indent=2))


if __name__ == "__main__":
    main()
