"""Compare source-shaped ScriptNum cases with the pinned Core 27.2 adapter.

The tested lock executes OP_1ADD, compares its serialized result against an
independent sign-magnitude expectation, and fails on the first mismatch. The
cases cover every one-byte encoding, selected nonminimal boundaries, and the
canonical encodings of all integers from -1023 through 1023. This is a finite
differential probe of numeric opcodes, not a full QSB spend.
"""

import argparse
import hashlib
import json
import subprocess
import sys
from pathlib import Path


def scriptnum(raw: bytes) -> int:
    if len(raw) > 4:
        raise ValueError("four-byte operand limit")
    if not raw:
        return 0
    word = int.from_bytes(raw, "little")
    sign_bit = 0x80 << (8 * (len(raw) - 1))
    return -(word & ~sign_bit) if raw[-1] & 0x80 else word


def encode_scriptnum(value: int) -> bytes:
    if value == 0:
        return b""
    magnitude = abs(value)
    raw = magnitude.to_bytes((magnitude.bit_length() + 7) // 8, "little")
    if raw[-1] & 0x80:
        return raw + (b"\x80" if value < 0 else b"\x00")
    if value < 0:
        return raw[:-1] + bytes([raw[-1] | 0x80])
    return raw


def cases() -> list[bytes]:
    rows = [bytes([b]) for b in range(256)]
    tops = (0x00, 0x01, 0x7f, 0x80, 0xff)
    for length in (2, 3, 4):
        for low in tops:
            for high in tops:
                rows.append(bytes([low] + [0x42] * (length - 2) + [high]))
    rows.extend((b"", b"\x0a\x00", b"\x98\x00\x00",
                 b"\x98\x80", b"\xff\xff\xff\x7f",
                 b"\xff\xff\xff\xff"))
    rows.extend(encode_scriptnum(value) for value in range(-1023, 1024))
    return rows


def verify(bt, native_root: Path, image: str, raw_cases: list[bytes],
           expected: bool) -> dict:
    tx = bt.Transaction(version=1, locktime=0)
    tx.add_input(bt.TxIn(b"\x11" * 32, 0, bytes([bt.OP_1])))
    tx.add_input(bt.TxIn(b"\x22" * 32, 0,
                         b"".join(bt.push_data(raw) for raw in reversed(raw_cases))))
    tx.add_output(bt.TxOut(90000, bytes([bt.OP_1])))
    lock = bytearray()
    for raw in raw_cases:
        lock.append(0x8b)  # OP_1ADD: forces four-byte CScriptNum parsing.
        lock += bt.push_data(encode_scriptnum(scriptnum(raw) + 1))
        lock.append(0x88)  # OP_EQUALVERIFY checks Core's serialized result.
    lock.append(bt.OP_1)
    payload = f"{tx.serialize().hex()}\n2\n1000\n51\n100000\n{lock.hex()}\n"
    result = subprocess.run(
        ["docker", "run", "--rm", "--network", "none", "--read-only",
         "--cap-drop=ALL", "--security-opt=no-new-privileges",
         "--platform=linux/arm64", "-i",
         "-v", f"{native_root.resolve()}:/native:ro", image,
         "/native/qsb-consensus"],
        input=payload, text=True, capture_output=True, timeout=30,
    )
    if result.returncode not in (0, 1):
        raise RuntimeError(f"Core adapter unavailable: {result.stderr}")
    accepted = (result.returncode == 0 and
                result.stdout.strip() == "core-27.2-api2-all-inputs-valid")
    assert accepted == expected, (raw_cases, result)
    return {
        "cases": len(raw_cases),
        "accepted": accepted,
        "transaction_sha256": hashlib.sha256(tx.serialize()).hexdigest(),
        "test_lock_sha256": hashlib.sha256(lock).hexdigest(),
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--app-root", type=Path, required=True)
    parser.add_argument("--native-root", type=Path, required=True)
    parser.add_argument("--image", required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    inventory = json.loads((Path(__file__).resolve().parents[1] /
                            "evidence/source-inventory.json").read_text())
    source_hashes = {}
    for relative in ("worker/cpu/bitcoin_tx.py", "consensus/verify.cpp"):
        digest = hashlib.sha256((args.app_root / relative).read_bytes()).hexdigest()
        if digest != inventory["app"]["files"][relative]:
            raise RuntimeError(f"unpinned app source: {relative}")
        source_hashes[relative] = digest
    sys.path.insert(0, str(args.app_root / "worker/cpu"))
    import bitcoin_tx as bt

    raw_cases = cases()
    groups = [raw_cases[i:i + 90] for i in range(0, len(raw_cases), 90)]
    results = [verify(bt, args.native_root, args.image, group, True)
               for group in groups]
    # The same opcode must reject a five-byte operand, even when its value is 1.
    tx = bt.Transaction(version=1, locktime=0)
    tx.add_input(bt.TxIn(b"\x11" * 32, 0, bytes([bt.OP_1])))
    tx.add_input(bt.TxIn(b"\x22" * 32, 0, bt.push_data(b"\x01\x00\x00\x00\x00")))
    tx.add_output(bt.TxOut(90000, bytes([bt.OP_1])))
    lock = bytes([0x8b, bt.OP_1])
    payload = f"{tx.serialize().hex()}\n2\n1000\n51\n100000\n{lock.hex()}\n"
    overflow = subprocess.run(
        ["docker", "run", "--rm", "--network", "none", "--read-only",
         "--cap-drop=ALL", "--security-opt=no-new-privileges",
         "--platform=linux/arm64", "-i",
         "-v", f"{args.native_root.resolve()}:/native:ro", args.image,
         "/native/qsb-consensus"],
        input=payload, text=True, capture_output=True, timeout=30,
    )
    assert overflow.returncode == 1, overflow
    report = {
        "scope": "finite numeric-opcode probe on a disposable two-input transaction",
        "source_revision": subprocess.check_output(
            ["git", "-C", str(args.app_root), "rev-parse", "HEAD"], text=True
        ).strip(),
        "source_file_sha256": source_hashes,
        "native_files_sha256": {
            p.name: hashlib.sha256(p.read_bytes()).hexdigest()
            for p in args.native_root.iterdir() if p.is_file()
        },
        "image": args.image,
        "tested_encodings": len(raw_cases),
        "groups": results,
        "five_byte_operand_rejected": True,
    }
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"tested_encodings": len(raw_cases),
                      "groups": len(results),
                      "five_byte_operand_rejected": True}))


if __name__ == "__main__":
    main()
