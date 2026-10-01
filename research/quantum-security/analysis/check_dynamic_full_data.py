"""Compare parameterized full-lock pushes with the pinned Lean wire fixture.

This is a finite differential test of builder output. The AST audit supplies
the separate source-level byte-value independence argument; neither test is a
formal Python-semantics or compiled-Core refinement theorem.
"""

import argparse
import ast
import hashlib
import json
import random
import sys
from pathlib import Path


PINNED_SHA256 = "c7e52af90bd0d9fce9834fce26dcd67aee0d7751ee228d9730873c4d12659a5c"
BASE_LOCK_SHA256 = "44f34e665e756e239aed514a530c136f582a0812437c4f32140a1ebe83628bba"


def fixture_chunks(path: Path) -> list[bytes]:
    source = path.read_text()
    body = source.split("def chunks : List Bytes := [\n", 1)[1].split("\n]\n", 1)[0]
    chunks = ast.literal_eval("[" + body + "\n]")
    assert len(chunks) == 880
    return [bytes(chunk) for chunk in chunks]


def parse_chunks(script: bytes) -> list[bytes]:
    chunks = []
    pos = 0
    while pos < len(script):
        start = pos
        op = script[pos]
        pos += 1
        if 1 <= op <= 75:
            pos += op
            assert pos <= len(script)
        elif op in (0x4c, 0x4d, 0x4e):
            raise AssertionError("Unexpected PUSHDATA opcode")
        chunks.append(script[start:pos])
    assert len(chunks) == 880
    return chunks


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--app-root", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    app_root = args.app_root.resolve()
    source_path = app_root / "worker/cpu/bitcoin_tx.py"
    source_hash = hashlib.sha256(source_path.read_bytes()).hexdigest()
    assert source_hash == PINNED_SHA256
    sys.path.insert(0, str(source_path.parent))
    import bitcoin_tx as bt
    import secp256k1 as ec

    rng = random.Random("QSB security analysis: PUBLIC DISPOSABLE TEST MATERIAL")
    builder = bt.QSBScriptBuilder(150, 8, 1, 7, 2, hash_mode="sha256")
    original_urandom = bt.os.urandom
    try:
        bt.os.urandom = rng.randbytes
        builder.generate_keys()
    finally:
        bt.os.urandom = original_urandom

    def nonce_sig(label: bytes) -> bytes:
        k = int.from_bytes(hashlib.sha256(label + b"_nonce").digest(), "big") % ec.N
        r = ec.point_mul(k, ec.G)[0] % ec.N
        s = max(1, int.from_bytes(hashlib.sha256(label + b"_s").digest()[:16],
                                  "big") % (ec.N // 2))
        return ec.encode_der_sig(r, s, sighash=1)

    fixture = fixture_chunks(root / "QSB/EncodedLayout.lean")
    base_sigs = tuple(nonce_sig(label) for label in
                      (b"qsb_pin", b"qsb_r0", b"qsb_r1"))
    baseline = builder.build_full_script(*base_sigs)
    assert hashlib.sha256(baseline).hexdigest() == BASE_LOCK_SHA256
    assert parse_chunks(baseline) == fixture

    cases = []

    def check(name: str, signatures: tuple[bytes, bytes, bytes]) -> None:
        pin, nonce0, nonce1 = signatures
        expected = list(fixture)
        expected[0] = bt.push_data(pin)
        for i in range(150):
            expected[6 + i] = bt.push_data(builder.hors_commitments[0][149 - i])
            expected[447 + i] = bt.push_data(builder.hors_commitments[1][149 - i])
        expected[307] = bt.push_data(nonce0)
        expected[748] = bt.push_data(nonce1)
        script = builder.build_full_script(pin, nonce0, nonce1)
        actual = parse_chunks(script)
        assert actual == expected, name
        assert script == b"".join(expected), name
        assert actual[446] == actual[879] == b"\xae"
        cases.append({
            "name": name,
            "pin_length": len(pin),
            "nonce0_length": len(nonce0),
            "nonce1_length": len(nonce1),
            "script_sha256": hashlib.sha256(script).hexdigest(),
            "byte_length": len(script),
        })

    check("literal_fixture", base_sigs)
    builder.hors_commitments[0][7] = bytes(range(20))
    builder.hors_commitments[1][149] = bytes.fromhex(
        "3011020101020c01000000000000000000001103")
    check("both_rounds_changed_nonce20", (b"\x01" * 20, b"\x02" * 20,
                                           b"\x03" * 20))
    check("all_three_empty", (b"", b"", b""))
    check("direct_push_boundary_75", (b"\x51" * 75, b"\x52" * 75,
                                      b"\x53" * 75))

    report = {
        "builder_sha256": source_hash,
        "lean_fixture_script_sha256": BASE_LOCK_SHA256,
        "instruction_count": 880,
        "first_round_data_indices": [6, 156, 307],
        "first_checkmultisig_index": 446,
        "second_round_data_indices": [447, 597, 748],
        "final_checkmultisig_index": 879,
        "cases": cases,
        "scope": "Four disposable full-lock builder runs; exact chunk equality to the parameterized Lean fixture at these inputs only. No consensus spend or universal Python proof.",
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    print("Checked four disposable parameterized full-lock outputs.")


if __name__ == "__main__":
    main()
