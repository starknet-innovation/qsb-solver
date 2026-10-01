"""Check the final data-block boundary in two disposable Config A builds."""

import argparse
import hashlib
import json
import random
import sys
from pathlib import Path


def decode(script: bytes):
    result = []
    pos = 0
    while pos < len(script):
        start = pos
        op = script[pos]
        pos += 1
        if op == 0:
            data = b""
        elif 0x51 <= op <= 0x60:
            data = bytes([op - 0x50])
        elif 1 <= op <= 75:
            data = script[pos : pos + op]
            assert len(data) == op
            pos += op
        else:
            data = None
        result.append((start, pos, op, data))
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--app-root", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    app_root = args.app_root.resolve()
    sys.path.insert(0, str(app_root / "worker/cpu"))
    import bitcoin_tx as bt
    import secp256k1 as ec

    source_hash = hashlib.sha256(
        (app_root / "worker/cpu/bitcoin_tx.py").read_bytes()
    ).hexdigest()
    assert source_hash == "c7e52af90bd0d9fce9834fce26dcd67aee0d7751ee228d9730873c4d12659a5c"

    def nonce_sig(label):
        k = int.from_bytes(hashlib.sha256(label + b"_nonce").digest(), "big") % ec.N
        r = ec.point_mul(k, ec.G)[0] % ec.N
        s = max(
            1,
            int.from_bytes(hashlib.sha256(label + b"_s").digest()[:16], "big")
            % (ec.N // 2),
        )
        return ec.encode_der_sig(r, s, sighash=1)

    nonces = tuple(nonce_sig(x) for x in (b"qsb_pin", b"qsb_r0", b"qsb_r1"))
    built = []
    for seed in (
        "QSB security analysis: PUBLIC DISPOSABLE TEST MATERIAL",
        "QSB dynamic final data: second PUBLIC DISPOSABLE setup",
    ):
        builder = bt.QSBScriptBuilder(150, 8, 1, 7, 2, hash_mode="sha256")
        rng = random.Random(seed)
        original = bt.os.urandom
        try:
            bt.os.urandom = rng.randbytes
            builder.generate_keys()
        finally:
            bt.os.urandom = original
        script = builder.build_full_script(*nonces)
        ops = decode(script)
        assert len(ops) == 880
        for i in range(150):
            assert ops[447 + i][3] == builder.hors_commitments[1][149 - i]
            assert ops[597 + i][3] == builder.dummy_sigs[1][149 - i]
        assert ops[747][3] == b""
        assert ops[748][3] == nonces[2]
        built.append((builder, script, ops))

    first, second = built
    assert hashlib.sha256(first[1]).hexdigest() == (
        "44f34e665e756e239aed514a530c136f582a0812437c4f32140a1ebe83628bba"
    )
    assert first[0].dummy_sigs[1] == second[0].dummy_sigs[1]
    assert first[0].hors_commitments[1] != second[0].hors_commitments[1]
    first_suffix = first[1][first[2][749][0] :]
    second_suffix = second[1][second[2][749][0] :]
    assert first_suffix == second_suffix

    report = {
        "builder_sha256": source_hash,
        "base_script_sha256": hashlib.sha256(first[1]).hexdigest(),
        "alternate_script_sha256": hashlib.sha256(second[1]).hexdigest(),
        "instruction_count": 880,
        "final_data_instruction_range": [447, 749],
        "final_commitment_pushes_reverse_indexed": True,
        "final_dummy_pushes_reverse_indexed": True,
        "dummy_bytes_equal_across_setups": True,
        "commitments_differ_across_setups": True,
        "suffix_from_instruction_749_equal": True,
        "scope": "Two disposable builder executions; not a universal source or Core proof.",
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    print("Checked two disposable dynamic final data blocks and suffixes.")


if __name__ == "__main__":
    main()
