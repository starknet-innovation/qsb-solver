"""Inventory final signature pushes and sequential deletion in the exact lock.

This is a deterministic source-fixture check, not a theorem about every setup
or Bitcoin Core's binary. It verifies the same script SHA-256 as ByteLayout and
checks opcode-boundary occurrences and sampled ten-signature deletion orders.
"""

import argparse
import hashlib
import json
import random
import subprocess
import sys
from pathlib import Path


def opcode_boundaries(script: bytes) -> list[int]:
    boundaries = []
    pc = 0
    while pc < len(script):
        boundaries.append(pc)
        op = script[pc]
        if 1 <= op <= 75:
            size = 1 + op
        elif op == 0x4C:
            size = 2 + script[pc + 1]
        elif op == 0x4D:
            size = 3 + int.from_bytes(script[pc + 1:pc + 3], "little")
        elif op == 0x4E:
            size = 5 + int.from_bytes(script[pc + 1:pc + 5], "little")
        else:
            size = 1
        assert pc + size <= len(script)
        pc += size
    assert pc == len(script)
    return boundaries


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--app-root", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    sys.path.insert(0, str(args.app_root / "worker/cpu"))
    import bitcoin_tx as bt
    import secp256k1 as ec

    builder = bt.QSBScriptBuilder(150, 8, 1, 7, 2, hash_mode="sha256")
    rng = random.Random("QSB security analysis: PUBLIC DISPOSABLE TEST MATERIAL")
    old_random = bt.os.urandom
    try:
        bt.os.urandom = rng.randbytes
        builder.generate_keys()
    finally:
        bt.os.urandom = old_random

    def nonce_sig(label: bytes) -> bytes:
        k = int.from_bytes(hashlib.sha256(label + b"_nonce").digest(), "big") % ec.N
        r = ec.point_mul(k, ec.G)[0] % ec.N
        s = max(1, int.from_bytes(hashlib.sha256(label + b"_s").digest()[:16],
                                  "big") % (ec.N // 2))
        return ec.encode_der_sig(r, s, sighash=1)

    pin, first_nonce, final_nonce = (nonce_sig(x) for x in
                                     (b"qsb_pin", b"qsb_r0", b"qsb_r1"))
    script = builder.build_full_script(pin, first_nonce, final_nonce)
    source_hash = hashlib.sha256(
        (args.app_root / "worker/cpu/bitcoin_tx.py").read_bytes()).hexdigest()
    ec_hash = hashlib.sha256(
        (args.app_root / "worker/cpu/secp256k1.py").read_bytes()).hexdigest()
    script_hash = hashlib.sha256(script).hexdigest()
    layout = json.loads((root / "evidence/byte-layout-map.json").read_text())
    pinned = json.loads((root / "evidence/source-inventory.json").read_text())["app"]
    assert source_hash == layout["builder_sha256"]
    assert source_hash == pinned["files"]["worker/cpu/bitcoin_tx.py"]
    assert ec_hash == pinned["files"]["worker/cpu/secp256k1.py"]
    assert script_hash == layout["script_sha256"]
    boundaries = opcode_boundaries(script)
    assert len(boundaries) == 880
    chunks = [script[start:end] for start, end in
              zip(boundaries, boundaries[1:] + [len(script)])]
    assert b"".join(chunks) == script

    selected = [(f"final_dummy_{i:03d}", sig)
                for i, sig in enumerate(builder.dummy_sigs[1])]
    selected.append(("final_nonce", final_nonce))
    assert len({sig for _, sig in selected}) == 151
    assert all(sig[-1] == 0x03 for _, sig in selected[:-1])
    assert final_nonce[-1] == 0x01
    cases = []
    for name, sig in selected:
        pattern = bt.push_data(sig)
        assert len(sig) in (9, 55)
        assert pattern == bytes((len(sig),)) + sig
        # The first byte is a direct-push length. Thus any boundary match
        # consumes one entire parsed opcode, even after other whole opcodes
        # have been removed. This is the premise for arbitrary subset order.
        assert all(not chunk.startswith(pattern) or chunk == pattern
                   for chunk in chunks), name
        matches = [pc for pc in boundaries
                   if script[pc:pc + len(pattern)] == pattern]
        assert len(matches) == 1, (name, matches)
        offset = matches[0]
        expected = script[:offset] + script[offset + len(pattern):]
        actual = bt.find_and_delete(script, sig)
        assert actual == expected, name
        cases.append({"name": name, "signature_hex": sig.hex(),
                      "push_offset": offset, "push_size": len(pattern),
                      "script_code_sha256": hashlib.sha256(actual).hexdigest()})

    rng = random.Random("QSB exact final scriptCode selection orders")
    choices = [list(range(9)), list(range(141, 150)),
               [0, 1, 17, 23, 41, 77, 96, 111, 149]]
    choices += [sorted(rng.sample(range(150), 9)) for _ in range(32)]
    multi_cases = []
    for ids in choices:
        signatures = [selected[i][1] for i in ids] + [final_nonce]
        patterns = {bt.push_data(sig) for sig in signatures}
        assert len(patterns) == 10
        expected = b"".join(chunk for chunk in chunks if chunk not in patterns)
        order_hashes = []
        for ordered in (signatures, list(reversed(signatures)),
                        rng.sample(signatures, len(signatures))):
            actual = script
            for sig in ordered:
                actual = bt.find_and_delete(actual, sig)
            assert actual == expected, ids
            order_hashes.append(hashlib.sha256(actual).hexdigest())
        assert len(set(order_hashes)) == 1
        multi_cases.append({"dummy_ids": ids,
                            "script_code_sha256": order_hashes[0]})

    report = {
        "scope": "one disposable exact lock; exhaustive boundary-pattern inventory and sampled ten-signature orders",
        "source_revision": subprocess.check_output(
            ["git", "-C", str(args.app_root), "rev-parse", "HEAD"],
            text=True).strip(),
        "pinned_source_revision": pinned["revision"],
        "builder_sha256": source_hash,
        "secp256k1_sha256": ec_hash,
        "script_sha256": script_hash,
        "script_bytes": len(script),
        "opcode_boundaries": len(boundaries),
        "checked_signature_pushes": len(cases),
        "dummy_sighash_byte": "03",
        "nonce_sighash_byte": "01",
        "all_selected_patterns_direct_pushes": True,
        "all_boundary_prefix_matches_complete_opcodes": True,
        "sampled_ten_signature_sets": len(multi_cases),
        "cases": cases,
        "multi_cases": multi_cases,
    }
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"script_sha256": script_hash,
                      "checked_signature_pushes": len(cases),
                      "sampled_ten_signature_sets": len(multi_cases)}, indent=2))


if __name__ == "__main__":
    main()
