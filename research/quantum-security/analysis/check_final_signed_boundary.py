"""Probe a final-round signed index with the pinned Core adapter.

The three hash-to-signature puzzle checks are replaced with OP_2DROP. Pinning,
all HORS comparisons, and both CHECKMULTISIGs remain real. The witness and
lock use disposable public test material. These are structural boundary
checks, not a production-vault spend or a Core-to-Lean refinement proof.
"""
import argparse
import hashlib
import json
import random
import subprocess
import sys
from pathlib import Path

from check_round_results import opcodes


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--app-root", type=Path, required=True)
    parser.add_argument("--native-root", type=Path, required=True)
    parser.add_argument("--image", required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--position", type=int, choices=(0, 1), default=0)
    args = parser.parse_args()
    sys.path.insert(0, str(args.app_root / "worker/cpu"))
    import bitcoin_tx as bt
    import secp256k1 as ec
    from qsb_pipeline import parse_der

    rng = random.Random("QSB security analysis: PUBLIC DISPOSABLE TEST MATERIAL")
    builder = bt.QSBScriptBuilder(150, 8, 1, 7, 2, hash_mode="sha256")
    old_random = bt.os.urandom
    try:
        bt.os.urandom = rng.randbytes
        builder.generate_keys()
    finally:
        bt.os.urandom = old_random

    def nonce_sig(label):
        k = int.from_bytes(hashlib.sha256(label + b"_nonce").digest(), "big") % ec.N
        r = ec.point_mul(k, ec.G)[0] % ec.N
        s = max(1, int.from_bytes(hashlib.sha256(label + b"_s").digest()[:16],
                                  "big") % (ec.N // 2))
        return ec.encode_der_sig(r, s, sighash=1)

    pin = nonce_sig(b"qsb_pin")
    nonces = [nonce_sig(b"qsb_r0"), nonce_sig(b"qsb_r1")]
    subsets = {0: list(range(9)), 1: list(range(9))}
    indices = builder.compute_witness_indices(subsets)
    assert indices[1][args.position] == 2 + args.position
    tx = bt.Transaction(version=1, locktime=1234567)
    tx.add_input(bt.TxIn(b"\x11" * 32, 0, b"", 0xfffffffe))
    tx.add_input(bt.TxIn(b"\x22" * 32, 0, b"", 0x80000000))
    tx.add_output(bt.TxOut(90000, b"\x00\x14" + b"\x33" * 20))

    def recover(sig, z):
        r, s = parse_der(sig)
        for x in (r, r + ec.N):
            if x >= ec.P:
                continue
            for parity in (0, 1):
                point = ec.ecdsa_recover(x, s, z, parity)
                if point and ec.ecdsa_verify(point, z, r, s):
                    return ec.compress_pubkey(point)
        raise AssertionError("test signature has no recovered key")

    exact = builder.build_full_script(pin, *nonces)
    lock = bytearray(exact)
    sites = [i for i, op in opcodes(exact) if op == bt.OP_CHECKSIGVERIFY]
    assert len(sites) == 4
    for i in sites[1:]:
        lock[i] = 0x6d  # OP_2DROP, preserving pinning and both CHECKMULTISIGs.
    lock = bytes(lock)

    def witness(index, raw_encoding):
        script_sig = bytearray()
        for round_index in (1, 0):
            selected = [builder.dummy_sigs[round_index][j]
                        for j in subsets[round_index]]
            script_code = bt.find_and_delete(lock, nonces[round_index])
            for sig in selected:
                script_code = bt.find_and_delete(script_code, sig)
            nonce_key = recover(nonces[round_index], tx.sighash(1, script_code, 1))
            pubkeys = [recover(sig, tx.sighash(1, script_code, sig[-1]))
                       for sig in selected]
            script_sig += bt.push_data(ec.compress_pubkey(ec.G))
            script_sig += bt.push_data(nonce_key)
            for pubkey in reversed(pubkeys):
                script_sig += bt.push_data(pubkey)
            for j in range((7 if round_index else 8) - 1, -1, -1):
                script_sig += bt.push_data(
                    builder.hors_secrets[round_index][subsets[round_index][j]])
            values = list(indices[round_index])
            if round_index == 1:
                values[args.position] = index
            for j, value in enumerate(reversed(values)):
                if (round_index == 1 and
                        j == len(values) - 1 - args.position and
                        raw_encoding is not None):
                    script_sig += bt.push_data(raw_encoding)
                else:
                    script_sig += bt.push_number(value)
        pin_key = recover(pin, tx.sighash(1, bt.find_and_delete(lock, pin), 1))
        script_sig += bt.push_data(ec.compress_pubkey(ec.G))
        script_sig += bt.push_data(pin_key)
        return bytes(script_sig)

    if args.position == 0:
        cases = [
            ("canonical_2", 2, None, True),
            ("dummy_0", 0, None, False),
            ("dummy_1", 1, None, False),
            ("cap_152", 152, None, False),
            ("cap_152_nonminimal", 152, b"\x98\x00\x00", False),
        ]
    else:
        cases = [
            ("canonical_3", 3, None, True),
            ("nonminimal_3", 3, b"\x03\x00", True),
            ("dummy_0", 0, None, False),
            ("dummy_1", 1, None, False),
            ("dummy_2", 2, None, False),
            ("negative_1", -1, b"\x81", False),
            ("cap_152", 152, None, False),
            ("cap_152_nonminimal", 152, b"\x98\x00\x00", False),
        ]
    results = []
    for name, index, raw_encoding, expected in cases:
        tx.inputs[1].script_sig = witness(index, raw_encoding)
        payload = f"{tx.serialize().hex()}\n2\n1000\n51\n100000\n{lock.hex()}\n"
        process = subprocess.run([
            "docker", "run", "--rm", "--network", "none", "--read-only",
            "--cap-drop=ALL", "--security-opt=no-new-privileges",
            "--platform=linux/arm64", "-i",
            "-v", f"{args.native_root.resolve()}:/native:ro", args.image,
            "/native/qsb-consensus"], input=payload, text=True,
            capture_output=True, timeout=30)
        if process.returncode not in (0, 1):
            raise RuntimeError(f"Core adapter unavailable: {process.stderr}")
        accepted = (process.returncode == 0 and
                    process.stdout.strip() == "core-27.2-api2-all-inputs-valid")
        assert accepted == expected, (name, process)
        results.append({
            "name": name,
            ("first_final_signed_index" if args.position == 0 else
             "second_final_signed_index"): index,
            "raw_encoding_hex": raw_encoding.hex() if raw_encoding else None,
            "accepted": accepted, "expected": expected,
            "transaction_sha256": hashlib.sha256(tx.serialize()).hexdigest(),
        })

    report = {
        "scope": "Three puzzle checks relaxed; pinning, HORS comparisons, and both CHECKMULTISIGs real; not a production-vault spend",
        "core_flags": "bitcoinconsensus_SCRIPT_FLAGS_VERIFY_ALL",
        "source_revision": subprocess.check_output(
            ["git", "-C", str(args.app_root), "rev-parse", "HEAD"],
            text=True).strip(),
        "exact_lock_sha256": hashlib.sha256(exact).hexdigest(),
        "test_lock_sha256": hashlib.sha256(lock).hexdigest(),
        "native_files_sha256": {f.name: hashlib.sha256(f.read_bytes()).hexdigest()
                                for f in args.native_root.iterdir() if f.is_file()},
        "image": args.image,
        "cases": results,
    }
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"cases": [{"name": x["name"], "accepted": x["accepted"]}
                                  for x in results]}, indent=2))


if __name__ == "__main__":
    main()
