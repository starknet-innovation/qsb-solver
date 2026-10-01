"""Synthetic Core experiment: is round one's CHECKMULTISIG result enforced?

Three hash-to-DER puzzle CHECKSIGVERIFY sites are replaced with OP_2DROP.
This is a structural experiment on a MODIFIED lock, not a spend of the real lock.
Pinning CHECKSIGVERIFY, both CHECKMULTISIGs, and all HORS checks remain real.
All secrets/outpoints are disposable, generated here, and never broadcast.
"""
import argparse
import hashlib
import json
import random
import subprocess
import sys
from pathlib import Path

def opcodes(script):
    i = 0
    while i < len(script):
        start, op = i, script[i]
        i += 1
        if 1 <= op <= 75:
            i += op
        elif op in (0x4c, 0x4d, 0x4e):
            width = {0x4c: 1, 0x4d: 2, 0x4e: 4}[op]
            count = int.from_bytes(script[i:i+width], "little")
            i += width + count
        yield start, op
    assert i == len(script)

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--app-root", type=Path, required=True)
    parser.add_argument("--native-root", type=Path, required=True)
    parser.add_argument("--image", required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    sys.path.insert(0, str(args.app_root / "worker/cpu"))
    import bitcoin_tx as bt
    import secp256k1 as ec
    from qsb_pipeline import parse_der
    root = Path(__file__).resolve().parents[1]
    pinned = json.loads((root / "evidence/source-inventory.json").read_text())["app"]
    for name in ("worker/cpu/bitcoin_tx.py", "worker/cpu/secp256k1.py",
                 "worker/cpu/qsb_pipeline.py"):
        assert hashlib.sha256((args.app_root / name).read_bytes()).hexdigest() == pinned["files"][name]
    prior = json.loads((root / "evidence/round-results.json").read_text())
    assert args.image == prior["image"]
    for name, expected in prior["native_files_sha256"].items():
        assert hashlib.sha256((args.native_root / name).read_bytes()).hexdigest() == expected
    rng = random.Random("QSB security analysis: PUBLIC DISPOSABLE TEST MATERIAL")
    builder = bt.QSBScriptBuilder(150, 8, 1, 7, 2, hash_mode="sha256")
    original_random = bt.os.urandom
    try:
        bt.os.urandom = rng.randbytes
        builder.generate_keys()
    finally:
        bt.os.urandom = original_random
    # Use precisely the production fixed nonce signatures.
    def nonce_sig(label):
        k = int.from_bytes(hashlib.sha256(label + b"_nonce").digest(), "big") % ec.N
        r = ec.point_mul(k, ec.G)[0] % ec.N
        s = max(1, int.from_bytes(hashlib.sha256(label + b"_s").digest()[:16], "big") % (ec.N // 2))
        return ec.encode_der_sig(r, s, sighash=1)
    pin = nonce_sig(b"qsb_pin")
    nonces = [nonce_sig(b"qsb_r0"), nonce_sig(b"qsb_r1")]
    exact_lock = builder.build_full_script(pin, *nonces)
    sig_sites = [i for i, op in opcodes(exact_lock) if op == 0xad]
    cms_sites = [i for i, op in opcodes(exact_lock) if op == 0xae]
    assert len(sig_sites) == 4 and len(cms_sites) == 2
    lock = bytearray(exact_lock)
    for i in sig_sites[1:]:
        lock[i] = 0x6d
    lock = bytes(lock)
    subsets = {0: [3, 17, 42, 66, 88, 101, 119, 140, 9],
               1: [5, 20, 55, 70, 90, 110, 130, 15, 45]}
    indices = builder.compute_witness_indices(subsets)
    tx = bt.Transaction(version=1, locktime=1234567)
    tx.add_input(bt.TxIn(b"\x11" * 32, 0, b"", 0xfffffffe))
    tx.add_input(bt.TxIn(b"\x22" * 32, 0, b"", 0x80000000))
    tx.add_output(bt.TxOut(90000, b"\x00\x14" + b"\x33" * 20))
    def recover(sig, z):
        r, s = parse_der(sig)
        for x in (r, r + ec.N):
            if x >= ec.P:
                continue
            for flag in (0, 1):
                point = ec.ecdsa_recover(x, s, z, flag)
                if point and ec.ecdsa_verify(point, z, r, s):
                    return ec.compress_pubkey(point)
        raise AssertionError("test signature has no recovered key")
    def first_round_nonce_key():
        sc = bt.find_and_delete(lock, nonces[0])
        for j in subsets[0]:
            sc = bt.find_and_delete(sc, builder.dummy_sigs[0][j])
        return recover(nonces[0], tx.sighash(1, sc, 1))
    disclosed_nonce = first_round_nonce_key()
    def witness(bad_round=None, bad_preimage=None, reuse_round1_nonce=False,
                wrong_final_scriptcode_key=None):
        w = bytearray()
        checks = []
        wrong_control = None
        for ri in (1, 0):
            sc = bt.find_and_delete(lock, nonces[ri])
            dummies = [builder.dummy_sigs[ri][j] for j in subsets[ri]]
            for ds in dummies:
                sc = bt.find_and_delete(sc, ds)
            z = tx.sighash(1, sc, 1)
            kn = disclosed_nonce if ri == 0 and reuse_round1_nonce else recover(nonces[ri], z)
            single_z = tx.sighash(1, sc, 3)
            pubs = [recover(ds, single_z) for ds in dummies]
            if ri == 1 and wrong_final_scriptcode_key is not None:
                # Retain exactly one reached final signature push while
                # removing the other nine. The correct shared scriptCode
                # removes all ten before any key is checked.
                wrong_sc = lock
                if wrong_final_scriptcode_key != 9:
                    wrong_sc = bt.find_and_delete(wrong_sc, nonces[ri])
                for j, ds in enumerate(dummies):
                    if j != wrong_final_scriptcode_key:
                        wrong_sc = bt.find_and_delete(wrong_sc, ds)
                assert wrong_sc != sc
                if wrong_final_scriptcode_key == 9:
                    wrong_z = tx.sighash(1, wrong_sc, 1)
                    kn = recover(nonces[ri], wrong_z)
                    wrong_key_verifies = ec.ecdsa_verify(ec.decompress_pubkey(kn), z,
                                                         *parse_der(nonces[ri]))
                else:
                    j = wrong_final_scriptcode_key
                    wrong_z = tx.sighash(1, wrong_sc, 3)
                    pubs[j] = recover(dummies[j], wrong_z)
                    wrong_key_verifies = ec.ecdsa_verify(
                        ec.decompress_pubkey(pubs[j]), single_z,
                        *parse_der(dummies[j]))
                assert wrong_z != (z if wrong_final_scriptcode_key == 9 else single_z)
                assert not wrong_key_verifies
                wrong_control = {
                    "retained_final_signature_slot": wrong_final_scriptcode_key,
                    "shared_scriptcode_sha256": hashlib.sha256(sc).hexdigest(),
                    "retained_scriptcode_sha256": hashlib.sha256(wrong_sc).hexdigest(),
                    "correct_sighash_scalar_hex": f"{(z if wrong_final_scriptcode_key == 9 else single_z):064x}",
                    "retained_sighash_scalar_hex": f"{wrong_z:064x}",
                    "wrong_key_verifies_correct_message": wrong_key_verifies,
                }
            if ri == bad_round:
                # Well-formed EC key; the nonempty DER signature stays unchanged.
                pubs[0] = ec.compress_pubkey(ec.G)
            r, s = parse_der(dummies[0])
            checks.append({"round": ri + 1, "first_dummy_verifies":
                           ec.ecdsa_verify(ec.decompress_pubkey(pubs[0]), single_z, r, s),
                           "nonce_verifies": ec.ecdsa_verify(ec.decompress_pubkey(kn), z, *parse_der(nonces[ri]))})
            w += bt.push_data(ec.compress_pubkey(ec.G)) + bt.push_data(kn)
            for pub in reversed(pubs):
                w += bt.push_data(pub)
            ts = 8 if ri == 0 else 7
            for j in range(ts - 1, -1, -1):
                secret = builder.hors_secrets[ri][subsets[ri][j]]
                if bad_preimage == ri and j == 0:
                    secret = b"\x00" * 20
                w += bt.push_data(secret)
            for iv in reversed(indices[ri]):
                w += bt.push_number(iv)
        kn = recover(pin, tx.sighash(1, bt.find_and_delete(lock, pin), 1))
        w += bt.push_data(ec.compress_pubkey(ec.G)) + bt.push_data(kn)
        return bytes(w), checks, wrong_control
    cases = []
    def run_case(name, expected, bad_round=None, bad_preimage=None,
                 reuse_round1_nonce=False, wrong_final_scriptcode_key=None):
        tx.inputs[1].script_sig, checks, wrong_control = witness(
            bad_round, bad_preimage, reuse_round1_nonce, wrong_final_scriptcode_key)
        # Helper prevout is OP_TRUE. No signing key or actual UTXO is used.
        payload = f"{tx.serialize().hex()}\n2\n1000\n51\n100000\n{lock.hex()}\n"
        result = subprocess.run([
            "docker", "run", "--rm", "--network", "none", "--read-only",
            "--cap-drop=ALL", "--security-opt=no-new-privileges", "--platform=linux/arm64",
            "-i", "-v", f"{args.native_root.resolve()}:/native:ro",
            args.image, "/native/qsb-consensus"], input=payload, text=True,
            capture_output=True, timeout=30)
        accepted = result.returncode == 0 and result.stdout.strip() == "core-27.2-api2-all-inputs-valid"
        if result.returncode not in (0, 1):
            raise RuntimeError(f"native verifier unavailable: {result.returncode}: {result.stderr}")
        case = {"name": name, "accepted": accepted, "expected": expected,
                "exit_code": result.returncode, "stdout": result.stdout.strip(),
                "independent_dummy_checks": checks,
                "synthetic_transaction_sha256": hashlib.sha256(tx.serialize()).hexdigest()}
        if wrong_control is not None:
            case["wrong_final_control"] = wrong_control
        cases.append(case)
        assert accepted == expected, cases[-1]
        return checks
    run_case("honest_relaxed", True)
    run_case("invalid_round1_multisig", True, bad_round=0)
    run_case("invalid_round2_multisig", False, bad_round=1)
    run_case("invalid_round1_preimage", False, bad_preimage=0)
    run_case("invalid_round2_preimage", False, bad_preimage=1)
    tx.outputs[0].script_pubkey = b"\x00\x14" + b"\x77" * 20
    checks = run_case("changed_destination_fresh_nonce", True)
    assert all(c["nonce_verifies"] for c in checks)
    checks = run_case("changed_destination_reused_round1_nonce", True, reuse_round1_nonce=True)
    assert not next(c for c in checks if c["round"] == 1)["nonce_verifies"]
    assert next(c for c in checks if c["round"] == 2)["nonce_verifies"]
    # With two outputs the signed input's SINGLE hash is in range. All ten
    # final signatures now depend on the shared FindAndDelete scriptCode.
    tx.add_output(bt.TxOut(1000, b"\x51"))
    assert tx.sighash(1, lock, 3) != 1 << 248
    run_case("two_output_shared_scriptcode", True)
    for j in range(10):
        run_case(f"two_output_retained_final_push_{j}", False,
                 wrong_final_scriptcode_key=j)
    report = {"scope": "MODIFIED lock; three puzzle CHECKSIGVERIFYs replaced with OP_2DROP; not a real-lock forgery",
              "source_revision": pinned["revision"],
              "exact_lock_sha256": hashlib.sha256(exact_lock).hexdigest(),
              "modified_lock_sha256": hashlib.sha256(lock).hexdigest(),
              "script_bytes": len(exact_lock), "runtime_ops": builder.count_opcodes_runtime(exact_lock)[0],
              "checksigverify_offsets": sig_sites, "checkmultisig_offsets": cms_sites,
              "native_files_sha256": {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in args.native_root.iterdir() if p.is_file()},
              "image": args.image, "cases": cases}
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"cases": [{"name": c["name"], "accepted": c["accepted"]} for c in cases], "scope": report["scope"]}, indent=2))

if __name__ == "__main__":
    main()
