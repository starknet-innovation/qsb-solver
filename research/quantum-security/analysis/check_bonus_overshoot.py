"""Probe final-round bonus out-of-pool selection on a SYNTHETIC altered lock.

One round-2 HORS commitment is replaced with a hand-crafted 20-byte DER
signature, so this lock does NOT satisfy the normal HASH160(random secret)
generation rule. Three hash-to-DER puzzle CHECKSIGVERIFY sites are relaxed to
OP_2DROP; pinning, HORS comparisons, and both CHECKMULTISIGs remain real.
This tests a source-extraction edge case, not a valid production-vault forgery.
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
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--app-root", type=Path, required=True)
    p.add_argument("--native-root", type=Path, required=True)
    p.add_argument("--image", required=True)
    p.add_argument("--output", type=Path, required=True)
    a = p.parse_args()
    sys.path.insert(0, str(a.app_root / "worker/cpu"))
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
    natural_c7 = builder.hors_commitments[1][7]
    crafted_c7 = ec.encode_der_sig(1, (1 << 88) + 17, sighash=3)
    assert len(crafted_c7) == len(natural_c7) == 20
    assert natural_c7 == ec.hash160(builder.hors_secrets[1][7])
    assert crafted_c7 != ec.hash160(builder.hors_secrets[1][7])

    def nonce_sig(label):
        k = int.from_bytes(hashlib.sha256(label + b"_nonce").digest(), "big") % ec.N
        r = ec.point_mul(k, ec.G)[0] % ec.N
        s = max(1, int.from_bytes(hashlib.sha256(label + b"_s").digest()[:16], "big") % (ec.N // 2))
        return ec.encode_der_sig(r, s, sighash=1)

    pin = nonce_sig(b"qsb_pin")
    nonces = [nonce_sig(b"qsb_r0"), nonce_sig(b"qsb_r1")]
    subsets = {0: list(range(9)), 1: list(range(9))}
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
            for parity in (0, 1):
                point = ec.ecdsa_recover(x, s, z, parity)
                if point and ec.ecdsa_verify(point, z, r, s):
                    return ec.compress_pubkey(point)
        raise AssertionError("test signature has no recovered key")

    def make_lock(c7):
        builder.hors_commitments[1][7] = c7
        exact = builder.build_full_script(pin, *nonces)
        lock = bytearray(exact)
        sites = [i for i, op in opcodes(exact) if op == bt.OP_CHECKSIGVERIFY]
        assert len(sites) == 4
        for i in sites[1:]:
            lock[i] = 0x6d  # OP_2DROP, while pinning remains checked.
        return exact, bytes(lock)

    def witness(lock, c7, overshoot_slot):
        w = bytearray()
        for ri in (1, 0):
            selected = [builder.dummy_sigs[ri][j] for j in subsets[ri]]
            if ri == 1 and overshoot_slot is not None:
                selected[overshoot_slot] = c7
            sc = bt.find_and_delete(lock, nonces[ri])
            for sig in selected:
                sc = bt.find_and_delete(sc, sig)
            kn = recover(nonces[ri], tx.sighash(1, sc, 1))
            pubs = []
            for j, sig in enumerate(selected):
                if ri == 1 and overshoot_slot == j and c7 == natural_c7:
                    pubs.append(ec.compress_pubkey(ec.G))
                else:
                    pubs.append(recover(sig, tx.sighash(1, sc, sig[-1])))
            w += bt.push_data(ec.compress_pubkey(ec.G)) + bt.push_data(kn)
            for pub in reversed(pubs):
                w += bt.push_data(pub)
            for j in range((7 if ri else 8) - 1, -1, -1):
                w += bt.push_data(builder.hors_secrets[ri][subsets[ri][j]])
            iv = list(indices[ri])
            if ri == 1 and overshoot_slot is not None:
                iv[overshoot_slot] = 152
                if overshoot_slot == 7:
                    # After the first bonus takes C7, depth 11 (rather than
                    # canonical depth 10) selects the remaining dummy j8.
                    iv[8] = 11
            for value in reversed(iv):
                w += bt.push_number(value)
        pin_key = recover(pin, tx.sighash(1, bt.find_and_delete(lock, pin), 1))
        w += bt.push_data(ec.compress_pubkey(ec.G)) + bt.push_data(pin_key)
        return bytes(w)

    results = []
    for name, c7, overshoot_slot, expected in (
        ("natural_c7_canonical", natural_c7, None, True),
        ("natural_c7_overshoot", natural_c7, 8, False),
        ("crafted_der20_canonical", crafted_c7, None, True),
        ("crafted_der20_overshoot", crafted_c7, 8, True),
        ("natural_c7_first_bonus_overshoot", natural_c7, 7, False),
        ("crafted_der20_first_bonus_overshoot", crafted_c7, 7, True),
    ):
        exact, lock = make_lock(c7)
        tx.inputs[1].script_sig = witness(lock, c7, overshoot_slot)
        payload = f"{tx.serialize().hex()}\n2\n1000\n51\n100000\n{lock.hex()}\n"
        result = subprocess.run([
            "docker", "run", "--rm", "--network", "none", "--read-only",
            "--cap-drop=ALL", "--security-opt=no-new-privileges",
            "--platform=linux/arm64", "-i",
            "-v", f"{a.native_root.resolve()}:/native:ro", a.image,
            "/native/qsb-consensus"], input=payload, text=True,
            capture_output=True, timeout=30)
        if result.returncode not in (0, 1):
            raise RuntimeError(f"Core unavailable: {result.stderr}")
        accepted = result.returncode == 0 and result.stdout.strip() == "core-27.2-api2-all-inputs-valid"
        assert accepted == expected, (name, result)
        results.append({"name": name, "accepted": accepted, "expected": expected,
                        "overshoot_slot": overshoot_slot,
                        "final_bonus_indices": [152, 11] if overshoot_slot == 7 else
                            [10, 152] if overshoot_slot == 8 else [10, 10],
                        "exact_lock_sha256": hashlib.sha256(exact).hexdigest(),
                        "test_lock_sha256": hashlib.sha256(lock).hexdigest(),
                        "transaction_sha256": hashlib.sha256(tx.serialize()).hexdigest()})

    report = {
        "scope": "SYNTHETIC altered commitment and relaxed puzzle checks; not a production-vault forgery",
        "core_flags": "bitcoinconsensus_SCRIPT_FLAGS_VERIFY_ALL",
        "source_revision": subprocess.check_output(
            ["git", "-C", str(a.app_root), "rev-parse", "HEAD"], text=True).strip(),
        "natural_commitment_hex": natural_c7.hex(),
        "crafted_der20_commitment_hex": crafted_c7.hex(),
        "native_files_sha256": {f.name: hashlib.sha256(f.read_bytes()).hexdigest()
                                for f in a.native_root.iterdir() if f.is_file()},
        "image": a.image,
        "cases": results,
    }
    a.output.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"scope": report["scope"],
                      "cases": [{k: row[k] for k in ("name", "accepted")}
                                for row in results]}, indent=2))


if __name__ == "__main__":
    main()
