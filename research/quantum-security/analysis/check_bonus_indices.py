"""Probe the final bonus index at its stack-role boundaries.

For indices 0..151 the generated HORS commitments are unmodified. A separate
index-152 case uses a hand-crafted DER-shaped commitment and therefore does
NOT satisfy the normal HASH160(random secret) generation rule. Three puzzle
CHECKSIGVERIFY sites are replaced with OP_2DROP throughout; pinning, HORS
comparisons and both CHECKMULTISIGs remain real. These cases are structural
tests, not valid production-vault forgeries.
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

    def witness(lock, c7, bonus_index, index_bytes=None):
        w = bytearray()
        for ri in (1, 0):
            selected = [builder.dummy_sigs[ri][j] for j in subsets[ri]]
            if ri == 1 and bonus_index >= 10:
                selected[8] = (builder.dummy_sigs[ri][bonus_index - 2]
                               if bonus_index <= 151 else c7)
            sc = bt.find_and_delete(lock, nonces[ri])
            for sig in selected:
                sc = bt.find_and_delete(sc, sig)
            kn = recover(nonces[ri], tx.sighash(1, sc, 1))
            pubs = []
            for j, sig in enumerate(selected):
                if ri == 1 and bonus_index == 152 and c7 == natural_c7 and j == 8:
                    pubs.append(ec.compress_pubkey(ec.G))
                else:
                    pubs.append(recover(sig, tx.sighash(1, sc, sig[-1])))
            w += bt.push_data(ec.compress_pubkey(ec.G)) + bt.push_data(kn)
            for pub in reversed(pubs):
                w += bt.push_data(pub)
            for j in range((7 if ri else 8) - 1, -1, -1):
                w += bt.push_data(builder.hors_secrets[ri][subsets[ri][j]])
            iv = list(indices[ri])
            if ri == 1:
                iv[8] = bonus_index
            for j, value in enumerate(reversed(iv)):
                if ri == 1 and j == 0 and index_bytes is not None:
                    # The last bonus index is the first value pushed by this
                    # reverse-order loop. Preserve its chosen byte encoding.
                    w += bt.push_data(index_bytes)
                else:
                    w += bt.push_number(value)
        pin_key = recover(pin, tx.sighash(1, bt.find_and_delete(lock, pin), 1))
        w += bt.push_data(ec.compress_pubkey(ec.G)) + bt.push_data(pin_key)
        return bytes(w)

    results = []
    for name, c7, bonus_index, index_bytes, expected in (
        ("revisit_top_0", natural_c7, 0, None, False),
        ("revisit_seventh_7", natural_c7, 7, None, False),
        ("nonce_slot_8", natural_c7, 8, None, False),
        ("nulldummy_slot_9", natural_c7, 9, None, False),
        ("first_unused_dummy_10", natural_c7, 10, None, True),
        ("first_unused_dummy_10_nonminimal", natural_c7, 10, b"\x0a\x00", True),
        ("next_unused_dummy_11", natural_c7, 11, None, True),
        ("last_unused_dummy_151", natural_c7, 151, None, True),
        ("natural_commitment_152", natural_c7, 152, None, False),
        ("crafted_der_commitment_152", crafted_c7, 152, None, True),
        ("crafted_der_commitment_152_nonminimal", crafted_c7, 152,
         b"\x98\x00\x00", True),
        ("crafted_der_commitment_152_five_bytes", crafted_c7, 152,
         b"\x98\x00\x00\x00\x00", False),
        ("crafted_der_commitment_negative_152", crafted_c7, 152,
         b"\x98\x80", False),
    ):
        exact, lock = make_lock(c7)
        tx.inputs[1].script_sig = witness(lock, c7, bonus_index, index_bytes)
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
        results.append({"name": name, "bonus_index": bonus_index,
                        "index_encoding_hex": index_bytes.hex() if index_bytes is not None else None,
                        "accepted": accepted, "expected": expected,
                        "exact_lock_sha256": hashlib.sha256(exact).hexdigest(),
                        "test_lock_sha256": hashlib.sha256(lock).hexdigest(),
                        "transaction_sha256": hashlib.sha256(tx.serialize()).hexdigest()})

    report = {
        "scope": "Three puzzle checks relaxed in every case; index 152 positive case also alters a commitment; not a production-vault forgery",
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
