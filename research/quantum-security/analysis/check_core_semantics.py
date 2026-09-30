"""Unmodified Core checks of isolated legacy signature semantics.

All transactions and keys are synthetic. These short scripts are NOT the QSB
locking script; the tests delimit assumptions a QSB proof must respect.
"""
import argparse
import hashlib
import json
import subprocess
import sys
from pathlib import Path

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
    tx = bt.Transaction(version=1, locktime=1234567)
    tx.add_input(bt.TxIn(b"\x44" * 32, 0, b"", 0xfffffffe))
    tx.add_input(bt.TxIn(b"\x55" * 32, 0, b"", 0x80000000))
    destination = b"\x00\x14" + b"\x66" * 20
    tx.add_output(bt.TxOut(90000, destination))
    r = bt._valid_small_r_values()[0]
    s = 17
    cases = []
    def check(name, lock, pub, expected):
        tx.inputs[1].script_sig = bt.push_data(pub)
        payload = f"{tx.serialize().hex()}\n2\n1000\n51\n100000\n{lock.hex()}\n"
        result = subprocess.run([
            "docker", "run", "--rm", "--network", "none", "--read-only", "--cap-drop=ALL",
            "--security-opt=no-new-privileges", "--platform=linux/arm64", "-i",
            "-v", f"{a.native_root.resolve()}:/native:ro", a.image, "/native/qsb-consensus"],
            input=payload, text=True, capture_output=True, timeout=30)
        if result.returncode not in (0, 1):
            raise RuntimeError(result.stderr)
        accepted = result.returncode == 0 and result.stdout.strip() == "core-27.2-api2-all-inputs-valid"
        cases.append({"name": name, "accepted": accepted, "expected": expected,
                      "script_hex": lock.hex(), "pubkey_encoding_hex": pub.hex(),
                      "raw_tx_sha256": hashlib.sha256(tx.serialize()).hexdigest()})
        assert accepted == expected, cases[-1]
    def lock_and_point(hashtype):
        sig = ec.encode_der_sig(r, s, sighash=hashtype)
        lock = bt.push_data(sig) + bytes([bt.OP_SWAP, bt.OP_CHECKSIG])
        z = tx.sighash(1, bt.find_and_delete(lock, sig), hashtype)
        point = ec.ecdsa_recover(r, s, z, 0)
        assert point and ec.ecdsa_verify(point, z, r, s)
        return lock, point, z
    lock, point, _ = lock_and_point(1)
    x, y = point
    compressed = ec.compress_pubkey(point)
    xy = x.to_bytes(32, "big") + y.to_bytes(32, "big")
    check("all_compressed", lock, compressed, True)
    check("all_uncompressed", lock, b"\x04" + xy, True)
    check("all_hybrid", lock, bytes([6 + y % 2]) + xy, True)
    check("all_hybrid_wrong_parity", lock, bytes([7 - y % 2]) + xy, False)
    tx.outputs[0].script_pubkey = b"\x00\x14" + b"\x77" * 20
    check("all_changed_destination_same_key", lock, compressed, False)
    lock, new_point, _ = lock_and_point(1)
    check("all_changed_destination_recovered_key", lock, ec.compress_pubkey(new_point), True)
    tx.outputs[0].script_pubkey = destination
    lock, point, z = lock_and_point(3)
    assert z == 1 << 248
    check("single_bug_original", lock, ec.compress_pubkey(point), True)
    tx.outputs[0].script_pubkey = b"\x00\x14" + b"\x88" * 20
    tx.outputs[0].value = 80000
    check("single_bug_changed_destination_and_amount", lock, ec.compress_pubkey(point), True)
    tx.add_output(bt.TxOut(1000, b"\x51"))
    in_range_lock, in_range_point, in_range_z = lock_and_point(3)
    assert in_range_z != 1 << 248
    check("single_in_range_old_recovery_key", in_range_lock,
          ec.compress_pubkey(point), False)
    check("single_in_range_new_recovery_key", in_range_lock,
          ec.compress_pubkey(in_range_point), True)
    report = {"scope": "isolated legacy scripts; NOT full QSB acceptance or a forgery",
              "core_flags": "bitcoinconsensus_SCRIPT_FLAGS_VERIFY_ALL (consensus, not policy)",
              "image": a.image, "cases": cases}
    a.output.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps([{k: c[k] for k in ("name", "accepted")} for c in cases], indent=2))

if __name__ == "__main__":
    main()
