"""Check every trailing legacy ECDSA sighash byte in isolated Core scripts.

The signature's DER integers are fixed and valid. For each byte, recover a
verification key for the corresponding transaction sighash and ask the pinned
Core consensus adapter to verify it. This is not a QSB full-lock experiment.
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
    tx.add_output(bt.TxOut(90000, b"\x00\x14" + b"\x66" * 20))
    r, s = bt._valid_small_r_values()[0], 17
    native_hashes = {f.name: hashlib.sha256(f.read_bytes()).hexdigest()
                     for f in a.native_root.iterdir() if f.is_file()}
    accepted = []
    for hashtype in range(256):
        sig = ec.encode_der_sig(r, s, sighash=hashtype)
        lock = bt.push_data(sig) + bytes([bt.OP_SWAP, bt.OP_CHECKSIG])
        z = tx.sighash(1, bt.find_and_delete(lock, sig), hashtype)
        point = ec.ecdsa_recover(r, s, z, 0)
        assert point and ec.ecdsa_verify(point, z, r, s)
        tx.inputs[1].script_sig = bt.push_data(ec.compress_pubkey(point))
        payload = f"{tx.serialize().hex()}\n2\n1000\n51\n100000\n{lock.hex()}\n"
        result = subprocess.run([
            "docker", "run", "--rm", "--network", "none", "--read-only",
            "--cap-drop=ALL", "--security-opt=no-new-privileges",
            "--platform=linux/arm64", "-i",
            "-v", f"{a.native_root.resolve()}:/native:ro", a.image,
            "/native/qsb-consensus"], input=payload, text=True,
            capture_output=True, timeout=30)
        if result.returncode not in (0, 1):
            raise RuntimeError(f"Core unavailable at hashtype {hashtype}: {result.stderr}")
        success = result.returncode == 0 and result.stdout.strip() == "core-27.2-api2-all-inputs-valid"
        accepted.append(success)
    report = {
        "scope": "isolated fixed-DER legacy CHECKSIG, not the complete QSB lock",
        "source_revision": subprocess.check_output(
            ["git", "-C", str(a.app_root), "rev-parse", "HEAD"], text=True).strip(),
        "core_flags": "bitcoinconsensus_SCRIPT_FLAGS_VERIFY_ALL",
        "native_files_sha256": native_hashes,
        "image": a.image,
        "accepted_count": sum(accepted),
        "rejected_sighash_bytes": [i for i, ok in enumerate(accepted) if not ok],
        "accepted_all_256": all(accepted),
    }
    a.output.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({k: report[k] for k in
                      ("accepted_count", "rejected_sighash_bytes", "accepted_all_256")}, indent=2))
    assert report["accepted_all_256"], "Pinned Core did not accept all sighash bytes"


if __name__ == "__main__":
    main()
