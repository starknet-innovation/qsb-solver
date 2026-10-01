"""Check one 20-byte fixed ECDSA signature against pinned Core 27.2.

This is an isolated bare CHECKSIG experiment with disposable transaction data.
It establishes that the nonce-width exception in DynamicSignedSource cannot be
removed by assuming a 20-byte DER signature always fails Core verification.
It does not produce a HASH160 preimage or execute the QSB lock.
"""

import argparse
import hashlib
import json
import subprocess
import sys
from pathlib import Path


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--app-root", type=Path, required=True)
    parser.add_argument("--native-root", type=Path, required=True)
    parser.add_argument("--image", required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    sys.path.insert(0, str(args.app_root / "worker/cpu"))
    import bitcoin_tx as bt
    import secp256k1 as ec

    # r=1 has two curve points, and the 12-byte s makes the DER+ALL string
    # exactly 20 bytes. Both scalars are valid and nonzero.
    r, s = 1, (1 << 88) + 17
    signature = ec.encode_der_sig(r, s, sighash=1)
    assert len(signature) == 20
    lock = bytes([bt.OP_CHECKSIG])
    tx = bt.Transaction(version=1, locktime=0)
    tx.add_input(bt.TxIn(b"\x44" * 32, 0, b"", 0xFFFFFFFE))
    tx.add_input(bt.TxIn(b"\x55" * 32, 0, b"", 0xFFFFFFFE))
    tx.add_output(bt.TxOut(90000, b"\x51"))
    z = tx.sighash(1, lock, 1)
    pub_point = ec.ecdsa_recover(r, s, z, 0)
    assert pub_point is not None and ec.ecdsa_verify(pub_point, z, r, s)
    pubkey = ec.compress_pubkey(pub_point)
    wrong_key = ec.compress_pubkey(ec.G)
    assert wrong_key != pubkey
    native = args.native_root.resolve()

    def core_case(name: str, key: bytes, altered_output: bool, expected: bool) -> dict:
        tx.outputs[0] = bt.TxOut(90001 if altered_output else 90000, b"\x51")
        tx.inputs[1].script_sig = bt.push_data(signature) + bt.push_data(key)
        raw_tx = tx.serialize()
        payload = f"{raw_tx.hex()}\n2\n1000\n51\n100000\n{lock.hex()}\n"
        run = subprocess.run([
            "docker", "run", "--rm", "--network", "none", "--read-only",
            "--cap-drop=ALL", "--security-opt=no-new-privileges",
            "--platform=linux/arm64", "-i", "-v", f"{native}:/native:ro",
            args.image, "/native/qsb-consensus"],
            input=payload, text=True, capture_output=True, timeout=30)
        if run.returncode not in (0, 1):
            raise RuntimeError(f"Core unavailable for {name}: {run.stderr}")
        accepted = (run.returncode == 0 and
                    run.stdout.strip() == "core-27.2-api2-all-inputs-valid")
        assert accepted == expected, (name, run)
        return {"name": name, "accepted": accepted,
                "raw_tx_sha256": hashlib.sha256(raw_tx).hexdigest()}

    cases = [
        core_case("recovered_key", pubkey, False, True),
        core_case("wrong_key", wrong_key, False, False),
        core_case("changed_all_output", pubkey, True, False),
    ]
    report = {
        "scope": "isolated bare CHECKSIG, disposable transaction; no HASH160 preimage or QSB lock acceptance",
        "core_flags": "bitcoinconsensus_SCRIPT_FLAGS_VERIFY_ALL",
        "source_revision": subprocess.check_output(
            ["git", "-C", str(args.app_root), "rev-parse", "HEAD"],
            text=True).strip(),
        "image": args.image,
        "native_executable_sha256": hashlib.sha256(
            (native / "qsb-consensus").read_bytes()).hexdigest(),
        "native_library_sha256": hashlib.sha256(
            (native / "libbitcoinconsensus.so.0").read_bytes()).hexdigest(),
        "signature_hex": signature.hex(),
        "signature_length": len(signature),
        "recovered_pubkey_hex": pubkey.hex(),
        "sighash_all_scalar_hex": format(z, "064x"),
        "cases": cases,
    }
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"signature_length": len(signature), "cases": cases}, indent=2))


if __name__ == "__main__":
    main()
