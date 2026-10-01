"""Probe Core's false CHECKMULTISIG early exit before an unreachable DER gate.

This uses disposable keys and a tiny isolated bare script. A malformed lower
signature must be ignored after the first failed comparison makes two
remaining signatures impossible to match against one remaining key. The
same top signature is also tested without DROP, to confirm the returned
CHECKMULTISIG Boolean is false. No QSB lock or funded output is spent.
"""

import argparse
import hashlib
import json
import subprocess
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--app-root", type=Path, required=True)
    parser.add_argument("--native-root", type=Path, required=True)
    parser.add_argument("--image", required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()

    pinned = json.loads((ROOT / "evidence/source-inventory.json").read_text())["app"]
    for name in ("worker/cpu/bitcoin_tx.py", "worker/cpu/secp256k1.py"):
        digest = hashlib.sha256((args.app_root / name).read_bytes()).hexdigest()
        assert digest == pinned["files"][name]
    prior = json.loads((ROOT / "evidence/find-and-delete-boundary.json").read_text())
    assert args.image == prior["image"]
    native_hashes = {
        "qsb-consensus": prior["native_executable_sha256"],
        "libbitcoinconsensus.so.0": prior["native_library_sha256"],
    }
    for name, digest in native_hashes.items():
        assert hashlib.sha256((args.native_root / name).read_bytes()).hexdigest() == digest

    sys.path.insert(0, str(args.app_root / "worker/cpu"))
    import bitcoin_tx as bt
    import secp256k1 as ec

    pubkey = ec.compress_pubkey(ec.G)
    well_formed = ec.encode_der_sig(1, 1, sighash=1)
    malformed = b"\x01"
    # Two keys, two signatures, and Core's extra CHECKMULTISIG dummy.
    # The top signature is the last one pushed by scriptSig.
    lock = b"\x52" + bt.push_data(pubkey) * 2 + b"\x52\xae"
    tx = bt.Transaction(version=1, locktime=0)
    tx.add_input(bt.TxIn(b"\x44" * 32, 0, b"", 0xFFFFFFFE))
    tx.add_input(bt.TxIn(b"\x55" * 32, 0, b"", 0xFFFFFFFE))
    tx.add_output(bt.TxOut(90000, b"\x51"))
    assert not ec.ecdsa_verify(ec.G, tx.sighash(1, lock + b"\x75\x51", 1), 1, 1)

    def core(script_sig: bytes, suffix: bytes) -> dict:
        tx.inputs[1].script_sig = script_sig
        script = lock + suffix
        payload = f"{tx.serialize().hex()}\n2\n1000\n51\n100000\n{script.hex()}\n"
        run = subprocess.run([
            "docker", "run", "--rm", "--network", "none", "--read-only",
            "--cap-drop=ALL", "--security-opt=no-new-privileges",
            "--platform=linux/arm64", "-i", "-v",
            f"{args.native_root.resolve()}:/native:ro", args.image,
            "/native/qsb-consensus"],
            input=payload, text=True, capture_output=True, timeout=30)
        if run.returncode not in (0, 1):
            raise RuntimeError(run.stderr)
        return {"accepted": run.returncode == 0 and
                run.stdout.strip() == "core-27.2-api2-all-inputs-valid",
                "returncode": run.returncode,
                "stdout": run.stdout.strip(),
                "stderr": run.stderr.strip(),
                "script_sha256": hashlib.sha256(script).hexdigest(),
                "raw_tx_sha256": hashlib.sha256(tx.serialize()).hexdigest()}

    skipped = b"\x00" + bt.push_data(malformed) + bt.push_data(well_formed)
    attempted = b"\x00" + bt.push_data(well_formed) + bt.push_data(malformed)
    results = {
        "malformed_unreachable_drop_true": core(skipped, b"\x75\x51"),
        "malformed_unreachable_no_drop": core(skipped, b""),
        "malformed_attempted_drop_true": core(attempted, b"\x75\x51"),
    }
    assert results["malformed_unreachable_drop_true"]["accepted"]
    assert not results["malformed_unreachable_no_drop"]["accepted"]
    assert not results["malformed_attempted_drop_true"]["accepted"]
    report = {
        "scope": "isolated Core 27.2 bare CHECKMULTISIG early-exit probe; not QSB acceptance",
        "source_revision": pinned["revision"],
        "image": args.image,
        "native_files_sha256": native_hashes,
        "well_formed_signature_hex": well_formed.hex(),
        "malformed_signature_hex": malformed.hex(),
        "results": results,
    }
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({name: row["accepted"] for name, row in results.items()}, indent=2))


if __name__ == "__main__":
    main()
