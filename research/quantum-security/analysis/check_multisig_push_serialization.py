"""Probe Core's deletion of a skipped long CHECKMULTISIG signature push.

An invalid lower signature is never reached after the upper signature fails
against both keys. FindAndDelete must nevertheless remove its push from the
shared scriptCode before that pair scan. Keys recovered for the code with and
without deletion make the difference observable through whether Core reaches
the malformed lower signature. This is an isolated unfunded bare-script probe.
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
        assert hashlib.sha256((args.app_root / name).read_bytes()).hexdigest() == pinned["files"][name]
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

    tx = bt.Transaction(version=1, locktime=0)
    tx.add_input(bt.TxIn(b"\x44" * 32, 0, b"", 0xFFFFFFFE))
    tx.add_input(bt.TxIn(b"\x55" * 32, 0, b"", 0xFFFFFFFE))
    tx.add_output(bt.TxOut(90000, b"\x51"))
    r, s = bt._valid_small_r_values()[0], 17
    upper = ec.encode_der_sig(r, s, sighash=1)

    def recovered_key(script_code: bytes) -> bytes:
        z = tx.sighash(1, script_code, 1)
        for recovery_id in range(4):
            point = ec.ecdsa_recover(r, s, z, recovery_id)
            if point and ec.ecdsa_verify(point, z, r, s):
                return ec.compress_pubkey(point)
        raise AssertionError("no recovery key")

    def core(lock: bytes, lower: bytes, pubkey: bytes) -> dict:
        # Bottom-to-top: NULLDUMMY, lower sig, upper sig, two sigs, two keys.
        tx.inputs[1].script_sig = (
            b"\x00" + bt.push_data(lower) + bt.push_data(upper) +
            b"\x52" + bt.push_data(pubkey) * 2
        )
        payload = (
            f"{tx.serialize().hex()}\n2\n1000\n51\n100000\n{lock.hex()}\n"
        )
        run = subprocess.run([
            "docker", "run", "--rm", "--network", "none", "--read-only",
            "--cap-drop=ALL", "--security-opt=no-new-privileges",
            "--platform=linux/arm64", "-i", "-v",
            f"{args.native_root.resolve()}:/native:ro", args.image,
            "/native/qsb-consensus"],
            input=payload, text=True, capture_output=True, timeout=30)
        if run.returncode not in (0, 1):
            raise RuntimeError(run.stderr)
        return {
            "accepted": run.returncode == 0 and
                        run.stdout.strip() == "core-27.2-api2-all-inputs-valid",
            "returncode": run.returncode,
            "stdout": run.stdout.strip(),
            "stderr": run.stderr.strip(),
            "raw_tx_sha256": hashlib.sha256(tx.serialize()).hexdigest(),
        }

    cases = []
    for size in (75, 76, 255, 256, 520):
        lower = b"\x01" * size  # Nonempty and invalid under DERSIG.
        pattern = bt.push_data(lower)
        lock = pattern + b"\x75\x52\xae\x75\x51"
        deleted = bt.find_and_delete(lock, lower)
        assert deleted == b"\x75\x52\xae\x75\x51"
        correct_key = recovered_key(deleted)
        retained_key = recovered_key(lock)
        assert correct_key != retained_key

        # Correct deletion makes the upper signature match, so Core attempts
        # the malformed lower signature and aborts. Retaining the push makes
        # the upper signature fail; Core skips the lower one and returns false,
        # which the lock drops before pushing true.
        reaches_malformed = core(lock, lower, correct_key)
        skips_malformed = core(lock, lower, retained_key)
        assert not reaches_malformed["accepted"]
        assert skips_malformed["accepted"], (size, skips_malformed)
        cases.append({
            "signature_length": size,
            "push_prefix_hex": pattern[:len(pattern) - size].hex(),
            "lock_sha256": hashlib.sha256(lock).hexdigest(),
            "deleted_code_sha256": hashlib.sha256(deleted).hexdigest(),
            "retained_code_sha256": hashlib.sha256(lock).hexdigest(),
            "correct_key_hex": correct_key.hex(),
            "retained_key_hex": retained_key.hex(),
            "reaches_malformed": reaches_malformed,
            "skips_malformed": skips_malformed,
        })

    report = {
        "scope": "isolated Core 27.2 first-scan deletion and early-exit probe; not QSB acceptance",
        "source_revision": pinned["revision"],
        "image": args.image,
        "native_files_sha256": native_hashes,
        "upper_signature_hex": upper.hex(),
        "cases": cases,
    }
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"case_count": len(cases),
                      "skipped_accepted": sum(c["skips_malformed"]["accepted"] for c in cases)},
                     indent=2))


if __name__ == "__main__":
    main()
