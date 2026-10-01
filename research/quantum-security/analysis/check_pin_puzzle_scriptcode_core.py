"""Probe Core's legacy FindAndDelete for a valid 32-byte ECDSA signature.

These are isolated, disposable bare scripts, not the QSB lock. The first has
no push-32 opcode and retains its entire scriptCode. The second contains one
exact push-32 opcode and deletes it. Each case uses a key recovered for the
expected sighash, plus a negative key recovered for the wrong scriptCode.
"""

import argparse
import hashlib
import json
import subprocess
import sys
from pathlib import Path


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--app-root", type=Path, required=True)
    parser.add_argument("--native-root", type=Path, required=True)
    parser.add_argument("--image", required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    pinned = json.loads((root / "evidence/source-inventory.json").read_text())["app"]
    for name in ("worker/cpu/bitcoin_tx.py", "worker/cpu/secp256k1.py"):
        assert sha256((args.app_root / name).read_bytes()) == pinned["files"][name]
    prior = json.loads((root / "evidence/roll-core.json").read_text())
    assert args.image == prior["image"]
    native = args.native_root.resolve()
    for name, expected in prior["native_files_sha256"].items():
        assert sha256((native / name).read_bytes()) == expected
    sys.path.insert(0, str(args.app_root / "worker/cpu"))
    import bitcoin_tx as bt
    import secp256k1 as ec

    r = bt._valid_small_r_values()[0]
    s = (1 << 184) + 17  # exactly 24 DER integer bytes
    tx = bt.Transaction(version=1, locktime=0)
    tx.add_input(bt.TxIn(b"\x11" * 32, 0, bytes([bt.OP_1])))
    tx.add_input(bt.TxIn(b"\x22" * 32, 0, b""))
    tx.add_output(bt.TxOut(90000, bytes([bt.OP_1])))
    tx.add_output(bt.TxOut(1000, bytes([bt.OP_1])))

    def recovered_key(script_code: bytes, hash_type: int) -> bytes:
        z = tx.sighash(1, script_code, hash_type)
        point = ec.ecdsa_recover(r, s, z, 0)
        assert point and ec.ecdsa_verify(point, z, r, s)
        return ec.compress_pubkey(point)

    def accepts(lock: bytes, sig: bytes, key: bytes) -> tuple[bool, str]:
        tx.inputs[1].script_sig = bt.push_data(sig) + bt.push_data(key)
        raw = tx.serialize()
        payload = f"{raw.hex()}\n2\n1000\n51\n100000\n{lock.hex()}\n"
        run = subprocess.run(
            ["docker", "run", "--rm", "--network", "none", "--read-only",
             "--cap-drop=ALL", "--security-opt=no-new-privileges",
             "--platform=linux/arm64", "-i", "-v", f"{native}:/native:ro",
             args.image, "/native/qsb-consensus"],
            input=payload, text=True, capture_output=True, timeout=30,
        )
        if run.returncode not in (0, 1):
            raise RuntimeError(run.stderr)
        accepted = (run.returncode == 0 and
                    run.stdout.strip() == "core-27.2-api2-all-inputs-valid")
        return accepted, sha256(raw)

    results = []
    for hash_type in (0x01, 0x03, 0xFF):
        sig = ec.encode_der_sig(r, s, sighash=hash_type)
        assert len(sig) == 32 and ec.is_valid_der_sig(sig)
        assert bt.push_data(sig) == b"\x20" + sig
        no_push = bytes([bt.OP_CHECKSIG])
        with_push = bt.push_data(sig) + bytes([0x75, bt.OP_CHECKSIG])
        cases = [
            ("no_push32", no_push, no_push, b""),
            ("one_push32", with_push, bytes([0x75, bt.OP_CHECKSIG]), with_push),
        ]
        for name, lock, expected_code, wrong_code in cases:
            tx.inputs[1].script_sig = b""
            assert bt.find_and_delete(lock, sig) == expected_code
            correct_key = recovered_key(expected_code, hash_type)
            wrong_key = recovered_key(wrong_code, hash_type)
            assert correct_key != wrong_key
            positive, positive_tx = accepts(lock, sig, correct_key)
            negative, negative_tx = accepts(lock, sig, wrong_key)
            assert positive and not negative, (name, hash_type)
            results.append({
                "name": name, "hash_type_hex": f"{hash_type:02x}",
                "signature_hex": sig.hex(), "lock_hex": lock.hex(),
                "expected_script_code_hex": expected_code.hex(),
                "wrong_script_code_hex": wrong_code.hex(),
                "positive_accepted": positive, "negative_accepted": negative,
                "positive_tx_sha256": positive_tx,
                "negative_tx_sha256": negative_tx,
            })

    report = {
        "scope": "isolated 32-byte legacy signature deletion; not QSB acceptance",
        "core_flags": "bitcoinconsensus_SCRIPT_FLAGS_VERIFY_ALL",
        "app_source_revision": pinned["revision"],
        "app_checkout_revision": subprocess.check_output(
            ["git", "-C", str(args.app_root), "rev-parse", "HEAD"],
            text=True).strip(),
        "image": args.image,
        "native_files_sha256": prior["native_files_sha256"],
        "hash_types_hex": ["01", "03", "ff"],
        "cases": results,
    }
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"signature_bytes": 32,
                      "positive_accepted": len(results),
                      "negative_rejected": len(results)}))


if __name__ == "__main__":
    main()
