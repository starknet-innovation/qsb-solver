"""Probe legacy FindAndDelete opcode-boundary behavior in pinned Core 27.2.

For each isolated bare CHECKSIG lock, recover a public key for the sighash
computed with the app's FindAndDelete result. Core must accept that key and
reject one recovered for a deliberately wrong scriptCode. The signatures and
transactions are disposable public test material. This tests selected source
cases, not an arbitrary-script equivalence theorem or the complete QSB lock.
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

    root = Path(__file__).resolve().parents[1]
    pinned = json.loads((root / "evidence/source-inventory.json").read_text())["app"]
    source_hash = hashlib.sha256((args.app_root / "worker/cpu/bitcoin_tx.py").read_bytes()).hexdigest()
    ec_hash = hashlib.sha256((args.app_root / "worker/cpu/secp256k1.py").read_bytes()).hexdigest()
    assert source_hash == pinned["files"]["worker/cpu/bitcoin_tx.py"]
    assert ec_hash == pinned["files"]["worker/cpu/secp256k1.py"]

    tx = bt.Transaction(version=1, locktime=0)
    tx.add_input(bt.TxIn(b"\x44" * 32, 0, b"", 0xFFFFFFFE))
    tx.add_input(bt.TxIn(b"\x55" * 32, 0, b"", 0xFFFFFFFE))
    tx.add_output(bt.TxOut(90000, b"\x51"))
    r, s = bt._valid_small_r_values()[0], 17
    sig = ec.encode_der_sig(r, s, sighash=1)
    pattern = bt.push_data(sig)
    drop_checksig = b"\x75\xac"
    locks = [
        ("one_canonical_push", pattern + drop_checksig,
         pattern + drop_checksig),
        ("two_canonical_pushes", pattern + b"\x75" + pattern + drop_checksig,
         pattern + b"\x75" + pattern + drop_checksig),
        ("adjacent_canonical_pushes", pattern + pattern + b"\x6d\xac",
         pattern + pattern + b"\x6d\xac"),
        ("embedded_pattern_inside_push",
         bt.push_data(b"\xaa" + pattern + b"\xbb") + drop_checksig,
         bt.push_data(b"\xaa" + pattern + b"\xbb").replace(pattern, b"") +
         drop_checksig),
        ("noncanonical_pushdata1",
         b"\x4c" + bytes((len(sig),)) + sig + drop_checksig,
         drop_checksig),
        ("noncanonical_pushdata2",
         b"\x4d" + len(sig).to_bytes(2, "little") + sig + drop_checksig,
         drop_checksig),
        ("noncanonical_pushdata4",
         b"\x4e" + len(sig).to_bytes(4, "little") + sig + drop_checksig,
         drop_checksig),
    ]
    pin_k = int.from_bytes(hashlib.sha256(b"qsb_pin_nonce").digest(), "big") % ec.N
    pin_r = ec.point_mul(pin_k, ec.G)[0] % ec.N
    pin_s = max(1, int.from_bytes(hashlib.sha256(b"qsb_pin_s").digest()[:16],
                                  "big") % (ec.N // 2))
    pin_sig = ec.encode_der_sig(pin_r, pin_s, sighash=1)
    pin_pattern = bt.push_data(pin_sig)
    assert len(pin_sig) == 56
    locks.append(("literal_pinning_signature_push",
                  pin_pattern + drop_checksig,
                  pin_pattern + drop_checksig))
    native = args.native_root.resolve()

    def recovered_pubkey(script_code: bytes, sig_r: int, sig_s: int) -> bytes:
        z = tx.sighash(1, script_code, 1)
        point = ec.ecdsa_recover(sig_r, sig_s, z, 0)
        assert point and ec.ecdsa_verify(point, z, sig_r, sig_s)
        return ec.compress_pubkey(point)

    def core_accepts(lock: bytes, pubkey: bytes, case_sig: bytes) -> tuple[bool, str]:
        tx.inputs[1].script_sig = bt.push_data(case_sig) + bt.push_data(pubkey)
        raw_tx = tx.serialize()
        payload = f"{raw_tx.hex()}\n2\n1000\n51\n100000\n{lock.hex()}\n"
        run = subprocess.run([
            "docker", "run", "--rm", "--network", "none", "--read-only",
            "--cap-drop=ALL", "--security-opt=no-new-privileges",
            "--platform=linux/arm64", "-i", "-v", f"{native}:/native:ro",
            args.image, "/native/qsb-consensus"],
            input=payload, text=True, capture_output=True, timeout=30)
        if run.returncode not in (0, 1):
            raise RuntimeError(run.stderr)
        accepted = (run.returncode == 0 and
                    run.stdout.strip() == "core-27.2-api2-all-inputs-valid")
        return accepted, hashlib.sha256(raw_tx).hexdigest()

    cases = []
    for name, lock, wrong_code in locks:
        case_sig = pin_sig if name == "literal_pinning_signature_push" else sig
        case_r, case_s = (pin_r, pin_s) if case_sig == pin_sig else (r, s)
        script_code = bt.find_and_delete(lock, case_sig)
        assert script_code != wrong_code
        correct_pub = recovered_pubkey(script_code, case_r, case_s)
        wrong_pub = recovered_pubkey(wrong_code, case_r, case_s)
        assert correct_pub != wrong_pub
        positive, positive_tx = core_accepts(lock, correct_pub, case_sig)
        negative, negative_tx = core_accepts(lock, wrong_pub, case_sig)
        case = {
            "name": name, "lock_hex": lock.hex(),
            "signature_hex": case_sig.hex(),
            "script_code_hex": script_code.hex(),
            "wrong_script_code_hex": wrong_code.hex(),
            "correct_pubkey_hex": correct_pub.hex(),
            "wrong_pubkey_hex": wrong_pub.hex(),
            "positive_accepted": positive, "negative_accepted": negative,
            "positive_tx_sha256": positive_tx,
            "negative_tx_sha256": negative_tx,
        }
        cases.append(case)
        assert positive and not negative, case

    report = {
        "scope": "isolated bare legacy FindAndDelete cases, not QSB lock",
        "core_flags": "bitcoinconsensus_SCRIPT_FLAGS_VERIFY_ALL",
        "signature_hex": sig.hex(),
        "pin_signature_hex": pin_sig.hex(),
        "pinned_source_revision": pinned["revision"],
        "builder_sha256": source_hash,
        "secp256k1_sha256": ec_hash,
        "source_revision": subprocess.check_output(
            ["git", "-C", str(args.app_root), "rev-parse", "HEAD"],
            text=True).strip(),
        "image": args.image,
        "native_executable_sha256": hashlib.sha256(
            (native / "qsb-consensus").read_bytes()).hexdigest(),
        "native_library_sha256": hashlib.sha256(
            (native / "libbitcoinconsensus.so.0").read_bytes()).hexdigest(),
        "cases": cases,
    }
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"case_count": len(cases),
                      "positive_accepted": sum(c["positive_accepted"]
                                               for c in cases),
                      "negative_rejected": sum(not c["negative_accepted"]
                                               for c in cases)}, indent=2))


if __name__ == "__main__":
    main()
