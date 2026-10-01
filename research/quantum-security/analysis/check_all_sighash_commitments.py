"""Probe the literal legacy SIGHASH_ALL transaction commitment in Core 27.2.

This uses a fixed DER signature in an isolated bare CHECKSIG lock. The app's
source-shaped serializer calculates each message and public recovery produces
the corresponding verification key. Pinned Core checks the positive and
same-key controls. It is finite evidence, not an arbitrary-transaction proof
or a full QSB-lock spend.
"""

import argparse
import copy
import hashlib
import json
import struct
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
    for name in ("worker/cpu/bitcoin_tx.py", "worker/cpu/secp256k1.py"):
        actual = hashlib.sha256((args.app_root / name).read_bytes()).hexdigest()
        assert actual == pinned["files"][name], (name, actual)

    tx = bt.Transaction(version=2, locktime=1234567)
    tx.add_input(bt.TxIn(b"\x44" * 32, 0, b"", 0xfffffffe))
    tx.add_input(bt.TxIn(b"\x55" * 32, 1, b"", 0x80000000))
    tx.add_output(bt.TxOut(90000, b"\x00\x14" + b"\x66" * 20))
    tx.add_output(bt.TxOut(1000, b"\x51"))
    r, s = bt._valid_small_r_values()[0], 17
    sig = ec.encode_der_sig(r, s, sighash=1)
    lock = bt.push_data(sig) + bytes([bt.OP_SWAP, bt.OP_CHECKSIG])
    script_code = bt.find_and_delete(lock, sig)
    assert script_code == bytes([bt.OP_SWAP, bt.OP_CHECKSIG])
    native = args.native_root.resolve()

    def preimage(t):
        """An independent, literal ALL layout using the app's field writers."""
        data = struct.pack("<I", t.version)
        data += bt.serialize_varint(len(t.inputs))
        for i, inp in enumerate(t.inputs):
            script = script_code if i == 1 else b""
            data += bt.TxIn(inp.txid, inp.vout, script, inp.sequence).serialize()
        data += bt.serialize_varint(len(t.outputs))
        for out in t.outputs:
            data += out.serialize()
        return data + struct.pack("<I", t.locktime) + struct.pack("<I", 1)

    def message(t):
        data = preimage(t)
        digest = bt.sha256d(data)
        assert int.from_bytes(digest, "big") == t.sighash(1, script_code, 1)
        return data, digest

    def recover_pubkey(t):
        _, digest = message(t)
        z = int.from_bytes(digest, "big")
        point = ec.ecdsa_recover(r, s, z, 0)
        assert point and ec.ecdsa_verify(point, z, r, s)
        return ec.compress_pubkey(point)

    def core_accepts(t, key, signed_script=None):
        t = copy.deepcopy(t)
        t.inputs[1].script_sig = bt.push_data(key) if signed_script is None else signed_script
        raw = t.serialize()
        payload = (f"{raw.hex()}\n2\n1000\n51\n100000\n{lock.hex()}\n")
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
        return accepted, raw.hex()

    baseline_preimage, baseline_digest = message(tx)
    baseline_key = recover_pubkey(tx)
    assert core_accepts(tx, baseline_key)[0]
    cases = []

    def record(name, candidate, changed_preimage, signed_script=None):
        data, digest = message(candidate)
        fresh_key = recover_pubkey(candidate)
        old_ok, old_raw = core_accepts(candidate, baseline_key, signed_script)
        fresh_ok, fresh_raw = core_accepts(candidate, fresh_key, signed_script)
        case = {
            "name": name,
            "preimage_hex": data.hex(),
            "digest_sha256d_hex": digest.hex(),
            "same_preimage_as_baseline": data == baseline_preimage,
            "same_digest_as_baseline": digest == baseline_digest,
            "fresh_pubkey_hex": fresh_key.hex(),
            "old_key_accepted": old_ok,
            "fresh_key_accepted": fresh_ok,
            "old_key_raw_tx_hex": old_raw,
            "fresh_key_raw_tx_hex": fresh_raw,
        }
        cases.append(case)
        assert (data != baseline_preimage) == changed_preimage, case
        assert (digest != baseline_digest) == changed_preimage, case
        assert old_ok == (not changed_preimage) and fresh_ok, case

    record("baseline", copy.deepcopy(tx), False)
    t = copy.deepcopy(tx)
    t.outputs[0].value -= 1
    record("output_amount", t, True)
    t = copy.deepcopy(tx)
    t.outputs[0].script_pubkey = b"\x00\x14" + b"\x77" * 20
    record("output_script", t, True)
    t = copy.deepcopy(tx)
    t.outputs.reverse()
    record("output_order", t, True)
    t = copy.deepcopy(tx)
    t.add_output(bt.TxOut(5, b"\x51"))
    record("output_count", t, True)
    t = copy.deepcopy(tx)
    t.outputs[0].script_pubkey = b"\x51" * 253
    record("output_script_compactsize_253", t, True)
    t = copy.deepcopy(tx)
    for _ in range(251):
        t.add_output(bt.TxOut(0, b""))
    assert len(t.outputs) == 253
    record("output_count_compactsize_253", t, True)
    t = copy.deepcopy(tx)
    t.inputs[1].txid = b"\x56" * 32
    record("signed_input_prevout", t, True)
    t = copy.deepcopy(tx)
    t.inputs[0].sequence -= 1
    record("other_input_sequence", t, True)
    t = copy.deepcopy(tx)
    t.version += 1
    record("version", t, True)
    t = copy.deepcopy(tx)
    t.locktime += 1
    record("locktime", t, True)
    t = copy.deepcopy(tx)
    t.inputs[0].script_sig = b"\x51\x75"  # OP_1 OP_DROP; empty stack remains.
    record("other_input_script_sig", t, False)
    nonminimal_key_push = b"\x4c" + bytes((len(baseline_key),)) + baseline_key
    record("signed_input_script_sig_encoding", copy.deepcopy(tx), False,
           nonminimal_key_push)

    report = {
        "scope": "isolated fixed-signature legacy ALL, not the QSB lock or universal binding",
        "source_revision": pinned["revision"],
        "source_sha256": {name: pinned["files"][name] for name in
                          ("worker/cpu/bitcoin_tx.py", "worker/cpu/secp256k1.py")},
        "core_flags": "bitcoinconsensus_SCRIPT_FLAGS_VERIFY_ALL",
        "image": args.image,
        "native_executable_sha256": hashlib.sha256(
            (native / "qsb-consensus").read_bytes()).hexdigest(),
        "native_library_sha256": hashlib.sha256(
            (native / "libbitcoinconsensus.so.0").read_bytes()).hexdigest(),
        "signature_hex": sig.hex(),
        "lock_hex": lock.hex(),
        "script_code_hex": script_code.hex(),
        "baseline_pubkey_hex": baseline_key.hex(),
        "cases": cases,
    }
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"case_count": len(cases),
                      "old_key_accepted": sum(c["old_key_accepted"] for c in cases),
                      "fresh_key_accepted": sum(c["fresh_key_accepted"] for c in cases)},
                     indent=2))


if __name__ == "__main__":
    main()
