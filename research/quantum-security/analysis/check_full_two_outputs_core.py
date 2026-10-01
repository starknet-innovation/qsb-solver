"""Probe a two-output withdrawal shape against the pinned Core 27.2 adapter.

Three hash-to-signature puzzle CHECKSIGVERIFY sites are changed to OP_2DROP.
Pinning, all 15 HORS comparisons, and both CHECKMULTISIGs remain real. All
secrets and signatures are disposable public test data; no transaction is
broadcast or funded. This is a finite consensus-interpreter experiment, not
an actual QSB spend or a universal Core-to-Lean refinement theorem.
"""

import argparse
import hashlib
import json
import random
import subprocess
import sys
from pathlib import Path

from check_round_results import opcodes


PINNED_BUILDER_SHA256 = "c7e52af90bd0d9fce9834fce26dcd67aee0d7751ee228d9730873c4d12659a5c"
PINNED_NATIVE_SHA256 = {
    "qsb-consensus": "9497dcf47c464fc49cbf54f806707bd67f04981c789c352bafb3805fe5d6dfcd",
    "libbitcoinconsensus.so.0": "5d7874783dc4989357600b3f273a44627d8ca6ac037f63d851572ff64a756983",
}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--app-root", type=Path, required=True)
    parser.add_argument("--native-root", type=Path, required=True)
    parser.add_argument("--image", required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    app_root = args.app_root.resolve()
    native_root = args.native_root.resolve()
    source_sha = hashlib.sha256(
        (app_root / "worker/cpu/bitcoin_tx.py").read_bytes()).hexdigest()
    assert source_sha == PINNED_BUILDER_SHA256
    native_hashes = {
        name: hashlib.sha256((native_root / name).read_bytes()).hexdigest()
        for name in PINNED_NATIVE_SHA256
    }
    assert native_hashes == PINNED_NATIVE_SHA256
    sys.path.insert(0, str(app_root / "worker/cpu"))
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

    def nonce_sig(label: bytes) -> bytes:
        k = int.from_bytes(hashlib.sha256(label + b"_nonce").digest(), "big") % ec.N
        r = ec.point_mul(k, ec.G)[0] % ec.N
        s = max(1, int.from_bytes(hashlib.sha256(label + b"_s").digest()[:16],
                                  "big") % (ec.N // 2))
        return ec.encode_der_sig(r, s, sighash=1)

    def recover(sig: bytes, message: int) -> bytes:
        r, s = parse_der(sig)
        for x in (r, r + ec.N):
            if x >= ec.P:
                continue
            for parity in (0, 1):
                point = ec.ecdsa_recover(x, s, message, parity)
                if point and ec.ecdsa_verify(point, message, r, s):
                    return ec.compress_pubkey(point)
        raise AssertionError("No disposable recovery key")

    pin = nonce_sig(b"qsb_pin")
    nonces = [nonce_sig(b"qsb_r0"), nonce_sig(b"qsb_r1")]
    exact = builder.build_full_script(pin, *nonces)
    assert hashlib.sha256(exact).hexdigest() == (
        "44f34e665e756e239aed514a530c136f582a0812437c4f32140a1ebe83628bba"
    )
    lock = bytearray(exact)
    sites = [i for i, op in opcodes(exact) if op == bt.OP_CHECKSIGVERIFY]
    assert len(sites) == 4
    for pos in sites[1:]:
        lock[pos] = 0x6d  # OP_2DROP at three puzzle sites only.
    lock = bytes(lock)
    subsets = {0: list(range(9)), 1: list(range(9))}
    indices = builder.compute_witness_indices(subsets)

    def transaction(two_outputs: bool) -> bt.Transaction:
        tx = bt.Transaction(version=1, locktime=1234567)
        tx.add_input(bt.TxIn(b"\x11" * 32, 0, b"", 0xfffffffe))
        tx.add_input(bt.TxIn(b"\x22" * 32, 0, b"", 0x80000000))
        tx.add_output(bt.TxOut(90000, b"\x00\x14" + b"\x33" * 20))
        if two_outputs:
            tx.add_output(bt.TxOut(1000, b"\x51"))
        return tx

    one_output = transaction(False)
    two_outputs = transaction(True)
    selected0 = builder.dummy_sigs[0][0]
    code0 = bt.find_and_delete(lock, nonces[0])
    for sig in builder.dummy_sigs[0][:9]:
        code0 = bt.find_and_delete(code0, sig)
    bug_digest = one_output.sighash(1, code0, selected0[-1])
    in_range_digest = two_outputs.sighash(1, code0, selected0[-1])
    assert bug_digest == 1 << 248
    assert in_range_digest != bug_digest

    def witness(tx: bt.Transaction, dummy_context: bt.Transaction) -> bytes:
        script_sig = bytearray()
        for round_index in (1, 0):
            selected = [builder.dummy_sigs[round_index][j]
                        for j in subsets[round_index]]
            script_code = bt.find_and_delete(lock, nonces[round_index])
            for sig in selected:
                script_code = bt.find_and_delete(script_code, sig)
            nonce_key = recover(nonces[round_index],
                                tx.sighash(1, script_code, 1))
            pubkeys = [recover(sig, dummy_context.sighash(
                1, script_code, sig[-1])) for sig in selected]
            script_sig += bt.push_data(ec.compress_pubkey(ec.G))
            script_sig += bt.push_data(nonce_key)
            for key in reversed(pubkeys):
                script_sig += bt.push_data(key)
            for j in range((7 if round_index else 8) - 1, -1, -1):
                script_sig += bt.push_data(
                    builder.hors_secrets[round_index][subsets[round_index][j]])
            for value in reversed(indices[round_index]):
                script_sig += bt.push_number(value)
        pin_key = recover(pin, tx.sighash(
            1, bt.find_and_delete(lock, pin), 1))
        script_sig += bt.push_data(ec.compress_pubkey(ec.G))
        script_sig += bt.push_data(pin_key)
        return bytes(script_sig)

    def core_accepts(tx: bt.Transaction) -> bool:
        payload = f"{tx.serialize().hex()}\n2\n1000\n51\n100000\n{lock.hex()}\n"
        process = subprocess.run([
            "docker", "run", "--rm", "--network", "none", "--read-only",
            "--cap-drop=ALL", "--security-opt=no-new-privileges",
            "--platform=linux/arm64", "-i",
            "-v", f"{native_root}:/native:ro", args.image,
            "/native/qsb-consensus"], input=payload, text=True,
            capture_output=True, timeout=30)
        if process.returncode not in (0, 1):
            raise RuntimeError(f"Pinned Core adapter unavailable: {process.stderr}")
        return (process.returncode == 0 and
                process.stdout.strip() == "core-27.2-api2-all-inputs-valid")

    cases = []

    def check(name: str, tx: bt.Transaction, expected: bool) -> None:
        accepted = core_accepts(tx)
        assert accepted == expected, (name, accepted, expected)
        cases.append({
            "name": name,
            "accepted": accepted,
            "expected": expected,
            "output_count": len(tx.outputs),
            "transaction_sha256": hashlib.sha256(tx.serialize()).hexdigest(),
        })

    one_output.inputs[1].script_sig = witness(one_output, one_output)
    check("one_output_bug_digest", one_output, True)
    two_outputs.inputs[1].script_sig = witness(two_outputs, one_output)
    check("two_outputs_old_dummy_keys", two_outputs, False)
    two_outputs.inputs[1].script_sig = witness(two_outputs, two_outputs)
    check("two_outputs_recovered_keys", two_outputs, True)
    two_outputs.outputs[1] = bt.TxOut(1001, b"\x51")
    check("two_outputs_changed_second_value", two_outputs, False)
    two_outputs.outputs[1] = bt.TxOut(1000, b"\x51")
    two_outputs.outputs[0] = bt.TxOut(90001, b"\x00\x14" + b"\x33" * 20)
    # The SINGLE dummy checks keep the original two-output recovery keys.
    # The fixed ALL pin and nonce checks get keys for this changed transaction.
    two_outputs.inputs[1].script_sig = witness(two_outputs, transaction(True))
    check("two_outputs_changed_first_value_same_dummy_keys", two_outputs, True)

    report = {
        "scope": "Two-input disposable full lock with three puzzle CHECKSIGVERIFY sites relaxed; 15 HORS comparisons, pinning and both CHECKMULTISIGs remain real. Input 1 uses in-range SIGHASH_SINGLE when two outputs exist. Not a full QSB spend or universal Core refinement.",
        "builder_sha256": source_sha,
        "exact_lock_sha256": hashlib.sha256(exact).hexdigest(),
        "test_lock_sha256": hashlib.sha256(lock).hexdigest(),
        "native_files_sha256": native_hashes,
        "image": args.image,
        "bug_message_scalar_hex": f"{bug_digest:064x}",
        "in_range_message_scalar_hex": f"{in_range_digest:064x}",
        "cases": cases,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"cases": [{"name": c["name"], "accepted": c["accepted"]}
                                  for c in cases]}, indent=2))


if __name__ == "__main__":
    main()
