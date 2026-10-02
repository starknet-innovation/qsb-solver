"""Probe a final subset switch through the disposable full Config A lock.

The three hash-to-signature puzzle CHECKSIGVERIFY opcodes are replaced with
OP_2DROP. Pinning, HORS comparisons, both CHECKMULTISIGs, and in-range
SIGHASH_SINGLE/ALL checks remain active. Every transaction is synthetic and
unfunded. This finite experiment is not an accepted spend of the real lock.
"""

import argparse
import hashlib
import json
import random
import subprocess
import sys
from pathlib import Path

from check_round_results import opcodes


IMAGE = "ubuntu@sha256:b1066385161d28ddf6bc7e7b28a9170eec11484c821d1a5150d176cbde41d7f7"


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--app-root", type=Path, required=True)
    parser.add_argument("--native-root", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    app = args.app_root.resolve()
    native = args.native_root.resolve()
    inventory = json.loads((root / "evidence/source-inventory.json").read_text())
    boundary = json.loads((root / "evidence/bonus-indices.json").read_text())
    for name in ("bitcoin_tx.py", "secp256k1.py", "qsb_pipeline.py"):
        rel = f"worker/cpu/{name}"
        assert hashlib.sha256((app / rel).read_bytes()).hexdigest() == (
            inventory["app"]["files"][rel]
        )
    native_hashes = {
        name: hashlib.sha256((native / name).read_bytes()).hexdigest()
        for name in ("qsb-consensus", "libbitcoinconsensus.so.0")
    }
    assert native_hashes == boundary["native_files_sha256"]
    sys.path.insert(0, str(app / "worker/cpu"))
    import bitcoin_tx as bt
    import secp256k1 as ec
    from qsb_pipeline import parse_der

    builder = bt.QSBScriptBuilder(150, 8, 1, 7, 2, hash_mode="sha256")
    rng = random.Random("QSB security analysis: PUBLIC DISPOSABLE TEST MATERIAL")
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

    pin = nonce_sig(b"qsb_pin")
    nonces = [nonce_sig(b"qsb_r0"), nonce_sig(b"qsb_r1")]
    exact = builder.build_full_script(pin, *nonces)
    assert hashlib.sha256(exact).hexdigest() == (
        "44f34e665e756e239aed514a530c136f582a0812437c4f32140a1ebe83628bba"
    )
    lock = bytearray(exact)
    sites = [index for index, op in opcodes(exact)
             if op == bt.OP_CHECKSIGVERIFY]
    assert len(sites) == 4
    for index in sites[1:]:
        lock[index] = 0x6d  # OP_2DROP; the first site (pinning) remains real.
    lock = bytes(lock)
    assert hashlib.sha256(lock).hexdigest() == (
        "0f635f137ca6bf6f188ea31a7c73d518ba482c23dc378c0f18d7ef2e6d027e1f"
    )

    subsets = {0: list(range(9)), 1: list(range(9))}
    indices = builder.compute_witness_indices(subsets)
    tx = bt.Transaction(version=1, locktime=1234567)
    tx.add_input(bt.TxIn(b"\x11" * 32, 0, b"", 0xfffffffe))
    tx.add_input(bt.TxIn(b"\x22" * 32, 0, b"", 0x80000000))
    tx.add_output(bt.TxOut(90000, b"\x00\x14" + b"\x33" * 20))
    tx.add_output(bt.TxOut(1000, b"\x51"))

    def recover(sig: bytes, z: int) -> bytes:
        r, s = parse_der(sig)
        for x in (r, r + ec.N):
            if x >= ec.P:
                continue
            for parity in (0, 1):
                point = ec.ecdsa_recover(x, s, z, parity)
                if point and ec.ecdsa_verify(point, z, r, s):
                    return ec.compress_pubkey(point)
        raise AssertionError("Disposable signature has no recovered key")

    def witness(bonus_index: int, old_final_nonce_key: bytes | None = None
                ) -> tuple[bytes, bytes, bytes, int, list[int]]:
        result = bytearray()
        final_code = b""
        final_key = b""
        final_digest = -1
        final_ids: list[int] = []
        for round_index in (1, 0):
            selected_ids = list(subsets[round_index])
            if round_index == 1:
                selected_ids[8] = bonus_index - 2
            selected = [builder.dummy_sigs[round_index][j]
                        for j in selected_ids]
            assert len(set(selected)) == 9
            script_code = bt.find_and_delete(lock, nonces[round_index])
            for sig in selected:
                script_code = bt.find_and_delete(script_code, sig)
            nonce_digest = tx.sighash(1, script_code, 1)
            nonce_key = recover(nonces[round_index], nonce_digest)
            pubkeys = [recover(sig, tx.sighash(1, script_code, sig[-1]))
                       for sig in selected]
            result += bt.push_data(ec.compress_pubkey(ec.G))
            result += bt.push_data(
                old_final_nonce_key if round_index == 1 and
                old_final_nonce_key is not None else nonce_key)
            for key in reversed(pubkeys):
                result += bt.push_data(key)
            for j in range((7 if round_index else 8) - 1, -1, -1):
                result += bt.push_data(
                    builder.hors_secrets[round_index][subsets[round_index][j]])
            reached_indices = list(indices[round_index])
            if round_index == 1:
                reached_indices[8] = bonus_index
                final_code = script_code
                final_key = nonce_key
                final_digest = nonce_digest
                final_ids = selected_ids
            for value in reversed(reached_indices):
                result += bt.push_number(value)
        pin_code = bt.find_and_delete(lock, pin)
        pin_key = recover(pin, tx.sighash(1, pin_code, 1))
        result += bt.push_data(ec.compress_pubkey(ec.G))
        result += bt.push_data(pin_key)
        return bytes(result), final_key, final_code, final_digest, final_ids

    sig_a, key_a, code_a, digest_a, ids_a = witness(10)
    sig_b, key_b, code_b, digest_b, ids_b = witness(11)
    sig_b_old, _, _, _, _ = witness(11, key_a)
    assert ids_a == list(range(9))
    assert ids_b == list(range(8)) + [9]
    assert code_a != code_b and digest_a != digest_b and key_a != key_b
    nonpush_prefix = b"\x51\x75"  # OP_1 OP_DROP; leaves the same stack.
    tx.inputs[1].script_sig = sig_a
    original_script_sig_digest = tx.sighash(1, code_a, 1)
    tx.inputs[1].script_sig = nonpush_prefix + sig_a
    prefixed_script_sig_digest = tx.sighash(1, code_a, 1)
    assert original_script_sig_digest == prefixed_script_sig_digest == digest_a
    tx.inputs[1].script_sig = b""

    def check(name: str, script_sig: bytes, expected: bool) -> dict:
        tx.inputs[1].script_sig = script_sig
        raw = tx.serialize()
        payload = f"{raw.hex()}\n2\n1000\n51\n100000\n{lock.hex()}\n"
        run = subprocess.run([
            "docker", "run", "--rm", "--network", "none", "--read-only",
            "--cap-drop=ALL", "--security-opt=no-new-privileges",
            "--platform=linux/arm64", "-i", "-v", f"{native}:/native:ro",
            IMAGE, "/native/qsb-consensus"],
            input=payload, text=True, capture_output=True, timeout=60)
        if run.returncode not in (0, 1):
            raise RuntimeError(f"{name}: Core adapter error: {run.stderr}")
        accepted = (run.returncode == 0 and
                    run.stdout.strip() == "core-27.2-api2-all-inputs-valid")
        assert accepted == expected, (name, run)
        return {"case": name, "accepted": accepted,
                "transaction_sha256": hashlib.sha256(raw).hexdigest()}

    cases = [check("subset_a_recovered", sig_a, True),
             check("subset_a_nonpush_prefix_same_keys",
                   nonpush_prefix + sig_a, True),
             check("subset_b_recovered", sig_b, True),
             check("subset_b_old_nonce_key", sig_b_old, False)]
    report = {
        "scope": "full 880-opcode Config A lock with three SHA256 puzzle CHECKSIGVERIFY sites replaced by OP_2DROP; pinning, HORS and both CHECKMULTISIGs active; synthetic unfunded transactions only",
        "source_revision": subprocess.check_output(
            ["git", "-C", str(app), "rev-parse", "HEAD"], text=True).strip(),
        "image": IMAGE,
        "native_files_sha256": native_hashes,
        "exact_lock_sha256": hashlib.sha256(exact).hexdigest(),
        "test_lock_sha256": hashlib.sha256(lock).hexdigest(),
        "selected_input": 1,
        "output_count": 2,
        "subset_a_dummy_ids": ids_a,
        "subset_b_dummy_ids": ids_b,
        "subset_a_script_code_sha256": hashlib.sha256(code_a).hexdigest(),
        "subset_b_script_code_sha256": hashlib.sha256(code_b).hexdigest(),
        "subset_a_all_digest_hex": f"{digest_a:064x}",
        "subset_b_all_digest_hex": f"{digest_b:064x}",
        "nonpush_prefix_hex": nonpush_prefix.hex(),
        "script_sig_only_all_digest_unchanged":
            original_script_sig_digest == prefixed_script_sig_digest,
        "cases": cases,
    }
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"cases": cases,
                      "all_digests_differ": digest_a != digest_b}, indent=2))


if __name__ == "__main__":
    main()
