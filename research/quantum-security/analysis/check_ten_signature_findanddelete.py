"""Probe Core's shared ten-signature FindAndDelete on disposable fixture pushes.

This is an isolated bare CHECKMULTISIG lock, not a full QSB spend. It places
the fixture's 151 possible signature pushes in a nonexecuted branch, so Core
must delete the ten reached signatures from one shared legacy scriptCode.
Both SINGLE and ALL checks use in-range, transaction-dependent sighashes.
Three controls switch one selected dummy while keeping the fixed nonce and
transaction fields. The final cases probe nonminimal count ScriptNums, count
bounds, and NULLDUMMY on the same isolated lock.
"""

import argparse
import hashlib
import json
import random
import subprocess
import sys
from pathlib import Path


def parse_sig(sig: bytes) -> tuple[int, int]:
    r_len = sig[3]
    r = int.from_bytes(sig[4:4 + r_len], "big")
    assert sig[4 + r_len] == 2
    s_len = sig[5 + r_len]
    s = int.from_bytes(sig[6 + r_len:6 + r_len + s_len], "big")
    assert 6 + r_len + s_len == len(sig) - 1
    return r, s


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--app-root", type=Path, required=True)
    parser.add_argument("--native-root", type=Path, required=True)
    parser.add_argument("--image", required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    app = args.app_root.resolve()
    native = args.native_root.resolve()
    sys.path.insert(0, str(app / "worker/cpu"))
    import bitcoin_tx as bt
    import secp256k1 as ec

    inventory = json.loads((root / "evidence/source-inventory.json").read_text())
    layout = json.loads((root / "evidence/byte-layout-map.json").read_text())
    pinned_core = json.loads((root / "evidence/find-and-delete-boundary.json").read_text())
    builder_hash = hashlib.sha256((app / "worker/cpu/bitcoin_tx.py").read_bytes()).hexdigest()
    ec_hash = hashlib.sha256((app / "worker/cpu/secp256k1.py").read_bytes()).hexdigest()
    assert builder_hash == inventory["app"]["files"]["worker/cpu/bitcoin_tx.py"]
    assert ec_hash == inventory["app"]["files"]["worker/cpu/secp256k1.py"]
    assert builder_hash == layout["builder_sha256"]
    wrapper_hash = hashlib.sha256((native / "qsb-consensus").read_bytes()).hexdigest()
    library_hash = hashlib.sha256((native / "libbitcoinconsensus.so.0").read_bytes()).hexdigest()
    assert wrapper_hash == pinned_core["native_executable_sha256"]
    assert library_hash == pinned_core["native_library_sha256"]
    # The original experiment image may be absent from a later Docker cache.
    # This explicit arm64 Ubuntu 22.04 image identity was used for the
    # subset-switch rerun with the same hash-pinned Core binary and library.
    assert args.image in (
        pinned_core["image"],
        "ubuntu@sha256:b1066385161d28ddf6bc7e7b28a9170eec11484c821d1a5150d176cbde41d7f7",
    )

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

    pin, first_nonce, final_nonce = (nonce_sig(x) for x in
                                     (b"qsb_pin", b"qsb_r0", b"qsb_r1"))
    fixture_lock = builder.build_full_script(pin, first_nonce, final_nonce)
    assert hashlib.sha256(fixture_lock).hexdigest() == layout["script_sha256"]

    all_sigs = builder.dummy_sigs[1] + [final_nonce]
    chosen_ids = [0, 1, 17, 23, 41, 77, 96, 111, 149]
    chosen = [all_sigs[i] for i in chosen_ids] + [final_nonce]
    assert len(set(chosen)) == 10
    assert all(sig[-1] == 3 for sig in chosen[:-1])
    assert chosen[-1][-1] == 1

    # Push opcodes in a false branch are parsed and participate in
    # FindAndDelete, but their stack effects are skipped.
    lock = b"\x00\x63" + b"".join(bt.push_data(sig) for sig in all_sigs) + b"\x68\xae"
    code = lock
    for sig in reversed(chosen):  # Core scans from the top stack item.
        code = bt.find_and_delete(code, sig)
    selected = set(chosen)
    expected = b"\x00\x63" + b"".join(
        bt.push_data(sig) for sig in all_sigs if sig not in selected) + b"\x68\xae"
    assert code == expected
    assert len(lock) <= 10000

    tx = bt.Transaction(version=1, locktime=0)
    tx.add_input(bt.TxIn(b"\x44" * 32, 0, b"", 0xFFFFFFFE))
    tx.add_input(bt.TxIn(b"\x55" * 32, 0, b"", 0xFFFFFFFE))
    tx.add_output(bt.TxOut(90000, b"\x51"))
    tx.add_output(bt.TxOut(90000, b"\x51"))

    def recovered_key(sig: bytes, script_code: bytes) -> bytes:
        r, s = parse_sig(sig)
        z = tx.sighash(1, script_code, sig[-1])
        for recovery_flag in (0, 1):
            point = ec.ecdsa_recover(r, s, z, recovery_flag)
            if point is not None and ec.ecdsa_verify(point, z, r, s):
                return ec.compress_pubkey(point)
        raise AssertionError("No recovery point for disposable signature")

    keys = [recovered_key(sig, code) for sig in chosen]
    wrong_all = recovered_key(final_nonce, lock)
    wrong_single = recovered_key(chosen[0], lock)
    assert wrong_all != keys[-1]
    assert wrong_single != keys[0]

    def check(label: str, key_list: list[bytes],
              sig_list: list[bytes] | None = None,
              lock_bytes: bytes | None = None,
              key_count_cell: bytes | None = None,
              sig_count_cell: bytes | None = None,
              dummy: bytes = b"") -> dict:
        sig_list = chosen if sig_list is None else sig_list
        lock_bytes = lock if lock_bytes is None else lock_bytes
        script_sig = (bt.push_data(dummy) +
                      b"".join(bt.push_data(sig) for sig in sig_list) +
                      (bt.push_number(10) if sig_count_cell is None else
                       bt.push_data(sig_count_cell)) +
                      b"".join(bt.push_data(key) for key in key_list) +
                      (bt.push_number(10) if key_count_cell is None else
                       bt.push_data(key_count_cell)))
        tx.inputs[1].script_sig = script_sig
        raw = tx.serialize()
        payload = f"{raw.hex()}\n2\n1000\n51\n100000\n{lock_bytes.hex()}\n"
        run = subprocess.run([
            "docker", "run", "--rm", "--network", "none", "--read-only",
            "--cap-drop=ALL", "--security-opt=no-new-privileges",
            "--platform=linux/arm64", "-i", "-v", f"{native}:/native:ro",
            args.image, "/native/qsb-consensus"],
            input=payload, text=True, capture_output=True, timeout=60)
        if run.returncode not in (0, 1):
            raise RuntimeError(f"{label}: Core adapter error: {run.stderr}")
        accepted = (run.returncode == 0 and
                    run.stdout.strip() == "core-27.2-api2-all-inputs-valid")
        return {"case": label, "accepted": accepted,
                "lock_sha256": hashlib.sha256(lock_bytes).hexdigest(),
                "transaction_sha256": hashlib.sha256(raw).hexdigest()}

    wrong_all_keys = keys.copy()
    wrong_all_keys[-1] = wrong_all
    wrong_single_keys = keys.copy()
    wrong_single_keys[0] = wrong_single
    cases = [check("shared_code", keys),
             check("wrong_all_key", wrong_all_keys),
             check("wrong_in_range_single_key", wrong_single_keys)]
    for omitted in range(10):
        missing_one_code = lock
        for index in reversed(range(10)):
            if index != omitted:
                missing_one_code = bt.find_and_delete(missing_one_code, chosen[index])
        assert missing_one_code != code
        missing_one_keys = [recovered_key(sig, missing_one_code) for sig in chosen]
        assert missing_one_keys != keys
        cases.append(check(f"retain_selected_push_{omitted}", missing_one_keys))
    assert [case["accepted"] for case in cases] == [True] + [False] * 12, cases

    # Change one of nine selected generated dummies while retaining the same
    # lock, transaction fields, and fixed ALL nonce signature. The first nine
    # keys are recovered for the second selection in the negative control;
    # only the old nonce key is reused. This isolates the final ALL digest's
    # dependence on the reached FindAndDelete signature set.
    subset_a_ids = [0] + list(range(2, 10))
    subset_b_ids = [1] + list(range(2, 10))

    def subset_code(ids: list[int]) -> tuple[list[bytes], bytes]:
        signatures = [all_sigs[i] for i in ids] + [final_nonce]
        result = lock
        for signature in reversed(signatures):
            result = bt.find_and_delete(result, signature)
        return signatures, result

    subset_a, subset_a_code = subset_code(subset_a_ids)
    subset_b, subset_b_code = subset_code(subset_b_ids)
    assert len(subset_a) == len(subset_b) == 10
    assert subset_a_code != subset_b_code
    subset_a_digest = tx.sighash(1, subset_a_code, 1)
    subset_b_digest = tx.sighash(1, subset_b_code, 1)
    assert subset_a_digest != subset_b_digest
    subset_a_keys = [recovered_key(sig, subset_a_code) for sig in subset_a]
    subset_b_keys = [recovered_key(sig, subset_b_code) for sig in subset_b]
    assert subset_a_keys[-1] != subset_b_keys[-1]
    subset_b_old_nonce_keys = subset_b_keys.copy()
    subset_b_old_nonce_keys[-1] = subset_a_keys[-1]
    subset_cases = [
        check("subset_a_recovered", subset_a_keys, subset_a),
        check("subset_b_recovered", subset_b_keys, subset_b),
        check("subset_b_old_nonce_key", subset_b_old_nonce_keys, subset_b),
    ]
    assert [case["accepted"] for case in subset_cases] == [
        True, True, False], subset_cases
    cases.extend(subset_cases)

    # DROP; TRUE distinguishes a CHECKMULTISIG false result from an encoding
    # abort. The last pushed signature is the first one scanned by Core.
    lock_drop_true = lock + b"\x75\x51"
    empty_first = chosen.copy()
    empty_first[-1] = b""
    malformed_first = chosen.copy()
    malformed_first[-1] = b"\x31" + malformed_first[-1][1:]
    cases.extend((
        check("empty_first_drop_true", keys, empty_first, lock_drop_true),
        check("malformed_first_drop_true", keys, malformed_first,
              lock_drop_true),
    ))
    assert [case["accepted"] for case in cases[-2:]] == [True, False], cases

    # Core parses both source-addressed count cells with minimal-number
    # enforcement disabled, but enforces the count ranges and NULLDUMMY.
    structural_cases = [
        check("nonminimal_key_count_10", keys, key_count_cell=b"\x0a\x00"),
        check("nonminimal_sig_count_10", keys, sig_count_cell=b"\x0a\x00"),
        check("nonminimal_both_counts_10", keys,
              key_count_cell=b"\x0a\x00", sig_count_cell=b"\x0a\x00"),
        check("nonempty_dummy", keys, dummy=b"\x01"),
        check("negative_key_count", keys, key_count_cell=b"\x81"),
        check("too_many_keys_21", keys, key_count_cell=b"\x15"),
        check("more_signatures_than_keys_11", keys,
              sig_count_cell=b"\x0b"),
    ]
    assert [case["accepted"] for case in structural_cases] == [
        True, True, True, False, False, False, False], structural_cases
    cases.extend(structural_cases)

    report = {
        "scope": "isolated bare ten-signature CHECKMULTISIG with fixture pushes in a false branch, subset-switch controls, and two DROP; TRUE encoding-gate cases; not full QSB acceptance",
        "core_flags": "bitcoinconsensus_SCRIPT_FLAGS_VERIFY_ALL",
        "source_revision": subprocess.check_output(
            ["git", "-C", str(app), "rev-parse", "HEAD"], text=True).strip(),
        "builder_sha256": builder_hash,
        "secp256k1_sha256": ec_hash,
        "fixture_script_sha256": hashlib.sha256(fixture_lock).hexdigest(),
        "image": args.image,
        "native_executable_sha256": wrapper_hash,
        "native_library_sha256": library_hash,
        "selected_dummy_ids": chosen_ids,
        "lock_bytes": len(lock),
        "lock_sha256": hashlib.sha256(lock).hexdigest(),
        "parser_gate_lock_sha256": hashlib.sha256(lock_drop_true).hexdigest(),
        "shared_script_code_sha256": hashlib.sha256(code).hexdigest(),
        "both_sighash_types_in_range": True,
        "subset_switch": {
            "a_ids": subset_a_ids,
            "b_ids": subset_b_ids,
            "a_script_code_sha256": hashlib.sha256(subset_a_code).hexdigest(),
            "b_script_code_sha256": hashlib.sha256(subset_b_code).hexdigest(),
            "a_all_digest_hex": f"{subset_a_digest:064x}",
            "b_all_digest_hex": f"{subset_b_digest:064x}",
        },
        "cases": cases,
    }
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"lock_bytes": len(lock), "cases": cases}, indent=2))


if __name__ == "__main__":
    main()
