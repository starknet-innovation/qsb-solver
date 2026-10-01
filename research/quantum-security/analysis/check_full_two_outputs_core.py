"""Probe disposable full-lock layouts against pinned Core 27.2.

Three hash-to-signature puzzle CHECKSIGVERIFY sites are changed to OP_2DROP.
Pinning, all 15 HORS comparisons, and both CHECKMULTISIGs remain real. All
secrets and signatures are disposable public test data; no transaction is
broadcast or funded. The original two-input wrapper and a test-only variable-
input adapter call the same pinned library. This is a finite consensus-
interpreter experiment, not an actual QSB spend or a universal refinement.
"""

import argparse
import hashlib
import json
import random
import struct
import subprocess
import sys
from pathlib import Path

from check_round_results import opcodes


PINNED_BUILDER_SHA256 = "c7e52af90bd0d9fce9834fce26dcd67aee0d7751ee228d9730873c4d12659a5c"
PINNED_HELPER_SHA256 = {
    "worker/cpu/secp256k1.py": "d2cebd1410b75cad606806cf02d7bee3e24724d5fcb7a53a07f598fcbc8afece",
    "worker/cpu/qsb_pipeline.py": "05334c08fa012a77ccba2887e05d78f90a8b81c0e34b786931b423f7f11255d8",
}
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
    helper_hashes = {
        name: hashlib.sha256((app_root / name).read_bytes()).hexdigest()
        for name in PINNED_HELPER_SHA256
    }
    assert helper_hashes == PINNED_HELPER_SHA256
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

    def transaction(two_outputs: bool, input_count: int = 2) -> bt.Transaction:
        assert input_count in (2, 3)
        tx = bt.Transaction(version=1, locktime=1234567)
        tx.add_input(bt.TxIn(b"\x11" * 32, 0, b"", 0xfffffffe))
        tx.add_input(bt.TxIn(b"\x22" * 32, 0, b"", 0x80000000))
        if input_count == 3:
            tx.add_input(bt.TxIn(b"\x44" * 32, 0, b"", 0xfffffffd))
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
    code1 = bt.find_and_delete(lock, nonces[1])
    for sig in builder.dummy_sigs[1][:9]:
        code1 = bt.find_and_delete(code1, sig)
    bug_digest = one_output.sighash(1, code0, selected0[-1])
    in_range_digest = two_outputs.sighash(1, code0, selected0[-1])
    assert bug_digest == 1 << 248
    assert in_range_digest != bug_digest

    def canonical_index(_round: int, _position: int, value: int) -> bytes:
        return bt.push_number(value)

    def four_byte_index(_round: int, _position: int, value: int) -> bytes:
        # Four-byte positive ScriptNum, deliberately nonminimal for these
        # small values. This tests operand parsing through the full lock.
        assert 0 <= value < 1 << 24
        return bt.push_data(value.to_bytes(4, "little"))

    def pushdata1_index(round_index: int, position: int, value: int) -> bytes:
        direct = four_byte_index(round_index, position, value)
        assert direct[0] == 4
        return b"\x4c\x04" + direct[1:]

    def one_oversize_index(round_index: int, position: int, value: int) -> bytes:
        if round_index == 0 and position == 0:
            return bt.push_data(value.to_bytes(5, "little"))
        return canonical_index(round_index, position, value)

    def witness(tx: bt.Transaction, dummy_context: bt.Transaction,
                index_encoder=canonical_index, spending_index: int = 1) -> bytes:
        script_sig = bytearray()
        for round_index in (1, 0):
            selected = [builder.dummy_sigs[round_index][j]
                        for j in subsets[round_index]]
            script_code = bt.find_and_delete(lock, nonces[round_index])
            for sig in selected:
                script_code = bt.find_and_delete(script_code, sig)
            nonce_key = recover(nonces[round_index],
                                tx.sighash(spending_index, script_code, 1))
            pubkeys = [recover(sig, dummy_context.sighash(
                spending_index, script_code, sig[-1])) for sig in selected]
            script_sig += bt.push_data(ec.compress_pubkey(ec.G))
            script_sig += bt.push_data(nonce_key)
            for key in reversed(pubkeys):
                script_sig += bt.push_data(key)
            for j in range((7 if round_index else 8) - 1, -1, -1):
                script_sig += bt.push_data(
                    builder.hors_secrets[round_index][subsets[round_index][j]])
            for position in range(len(indices[round_index]) - 1, -1, -1):
                value = indices[round_index][position]
                script_sig += index_encoder(round_index, position, value)
        pin_key = recover(pin, tx.sighash(
            spending_index, bt.find_and_delete(lock, pin), 1))
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

    variable_adapter = Path(__file__).with_name(
        "core_variable_inputs_adapter.py").resolve()
    variable_adapter_sha = hashlib.sha256(variable_adapter.read_bytes()).hexdigest()

    def variable_core_result(tx: bt.Transaction, spending_index: int,
                             raw_tx: bytes | None = None,
                             spent: list[dict] | None = None) -> dict:
        if spent is None:
            spent = [{"script_pubkey_hex": "51", "value": 1000}
                     for _ in tx.inputs]
            spent[spending_index] = {
                "script_pubkey_hex": lock.hex(), "value": 100000}
        payload = json.dumps({"transaction_hex": (raw_tx or tx.serialize()).hex(),
                              "spent_outputs": spent}) + "\n"
        process = subprocess.run([
            "docker", "run", "--rm", "--network", "none", "--read-only",
            "--cap-drop=ALL", "--security-opt=no-new-privileges",
            "--platform=linux/arm64", "-i",
            "-v", f"{native_root}:/native:ro",
            "-v", f"{variable_adapter}:/adapter.py:ro", args.image,
            "python3", "/adapter.py"], input=payload, text=True,
            capture_output=True, timeout=30)
        if process.returncode:
            raise RuntimeError(
                f"Pinned variable-input adapter failed: {process.stderr}")
        result = json.loads(process.stdout)
        assert result["api_version"] == 2
        assert result["flags"] == 134677
        assert len(result["inputs"]) == len(tx.inputs)
        return result

    cases = []

    def check(name: str, tx: bt.Transaction, expected: bool) -> None:
        accepted = core_accepts(tx)
        assert accepted == expected, (name, accepted, expected)
        cases.append({
            "name": name,
            "accepted": accepted,
            "expected": expected,
            "output_count": len(tx.outputs),
            "script_sig_length": len(tx.inputs[1].script_sig),
            "transaction_sha256": hashlib.sha256(tx.serialize()).hexdigest(),
        })

    def check_variable(name: str, tx: bt.Transaction,
                       spending_index: int, expected: bool,
                       raw_tx: bytes | None = None,
                       spent: list[dict] | None = None) -> None:
        result = variable_core_result(tx, spending_index, raw_tx, spent)
        accepted = all(item == {"valid": True, "error": 0}
                       for item in result["inputs"])
        assert accepted == expected, (name, result, expected)
        record = {
            "name": name,
            "accepted": accepted,
            "expected": expected,
            "input_count": len(tx.inputs),
            "spending_index": spending_index,
            "input_results": result["inputs"],
            "output_count": len(tx.outputs),
            "round0_single_message_scalar_hex":
                f"{tx.sighash(spending_index, code0, selected0[-1]):064x}",
            "round1_single_message_scalar_hex":
                f"{tx.sighash(spending_index, code1, builder.dummy_sigs[1][0][-1]):064x}",
            "script_sig_length": len(tx.inputs[spending_index].script_sig),
            "transaction_sha256": hashlib.sha256(
                raw_tx or tx.serialize()).hexdigest(),
        }
        if raw_tx is not None:
            record["transaction_encoding"] = "segwit_marker_flag_and_witness"
        cases.append(record)

    def serialize_segwit(tx: bt.Transaction,
                         witnesses: list[list[bytes]]) -> bytes:
        assert len(witnesses) == len(tx.inputs)
        return (
            struct.pack("<I", tx.version) + b"\x00\x01" +
            bt.serialize_varint(len(tx.inputs)) +
            b"".join(inp.serialize() for inp in tx.inputs) +
            bt.serialize_varint(len(tx.outputs)) +
            b"".join(out.serialize() for out in tx.outputs) +
            b"".join(bt.serialize_varint(len(witness)) +
                     b"".join(bt.serialize_varint(len(item)) + item
                              for item in witness)
                     for witness in witnesses) +
            struct.pack("<I", tx.locktime))

    one_output.inputs[1].script_sig = witness(one_output, one_output)
    check("one_output_bug_digest", one_output, True)
    two_outputs.inputs[1].script_sig = witness(two_outputs, one_output)
    check("two_outputs_old_dummy_keys", two_outputs, False)
    two_outputs.inputs[1].script_sig = witness(two_outputs, two_outputs)
    check("two_outputs_recovered_keys", two_outputs, True)
    canonical_witness = two_outputs.inputs[1].script_sig
    assert len(indices[0]) == len(indices[1]) == 9
    two_outputs.inputs[1].script_sig = witness(
        two_outputs, two_outputs, four_byte_index)
    check("two_outputs_all_18_nonminimal_four_byte_indices", two_outputs, True)
    two_outputs.inputs[1].script_sig = witness(
        two_outputs, two_outputs, pushdata1_index)
    check("two_outputs_all_18_nonminimal_pushdata1_indices", two_outputs, True)
    two_outputs.inputs[1].script_sig = witness(
        two_outputs, two_outputs, one_oversize_index)
    check("two_outputs_first_index_five_bytes_rejected", two_outputs, False)
    # Empty pushes before the witness become bottom-stack cells. The modeled
    # canonical peak is 615, so 385 reaches the 1000-cell limit and 386
    # exceeds it. These are finite native differential cases, not a proof of
    # full Core-to-Lean trace equivalence.
    for extra_cells, expected in ((1, True), (64, True), (256, True),
                                  (385, True), (386, False)):
        two_outputs.inputs[1].script_sig = b"\x00" * extra_cells + canonical_witness
        check(f"two_outputs_{extra_cells}_bottom_empty_cells", two_outputs, expected)
    # The Lean frame theorem quantifies over byte values, not only empty cells.
    # Exercise that distinction at the same stack boundary with nonempty data.
    varied_cells = [
        hashlib.sha256(b"qsb-bottom-cell-" + i.to_bytes(2, "little")).digest()[:20]
        for i in range(386)
    ]
    for extra_cells, expected in ((385, True), (386, False)):
        prefix = b"".join(bt.push_data(cell) for cell in varied_cells[:extra_cells])
        two_outputs.inputs[1].script_sig = prefix + canonical_witness
        check(f"two_outputs_{extra_cells}_bottom_varied_20_byte_cells",
              two_outputs, expected)
    two_outputs.inputs[1].script_sig = (
        b"\x00" * 384 + bt.push_data(b"\x5a" * 520) + canonical_witness)
    check("two_outputs_385_bottom_cells_one_520_byte", two_outputs, True)
    # The lock's fixed roll depths address cells above these additional
    # bottom-stack values. A non-push scriptSig prefix is consensus-admitted
    # for this bare output, and a 520-byte push reaches the element limit.
    two_outputs.inputs[1].script_sig = b"\x51\x51\x93" + canonical_witness
    check("two_outputs_nonpush_bottom_prefix", two_outputs, True)
    two_outputs.inputs[1].script_sig = (
        bt.push_data(b"\x5a" * 520) + canonical_witness)
    check("two_outputs_max_element_bottom_prefix", two_outputs, True)
    two_outputs.inputs[1].script_sig = canonical_witness
    two_outputs.outputs[1] = bt.TxOut(1001, b"\x51")
    check("two_outputs_changed_second_value", two_outputs, False)
    two_outputs.outputs[1] = bt.TxOut(1000, b"\x51")
    two_outputs.outputs[0] = bt.TxOut(90001, b"\x00\x14" + b"\x33" * 20)
    # The SINGLE dummy checks keep the original two-output recovery keys.
    # The fixed ALL pin and nonce checks get keys for this changed transaction.
    two_outputs.inputs[1].script_sig = witness(two_outputs, transaction(True))
    check("two_outputs_changed_first_value_same_dummy_keys", two_outputs, True)

    # Cross-check the ctypes ABI against the original two-input wrapper before
    # using it for layouts that wrapper intentionally refuses to represent.
    baseline = transaction(True)
    baseline.inputs[1].script_sig = witness(baseline, baseline)
    assert core_accepts(baseline)
    check_variable("variable_adapter_two_input_positive_control",
                   baseline, 1, True)
    rejected = transaction(True)
    rejected.inputs[1].script_sig = witness(rejected, rejected)
    rejected.outputs[1] = bt.TxOut(1001, b"\x51")
    assert not core_accepts(rejected)
    check_variable("variable_adapter_two_input_negative_control",
                   rejected, 1, False)

    # Extra input after the QSB input leaves SINGLE in range. Moving the QSB
    # input to index 2 with only two outputs makes SINGLE use the fixed bug
    # digest again. Both cases keep the same complete puzzle-relaxed lock.
    three_index_one = transaction(True, input_count=3)
    three_index_one.inputs[1].script_sig = witness(
        three_index_one, three_index_one)
    assert three_index_one.sighash(1, code0, selected0[-1]) != bug_digest
    check_variable("three_inputs_qsb_index_one_single_in_range",
                   three_index_one, 1, True)

    three_index_two = transaction(True, input_count=3)
    three_index_two.inputs[2].script_sig = witness(
        three_index_two, three_index_two, spending_index=2)
    assert three_index_two.sighash(2, code0, selected0[-1]) == bug_digest
    assert three_index_two.sighash(
        2, code1, builder.dummy_sigs[1][0][-1]) == bug_digest
    check_variable("three_inputs_qsb_index_two_single_bug", three_index_two,
                   2, True)

    # A bare legacy QSB input can coexist with a SegWit-serialized companion
    # input. The QSB legacy sighash omits the witness envelope; the P2WSH
    # input's witness is nevertheless checked under VERIFY_ALL. This tests a
    # transaction-byte extraction case outside the app's legacy serializer.
    witness_script = b"\x75\x51"  # OP_DROP; OP_TRUE
    p2wsh = b"\x00\x20" + hashlib.sha256(witness_script).digest()
    for spending_index, tx in ((1, three_index_one), (2, three_index_two)):
        spent = [{"script_pubkey_hex": "51", "value": 1000}
                 for _ in tx.inputs]
        spent[0] = {"script_pubkey_hex": p2wsh.hex(), "value": 1000}
        spent[spending_index] = {
            "script_pubkey_hex": lock.hex(), "value": 100000}
        witnesses = [[b"a", witness_script]] + [[] for _ in tx.inputs[1:]]
        raw_tx = serialize_segwit(tx, witnesses)
        assert raw_tx != tx.serialize()
        check_variable(f"three_inputs_qsb_index_{spending_index}_mixed_p2wsh",
                       tx, spending_index, True, raw_tx, spent)
        if spending_index == 2:
            changed_witnesses = [[b"b", witness_script]] + [
                [] for _ in tx.inputs[1:]]
            check_variable(
                "three_inputs_qsb_index_two_changed_only_p2wsh_witness",
                tx, spending_index, True,
                serialize_segwit(tx, changed_witnesses), spent)
            bad_witnesses = [[b"a", b"\x00"]] + [
                [] for _ in tx.inputs[1:]]
            check_variable("three_inputs_qsb_index_two_bad_p2wsh_witness",
                           tx, spending_index, False,
                           serialize_segwit(tx, bad_witnesses), spent)

    original_three = transaction(True, input_count=3)
    three_index_two.outputs[0] = bt.TxOut(90001, b"\x00\x14" + b"\x33" * 20)
    three_index_two.outputs[1] = bt.TxOut(1001, b"\x51")
    check_variable("three_inputs_qsb_index_two_changed_outputs_old_all_keys_rejected",
                   three_index_two, 2, False)
    three_index_two.inputs[2].script_sig = witness(
        three_index_two, original_three, spending_index=2)
    assert three_index_two.sighash(2, code0, selected0[-1]) == bug_digest
    assert three_index_two.sighash(
        2, code1, builder.dummy_sigs[1][0][-1]) == bug_digest
    check_variable("three_inputs_qsb_index_two_changed_both_outputs_same_dummy_keys",
                   three_index_two, 2, True)

    report = {
        "scope": "Disposable full lock with three puzzle CHECKSIGVERIFY sites relaxed; 15 HORS comparisons, pinning and both CHECKMULTISIGs remain real. Original two-input cases use the pinned wrapper; new two-input controls and three-input cases use a cross-checked test-only adapter with the same pinned library. Input 1 with two outputs has in-range SINGLE; input 2 with two outputs uses the SINGLE bug digest. Mixed SegWit cases add a P2WSH companion input, a valid witness-only mutation, and a wrong-witness control. Not a full QSB spend or universal Core refinement.",
        "builder_sha256": source_sha,
        "helper_files_sha256": helper_hashes,
        "exact_lock_sha256": hashlib.sha256(exact).hexdigest(),
        "test_lock_sha256": hashlib.sha256(lock).hexdigest(),
        "native_files_sha256": native_hashes,
        "variable_adapter_sha256": variable_adapter_sha,
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
