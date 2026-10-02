"""Test a reused first-round puzzle signature in a disposable Config A lock.

The pin and final puzzle CHECKSIGVERIFY opcodes are replaced by OP_2DROP.
The first-round OP_DUP; OP_SHA256 pair becomes OP_NOP; <fixed DER signature>.
The first puzzle CHECKSIGVERIFY remains real, while its hash search is bypassed.
The old first-round nonce key stays a valid SEC key but fails its ALL signature
on the changed transaction; that false multisignature result is discarded.
This is not a spend of the unmodified lock or an attack-complexity measurement.
"""

import argparse
import hashlib
import json
import random
import subprocess
import sys
import tarfile
from pathlib import Path

from check_full_two_outputs_core import (
    PINNED_BUILDER_SHA256,
    PINNED_HELPER_SHA256,
    PINNED_MACOS_ARCHIVE_SHA256,
    PINNED_MACOS_ORIGINAL_LIBRARY_SHA256,
    PINNED_MACOS_RESIGNED_LIBRARY_SHA256,
)
from check_round_results import opcodes


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--app-root", type=Path, required=True)
    parser.add_argument("--consensus-library", type=Path, required=True)
    parser.add_argument("--core-archive", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    app = args.app_root.resolve()
    library = args.consensus_library.resolve()
    archive_path = args.core_archive.resolve()
    assert hashlib.sha256((app / "worker/cpu/bitcoin_tx.py").read_bytes()).hexdigest() == PINNED_BUILDER_SHA256
    for name, expected in PINNED_HELPER_SHA256.items():
        assert hashlib.sha256((app / name).read_bytes()).hexdigest() == expected
    assert hashlib.sha256(archive_path.read_bytes()).hexdigest() == PINNED_MACOS_ARCHIVE_SHA256
    with tarfile.open(archive_path, "r:gz") as archive:
        original = archive.extractfile("bitcoin-27.2/lib/libbitcoinconsensus.0.dylib")
        assert original is not None
        assert hashlib.sha256(original.read()).hexdigest() == PINNED_MACOS_ORIGINAL_LIBRARY_SHA256
    assert hashlib.sha256(library.read_bytes()).hexdigest() == PINNED_MACOS_RESIGNED_LIBRARY_SHA256

    sys.path.insert(0, str(app / "worker/cpu"))
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
        s = max(1, int.from_bytes(hashlib.sha256(label + b"_s").digest()[:16], "big") % (ec.N // 2))
        return ec.encode_der_sig(r, s, sighash=1)

    def recover(sig: bytes, z: int) -> bytes:
        r, s = parse_der(sig)
        for x in (r, r + ec.N):
            if x >= ec.P:
                continue
            for parity in (0, 1):
                point = ec.ecdsa_recover(x, s, z, parity)
                if point and ec.ecdsa_verify(point, z, r, s):
                    return ec.compress_pubkey(point)
        raise AssertionError("no disposable recovered key")

    pin = nonce_sig(b"qsb_pin")
    nonces = [nonce_sig(b"qsb_r0"), nonce_sig(b"qsb_r1")]
    exact = builder.build_full_script(pin, *nonces)
    assert hashlib.sha256(exact).hexdigest() == "44f34e665e756e239aed514a530c136f582a0812437c4f32140a1ebe83628bba"
    sites = [i for i, op in opcodes(exact) if op == bt.OP_CHECKSIGVERIFY]
    assert len(sites) == 4
    before_first_check = [(i, op) for i, op in opcodes(exact) if i < sites[2]]
    first_hash = before_first_check[-3][0]
    first_dup = before_first_check[-4][0]
    assert exact[first_hash] == bt.OP_SHA256_OP
    assert exact[first_dup] == bt.OP_DUP
    puzzle_sig = ec.encode_der_sig(2, 1 << 184, sighash=1)
    assert len(puzzle_sig) == 32 and parse_der(puzzle_sig) == (2, 1 << 184)
    lock_bytes = bytearray(exact)
    lock_bytes[sites[1]] = 0x6d  # Relax pin puzzle, retaining fixed pin ALL check.
    lock_bytes[sites[3]] = 0x6d  # Relax final puzzle, retaining final multisig.
    lock_bytes[first_dup] = 0x61  # OP_NOP in place of OP_DUP.
    lock = bytes(lock_bytes[:first_hash] + b"\x20" + puzzle_sig + lock_bytes[first_hash + 1:])
    assert len(lock) == len(exact) + 32 and len(lock) <= 10000
    assert len([op for _, op in opcodes(lock) if op == bt.OP_CHECKSIGVERIFY]) == 2
    modified_ops = builder.count_opcodes_runtime(lock)[0]
    assert modified_ops <= 201
    subsets = {0: [3, 17, 42, 66, 88, 101, 119, 140, 9],
               1: [5, 20, 55, 70, 90, 110, 130, 15, 45]}
    indices = builder.compute_witness_indices(subsets)

    def transaction(destination: int) -> bt.Transaction:
        tx = bt.Transaction(version=1, locktime=1234567)
        tx.add_input(bt.TxIn(b"\x11" * 32, 0, b"", 0xfffffffe))
        tx.add_input(bt.TxIn(b"\x22" * 32, 0, b"", 0x80000000))
        tx.add_output(bt.TxOut(90000, b"\x00\x14" + bytes([destination]) * 20))
        tx.add_output(bt.TxOut(1000, b"\x51"))
        return tx

    original_tx = transaction(0x33)
    changed_tx = transaction(0x77)
    puzzle_code = bt.find_and_delete(lock, puzzle_sig)
    first_nonce_code = bt.find_and_delete(lock, nonces[0])
    for sig in [builder.dummy_sigs[0][j] for j in subsets[0]]:
        first_nonce_code = bt.find_and_delete(first_nonce_code, sig)
    old_nonce_key = recover(nonces[0], original_tx.sighash(1, first_nonce_code, 1))
    old_nonce_verifies_new = ec.ecdsa_verify(
        ec.decompress_pubkey(old_nonce_key),
        changed_tx.sighash(1, first_nonce_code, 1), *parse_der(nonces[0]))
    assert not old_nonce_verifies_new
    old_puzzle_key = recover(puzzle_sig, original_tx.sighash(1, puzzle_code, 1))
    new_puzzle_key = recover(puzzle_sig, changed_tx.sighash(1, puzzle_code, 1))
    assert old_puzzle_key != new_puzzle_key
    old_puzzle_verifies_new = ec.ecdsa_verify(
        ec.decompress_pubkey(old_puzzle_key),
        changed_tx.sighash(1, puzzle_code, 1), *parse_der(puzzle_sig))
    assert not old_puzzle_verifies_new

    def witness(tx: bt.Transaction, first_puzzle_key: bytes,
                bad_final_nonce: bool = False) -> bytes:
        script_sig = bytearray()
        for ri in (1, 0):
            selected = [builder.dummy_sigs[ri][j] for j in subsets[ri]]
            code = bt.find_and_delete(lock, nonces[ri])
            for sig in selected:
                code = bt.find_and_delete(code, sig)
            z_all = tx.sighash(1, code, 1)
            nonce_key = old_nonce_key if ri == 0 else recover(nonces[ri], z_all)
            if ri == 1 and bad_final_nonce:
                nonce_key = recover(nonces[ri], original_tx.sighash(1, code, 1))
            z_single = tx.sighash(1, code, 3)
            pubs = [recover(sig, z_single) for sig in selected]
            script_sig += bt.push_data(first_puzzle_key if ri == 0 else ec.compress_pubkey(ec.G))
            script_sig += bt.push_data(nonce_key)
            for pub in reversed(pubs):
                script_sig += bt.push_data(pub)
            for j in range((7 if ri == 1 else 8) - 1, -1, -1):
                script_sig += bt.push_data(builder.hors_secrets[ri][subsets[ri][j]])
            for iv in reversed(indices[ri]):
                script_sig += bt.push_number(iv)
        pin_key = recover(pin, tx.sighash(1, bt.find_and_delete(lock, pin), 1))
        script_sig += bt.push_data(ec.compress_pubkey(ec.G)) + bt.push_data(pin_key)
        return bytes(script_sig)

    adapter = Path(__file__).with_name("core_variable_inputs_adapter.py")

    def run_case(name: str, tx: bt.Transaction, puzzle_key: bytes,
                 expected: bool, bad_final_nonce: bool = False) -> dict:
        tx.inputs[1].script_sig = witness(tx, puzzle_key, bad_final_nonce)
        request = {"transaction_hex": tx.serialize().hex(),
                   "spent_outputs": [
                       {"script_pubkey_hex": "51", "value": 1000},
                       {"script_pubkey_hex": lock.hex(), "value": 100000}]}
        result = subprocess.run([sys.executable, str(adapter), "--library", str(library)],
                                input=json.dumps(request), text=True, capture_output=True,
                                check=True, timeout=30)
        core = json.loads(result.stdout)
        accepted = all(item["valid"] for item in core["inputs"])
        assert accepted == expected, (name, core)
        return {"name": name, "accepted": accepted, "expected": expected,
                "core": core, "transaction_sha256": hashlib.sha256(tx.serialize()).hexdigest()}

    cases = [
        run_case("original_first_puzzle", original_tx, old_puzzle_key, True),
        run_case("changed_recovered_puzzle_key", changed_tx, new_puzzle_key, True),
        run_case("changed_stale_puzzle_key", changed_tx, old_puzzle_key, False),
        run_case("changed_stale_final_nonce_key", changed_tx, new_puzzle_key, False, True),
    ]
    report = {
        "scope": "MODIFIED lock: pin/final puzzles relaxed, first DUP/SHA256 replaced by NOP/fixed DER push; first puzzle CHECKSIGVERIFY and both multisignatures active; not an unmodified-lock spend",
        "app_builder_sha256": PINNED_BUILDER_SHA256,
        "core_archive_sha256": PINNED_MACOS_ARCHIVE_SHA256,
        "original_core_library_sha256": PINNED_MACOS_ORIGINAL_LIBRARY_SHA256,
        "loaded_core_library_sha256": PINNED_MACOS_RESIGNED_LIBRARY_SHA256,
        "adapter_sha256": hashlib.sha256(adapter.read_bytes()).hexdigest(),
        "exact_lock_sha256": hashlib.sha256(exact).hexdigest(),
        "modified_lock_sha256": hashlib.sha256(lock).hexdigest(),
        "exact_lock_bytes": len(exact),
        "modified_lock_bytes": len(lock),
        "modified_lock_runtime_ops": modified_ops,
        "first_hash_opcode_offset": first_hash,
        "first_dup_opcode_offset": first_dup,
        "original_checksigverify_offsets": sites,
        "modified_checksigverify_offsets": [i for i, op in opcodes(lock)
                                          if op == bt.OP_CHECKSIGVERIFY],
        "first_puzzle_signature_hex": puzzle_sig.hex(),
        "reused_first_nonce_key_hex": old_nonce_key.hex(),
        "first_puzzle_key_old_hex": old_puzzle_key.hex(),
        "first_puzzle_key_new_hex": new_puzzle_key.hex(),
        "old_puzzle_key_verifies_new_digest": old_puzzle_verifies_new,
        "old_nonce_key_verifies_new_digest": old_nonce_verifies_new,
        "cases": cases,
    }
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"scope": report["scope"], "cases": [
        {"name": case["name"], "accepted": case["accepted"]} for case in cases]}, indent=2))


if __name__ == "__main__":
    main()
