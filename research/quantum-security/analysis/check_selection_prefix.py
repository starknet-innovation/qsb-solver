"""Core check of first-selection local reachability on TRUNCATED test locks.

Only the pinning signature check is real; the first puzzle CHECKSIGVERIFY is
replaced by OP_2DROP. The locks end at selected instructions spanning the
first signed-pool comparison and next numeric parse. This is NOT full-lock
acceptance or unauthorized spending.
"""
import argparse
import hashlib
import json
import random
import subprocess
import sys
from pathlib import Path

from check_round_results import opcodes


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--app-root", type=Path, required=True)
    parser.add_argument("--native-root", type=Path, required=True)
    parser.add_argument("--image", required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    sys.path.insert(0, str(args.app_root / "worker/cpu"))
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

    def nonce_sig(label):
        k = int.from_bytes(hashlib.sha256(label + b"_nonce").digest(), "big") % ec.N
        r = ec.point_mul(k, ec.G)[0] % ec.N
        s = max(1, int.from_bytes(hashlib.sha256(label + b"_s").digest()[:16], "big") % (ec.N // 2))
        return ec.encode_der_sig(r, s, sighash=1)

    pin = nonce_sig(b"qsb_pin")
    exact_lock = builder.build_full_script(
        pin, nonce_sig(b"qsb_r0"), nonce_sig(b"qsb_r1"))
    layout = json.loads((Path(__file__).resolve().parents[1] /
                         "evidence/layout-map.json").read_text())
    source_hash = hashlib.sha256(
        (args.app_root / "worker/cpu/bitcoin_tx.py").read_bytes()).hexdigest()
    assert source_hash == layout["builder_sha256"]
    assert hashlib.sha256(exact_lock).hexdigest() == layout["script_sha256"]
    instructions = list(opcodes(exact_lock))
    assert instructions[315] == (4783, bt.OP_ROLL)
    roll_prefix_len = instructions[316][0]
    comparison_prefix_len = instructions[320][0]
    second_roll_prefix_len = instructions[323][0]
    before_min_prefix_len = instructions[324][0]
    second_min_prefix_len = instructions[325][0]
    assert (roll_prefix_len, comparison_prefix_len) == (4784, 4790)
    assert instructions[322][1] == bt.OP_ROLL
    assert instructions[324][1] == bt.OP_MIN

    def test_lock(prefix_len):
        # The first puzzle check is intentionally relaxed. Pinning remains real.
        lock = bytearray(exact_lock[:prefix_len])
        checks = [pos for pos, op in opcodes(lock) if op == bt.OP_CHECKSIGVERIFY]
        assert checks == [58, 61]
        lock[61] = 0x6d  # OP_2DROP
        return bytes(lock)

    tx = bt.Transaction(version=1, locktime=1234567)
    tx.add_input(bt.TxIn(b"\x11" * 32, 0, b"", 0xfffffffe))
    tx.add_input(bt.TxIn(b"\x22" * 32, 0, b"", 0x80000000))
    tx.add_output(bt.TxOut(90000, b"\x00\x14" + b"\x33" * 20))
    def pin_key_for(lock):
        r, s = parse_der(pin)
        z = tx.sighash(1, bt.find_and_delete(lock, pin), 1)
        for x in (r, r + ec.N):
            if x >= ec.P:
                continue
            for parity in (0, 1):
                point = ec.ecdsa_recover(x, s, z, parity)
                if point and ec.ecdsa_verify(point, z, r, s):
                    return ec.compress_pubkey(point)
        raise AssertionError("test signature has no recovered pinning key")

    indices = builder.compute_witness_indices({0: list(range(9)), 1: list(range(9))})

    def witness(marker, pin_key, first_index):
        cells = []  # Bottom-to-top, using arbitrary disposable round material.
        for ri in (1, 0):
            cells += [b"\x51", b"\x52"]  # Puzzle and nonce keys, unused by the prefix.
            cells += [b"\x53"] * 9       # Dummy verification keys, unused.
            cells += [b"\x54"] * (7 if ri else 8)  # HORS openings, unused.
            iv = list(indices[ri])
            if ri == 0:
                iv[0] = first_index
            for j in range(8, -1, -1):
                cells.append(iv[j])
                if ri == 0 and j == 1:
                    cells.append(marker)  # Immediately below the first index.
        data = bytearray()
        for cell in cells:
            data += bt.push_number(cell) if isinstance(cell, int) else bt.push_data(cell)
        data += bt.push_data(b"\x55") + bt.push_data(pin_key)
        return bytes(data)

    results = []
    for name, prefix_len, marker, first_index, expected in (
        ("roll_nonzero_external_marker", roll_prefix_len, b"\xa5" * 20, 152, True),
        ("roll_zero_external_marker", roll_prefix_len, b"\x00" * 20, 152, False),
        ("comparison_self_chosen_commitment", comparison_prefix_len,
         ec.hash160(b"\x0a"), 152, True),
        ("comparison_wrong_commitment", comparison_prefix_len,
         b"\x00" * 20, 152, False),
        ("second_index_roll_reaches_commitment", second_roll_prefix_len,
         ec.hash160(b"\x0a"), 152, True),
        ("before_second_index_min", before_min_prefix_len,
         ec.hash160(b"\x0a"), 152, True),
        ("second_index_min_rejects", second_min_prefix_len,
         ec.hash160(b"\x0a"), 152, False),
        ("nonminimal_index_before_second_min", before_min_prefix_len,
         ec.hash160(b"\x0a"), b"\x98\x00\x00", True),
        ("nonminimal_index_second_min_rejects", second_min_prefix_len,
         ec.hash160(b"\x0a"), b"\x98\x00\x00", False),
        ("large_index_before_second_min", before_min_prefix_len,
         ec.hash160(b"\x0a"), b"\xff\xff\xff\x7f", True),
        ("large_index_second_min_rejects", second_min_prefix_len,
         ec.hash160(b"\x0a"), b"\xff\xff\xff\x7f", False),
    ):
        lock = test_lock(prefix_len)
        tx.inputs[1].script_sig = witness(marker, pin_key_for(lock), first_index)
        payload = f"{tx.serialize().hex()}\n2\n1000\n51\n100000\n{lock.hex()}\n"
        result = subprocess.run([
            "docker", "run", "--rm", "--network", "none", "--read-only",
            "--cap-drop=ALL", "--security-opt=no-new-privileges", "--platform=linux/arm64",
            "-i", "-v", f"{args.native_root.resolve()}:/native:ro",
            args.image, "/native/qsb-consensus"], input=payload, text=True,
            capture_output=True, timeout=30)
        if result.returncode not in (0, 1):
            raise RuntimeError(f"native verifier unavailable: {result.returncode}: {result.stderr}")
        accepted = result.returncode == 0 and result.stdout.strip() == "core-27.2-api2-all-inputs-valid"
        assert accepted == expected, (name, result)
        results.append({"name": name, "prefix_bytes": prefix_len,
                        "first_index": first_index if isinstance(first_index, int)
                        else first_index.hex(),
                        "test_lock_sha256": hashlib.sha256(lock).hexdigest(),
                        "accepted": accepted, "expected": expected,
                        "transaction_sha256": hashlib.sha256(tx.serialize()).hexdigest()})

    report = {
        "scope": "TRUNCATED first-selection test lock with one puzzle check relaxed; not full-lock acceptance",
        "source_revision": subprocess.check_output(
            ["git", "-C", str(args.app_root), "rev-parse", "HEAD"], text=True).strip(),
        "exact_lock_sha256": hashlib.sha256(exact_lock).hexdigest(),
        "roll_prefix_bytes": roll_prefix_len,
        "comparison_prefix_bytes": comparison_prefix_len,
        "second_roll_prefix_bytes": second_roll_prefix_len,
        "before_min_prefix_bytes": before_min_prefix_len,
        "second_min_prefix_bytes": second_min_prefix_len,
        "first_selection_roll_offset": 4783,
        "native_files_sha256": {p.name: hashlib.sha256(p.read_bytes()).hexdigest()
                                for p in args.native_root.iterdir() if p.is_file()},
        "image": args.image,
        "cases": results,
    }
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"scope": report["scope"], "cases": results}, indent=2))


if __name__ == "__main__":
    main()
