"""Check all four ECDSA recovery-point branches in pinned Core 27.2.

The signature, transaction and previous outputs are synthetic and unfunded.
The bare locking script is OP_CHECKSIG, not the QSB lock. This finite probe
tests accepted secp256k1 keys for x=r and x=r+n, not a QSB spend or a quantum
hash bound.
"""

import argparse
import hashlib
import json
import struct
import subprocess
import sys
from pathlib import Path


PINNED_SOURCE_SHA256 = {
    "worker/cpu/bitcoin_tx.py": "c7e52af90bd0d9fce9834fce26dcd67aee0d7751ee228d9730873c4d12659a5c",
    "worker/cpu/secp256k1.py": "d2cebd1410b75cad606806cf02d7bee3e24724d5fcb7a53a07f598fcbc8afece",
}
PINNED_NATIVE_SHA256 = {
    "qsb-consensus": "9497dcf47c464fc49cbf54f806707bd67f04981c789c352bafb3805fe5d6dfcd",
    "libbitcoinconsensus.so.0": "5d7874783dc4989357600b3f273a44627d8ca6ac037f63d851572ff64a756983",
}


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--app-root", type=Path, required=True)
    parser.add_argument("--native-root", type=Path, required=True)
    parser.add_argument("--image", required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    app = args.app_root.resolve()
    native = args.native_root.resolve()
    for name, expected in PINNED_SOURCE_SHA256.items():
        assert sha256((app / name).read_bytes()) == expected
    for name, expected in PINNED_NATIVE_SHA256.items():
        assert sha256((native / name).read_bytes()) == expected
    sys.path.insert(0, str(app / "worker/cpu"))
    import bitcoin_tx as bt
    import secp256k1 as ec

    r, s, hash_type = 2, 1, 1
    sig = ec.encode_der_sig(r, s, sighash=hash_type)
    assert len(sig) == 9 and ec.is_valid_der_sig(sig)
    lock = bytes([bt.OP_CHECKSIG])
    tx = bt.Transaction(version=2, locktime=1234567)
    tx.add_input(bt.TxIn(b"\x11" * 32, 0, b"", 0xfffffffe))
    tx.add_input(bt.TxIn(b"\x22" * 32, 1, b"", 0x80000000))
    tx.add_output(bt.TxOut(90000, b"\x51"))
    tx.add_output(bt.TxOut(1000, b"\x51"))
    digest = tx.sighash(1, lock, hash_type)
    prepared = bt.Transaction(version=tx.version, locktime=tx.locktime)
    prepared.add_input(bt.TxIn(tx.inputs[0].txid, tx.inputs[0].vout,
                               b"", tx.inputs[0].sequence))
    prepared.add_input(bt.TxIn(tx.inputs[1].txid, tx.inputs[1].vout,
                               lock, tx.inputs[1].sequence))
    for out in tx.outputs:
        prepared.add_output(out)
    preimage = prepared.serialize() + struct.pack("<I", hash_type)
    assert int.from_bytes(bt.sha256d(preimage), "big") == digest

    def core_accepts(key: bytes) -> tuple[bool, str]:
        tx.inputs[1].script_sig = bt.push_data(sig) + bt.push_data(key)
        raw = tx.serialize()
        payload = f"{raw.hex()}\n2\n1000\n51\n100000\n{lock.hex()}\n"
        run = subprocess.run([
            "docker", "run", "--rm", "--network", "none", "--read-only",
            "--cap-drop=ALL", "--security-opt=no-new-privileges",
            "--platform=linux/arm64", "-i", "-v", f"{native}:/native:ro",
            args.image, "/native/qsb-consensus",
        ], input=payload, text=True, capture_output=True, timeout=30)
        if run.returncode not in (0, 1):
            raise RuntimeError(run.stderr)
        accepted = (run.returncode == 0 and
                    run.stdout.strip() == "core-27.2-api2-all-inputs-valid")
        return accepted, sha256(raw)

    r_inverse = ec.modinv(r, ec.N)
    cases = []
    keys = set()
    for branch, x in (("r", r), ("r_plus_n", r + ec.N)):
        assert x < ec.P
        rhs = (pow(x, 3, ec.P) + ec.B) % ec.P
        y = pow(rhs, (ec.P + 1) // 4, ec.P)
        assert pow(y, 2, ec.P) == rhs
        for parity in (0, 1):
            point = (x, y if y % 2 == parity else ec.P - y)
            key_point = ec.point_add(
                ec.point_mul((-digest * r_inverse) % ec.N, ec.G),
                ec.point_mul((s * r_inverse) % ec.N, point),
            )
            assert key_point != ec.INF
            assert ec.ecdsa_verify(key_point, digest, r, s)
            key = ec.compress_pubkey(key_point)
            assert key not in keys
            keys.add(key)
            accepted, tx_hash = core_accepts(key)
            assert accepted, (branch, parity)
            cases.append({
                "recovery_branch": branch,
                "recovery_x_hex": f"{x:064x}",
                "recovery_y_hex": f"{point[1]:064x}",
                "recovery_y_parity": parity,
                "public_key_hex": key.hex(),
                "core_accepted": accepted,
                "transaction_sha256": tx_hash,
            })
    assert len(keys) == 4
    helper_keys = {ec.compress_pubkey(point)
                   for parity in (0, 1)
                   if (point := ec.ecdsa_recover(r, s, digest, parity))}
    assert helper_keys == {bytes.fromhex(case["public_key_hex"])
                           for case in cases if case["recovery_branch"] == "r"}
    assert all(bytes.fromhex(case["public_key_hex"]) not in helper_keys
               for case in cases if case["recovery_branch"] == "r_plus_n")
    wrong_key = ec.compress_pubkey(ec.G)
    assert wrong_key not in keys
    assert not ec.ecdsa_verify(ec.G, digest, r, s)
    wrong_accepted, wrong_tx_hash = core_accepts(wrong_key)
    assert not wrong_accepted

    report = {
        "scope": "Unfunded two-input bare OP_CHECKSIG experiment; four Core-accepted keys for one 9-byte DER signature and one SHA256d transaction message. Not a QSB lock spend or quantum bound.",
        "source_files_sha256": PINNED_SOURCE_SHA256,
        "native_files_sha256": PINNED_NATIVE_SHA256,
        "image": args.image,
        "signature_hex": sig.hex(),
        "sighash_preimage_hex": preimage.hex(),
        "digest_hex": f"{digest:064x}",
        "app_helper_recovers_x_equals_r_only": True,
        "cases": cases,
        "wrong_key_hex": wrong_key.hex(),
        "wrong_key_core_accepted": wrong_accepted,
        "wrong_key_transaction_sha256": wrong_tx_hash,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"accepted_recovery_keys": len(cases),
                      "wrong_key_accepted": wrong_accepted}, indent=2))


if __name__ == "__main__":
    main()
