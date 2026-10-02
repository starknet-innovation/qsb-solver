"""Probe the scriptSig-to-bare-lock boundary in pinned Bitcoin Core 27.2.

Synthetic two-input transactions only. The second input uses an isolated
CHECKSIG lock, not the QSB locking script. This checks finite behavior of
the pinned consensus library and does not prove Core-to-Lean refinement.
"""

import argparse
import hashlib
import json
import subprocess
import sys
import tarfile
from pathlib import Path

from check_full_two_outputs_core import (
    PINNED_BUILDER_SHA256,
    PINNED_MACOS_ARCHIVE_SHA256,
    PINNED_MACOS_ORIGINAL_LIBRARY_SHA256,
    PINNED_MACOS_RESIGNED_LIBRARY_SHA256,
)


def sha256_file(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


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
    assert sha256_file(app / "worker/cpu/bitcoin_tx.py") == PINNED_BUILDER_SHA256
    helper = "worker/cpu/secp256k1.py"
    inventory = json.loads((Path(__file__).resolve().parents[1] /
                            "evidence/source-inventory.json").read_text())
    helper_hash = inventory["app"]["files"][helper]
    assert sha256_file(app / helper) == helper_hash
    assert sha256_file(archive_path) == PINNED_MACOS_ARCHIVE_SHA256
    with tarfile.open(archive_path, "r:gz") as archive:
        original = archive.extractfile(
            "bitcoin-27.2/lib/libbitcoinconsensus.0.dylib")
        assert original is not None
        assert hashlib.sha256(original.read()).hexdigest() == (
            PINNED_MACOS_ORIGINAL_LIBRARY_SHA256
        )
    assert sha256_file(library) == PINNED_MACOS_RESIGNED_LIBRARY_SHA256

    sys.path.insert(0, str(app / "worker/cpu"))
    import bitcoin_tx as bt
    import secp256k1 as ec

    tx = bt.Transaction(version=1, locktime=1234567)
    tx.add_input(bt.TxIn(b"\x44" * 32, 0, b"", 0xFFFFFFFE))
    tx.add_input(bt.TxIn(b"\x55" * 32, 0, b"", 0x80000000))
    tx.add_output(bt.TxOut(90000, b"\x00\x14" + b"\x66" * 20))
    r = bt._valid_small_r_values()[0]
    s = 17
    signature = ec.encode_der_sig(r, s, sighash=1)
    lock = bt.push_data(signature) + bytes([bt.OP_SWAP, bt.OP_CHECKSIG])
    script_code = bt.find_and_delete(lock, signature)
    digest = tx.sighash(1, script_code, 1)
    point = ec.ecdsa_recover(r, s, digest, 0)
    assert point and ec.ecdsa_verify(point, digest, r, s)
    key = ec.compress_pubkey(point)
    wrong_key = ec.compress_pubkey(ec.G)
    assert wrong_key != key

    adapter = Path(__file__).with_name("core_variable_inputs_adapter.py")
    cases = []
    for name, script_sig, expected in (
        ("push_only_baseline", bt.push_data(key), True),
        ("scriptsig_codeseparator_before_key", b"\xab" + bt.push_data(key), True),
        ("scriptsig_codeseparator_after_key", bt.push_data(key) + b"\xab", True),
        ("scriptsig_equalverify_then_codeseparator",
         b"\x51\x51\x88\xab" + bt.push_data(key), True),
        ("scriptsig_add_drop_then_codeseparator",
         b"\x51\x51\x93\x75\xab" + bt.push_data(key), True),
        ("scriptsig_extra_stack_cell", b"\x51\x51\x93" + bt.push_data(key), True),
        ("wrong_key_after_codeseparator", b"\xab" + bt.push_data(wrong_key), False),
    ):
        tx.inputs[1].script_sig = script_sig
        assert tx.sighash(1, script_code, 1) == digest
        raw = tx.serialize()
        request = {"transaction_hex": raw.hex(), "spent_outputs": [
            {"script_pubkey_hex": "51", "value": 1000},
            {"script_pubkey_hex": lock.hex(), "value": 100000},
        ]}
        result = subprocess.run(
            [sys.executable, str(adapter), "--library", str(library)],
            input=json.dumps(request), text=True, capture_output=True,
            check=True, timeout=30,
        )
        response = json.loads(result.stdout)
        assert response["api_version"] == 2
        assert response["inputs"][0] == {"valid": True, "error": 0}
        accepted = response["inputs"][1]["valid"]
        case = {
            "name": name,
            "accepted": accepted,
            "expected": expected,
            "script_sig_hex": script_sig.hex(),
            "raw_tx_sha256": hashlib.sha256(raw).hexdigest(),
            "core_error": response["inputs"][1]["error"],
        }
        cases.append(case)
        assert accepted == expected, case

    report = {
        "scope": "isolated CHECKSIG lock; not QSB acceptance or universal refinement",
        "core_version": "27.2",
        "core_api_version": 2,
        "core_flags": response["flags"],
        "app_builder_sha256": PINNED_BUILDER_SHA256,
        "app_secp256k1_sha256": helper_hash,
        "core_archive_sha256": PINNED_MACOS_ARCHIVE_SHA256,
        "archived_library_sha256": PINNED_MACOS_ORIGINAL_LIBRARY_SHA256,
        "loaded_library_sha256": PINNED_MACOS_RESIGNED_LIBRARY_SHA256,
        "adapter_source_sha256": sha256_file(adapter),
        "lock_hex": lock.hex(),
        "script_code_hex": script_code.hex(),
        "sighash_all_digest_hex": digest.to_bytes(32, "big").hex(),
        "signature_hex": signature.hex(),
        "pubkey_hex": key.hex(),
        "cases": cases,
    }
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps([{"name": c["name"], "accepted": c["accepted"]}
                      for c in cases], indent=2))


if __name__ == "__main__":
    main()
