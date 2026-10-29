"""Probe the narrow HASH160 scriptSig fragment against pinned Core 27.2.

These isolated consensus cases check acceptance and one-cell stack handoff.
The API does not expose hash-call order or an opcode trace, and the cases do
not refine the full QSB lock or arbitrary scriptSig execution.
"""

import argparse
import hashlib
import json
import subprocess
import sys
from pathlib import Path


PINNED_IMAGE = (
    "python@sha256:aa943ce411423c7582288f18707ff66eddcbaeb510502d747a72aeb34f30d159"
)
PINNED_BUILDER_SHA256 = "c7e52af90bd0d9fce9834fce26dcd67aee0d7751ee228d9730873c4d12659a5c"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--app-root", type=Path, required=True)
    parser.add_argument("--native-root", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()

    builder = args.app_root / "worker/cpu/bitcoin_tx.py"
    assert hashlib.sha256(builder.read_bytes()).hexdigest() == PINNED_BUILDER_SHA256
    root = Path(__file__).resolve().parents[1]
    native_hashes = json.loads((root / "evidence/round-results.json").read_text())[
        "native_files_sha256"
    ]
    for name, expected in native_hashes.items():
        assert hashlib.sha256((args.native_root / name).read_bytes()).hexdigest() == expected
    sys.path.insert(0, str(args.app_root / "worker/cpu"))
    import bitcoin_tx as bt

    tx = bt.Transaction(version=1, locktime=0)
    tx.add_input(bt.TxIn(b"\x44" * 32, 0, b"", 0xFFFFFFFE))
    tx.add_input(bt.TxIn(b"\x55" * 32, 0, b"", 0xFFFFFFFE))
    tx.add_output(bt.TxOut(90000, b"\x51"))
    native = args.native_root.resolve()
    cases = []

    def check(name, script_sig, lock, expected):
        tx.inputs[1].script_sig = script_sig
        raw_tx = tx.serialize()
        request = f"{raw_tx.hex()}\n2\n1000\n51\n100000\n{lock.hex()}\n"
        result = subprocess.run(
            ["docker", "run", "--rm", "--network", "none", "--read-only",
             "--cap-drop=ALL", "--security-opt=no-new-privileges",
             "--platform=linux/arm64", "-i", "-v", f"{native}:/native:ro",
             PINNED_IMAGE, "/native/qsb-consensus"],
            input=request, text=True, capture_output=True, timeout=30,
        )
        if result.returncode not in (0, 1):
            raise RuntimeError(result.stderr)
        accepted = (
            result.returncode == 0
            and result.stdout.strip() == "core-27.2-api2-all-inputs-valid"
        )
        case = {
            "name": name,
            "accepted": accepted,
            "expected": expected,
            "native_returncode": result.returncode,
            "native_stdout": result.stdout.strip(),
            "script_sig_hex": script_sig.hex(),
            "lock_hex": lock.hex(),
            "raw_tx_sha256": hashlib.sha256(raw_tx).hexdigest(),
        }
        cases.append(case)
        assert accepted == expected, case

    opening = b"\x11\x22\x33"
    digest = hashlib.new("ripemd160", hashlib.sha256(opening).digest()).digest()
    payload = b"\x42"
    suffix = b"\xa9" + bt.push_data(digest) + b"\x88" + bt.push_data(payload)
    # EQUALVERIFY consumes the one supplied payload, then the depth check
    # accepts exactly the empty residual stack.
    exact_cell_lock = bt.push_data(payload) + b"\x88\x74\x00\x87"
    check("canonical_success", bt.push_data(opening) + suffix,
          exact_cell_lock, True)
    wrong = bytes([digest[0] ^ 1]) + digest[1:]
    check("wrong_digest",
          bt.push_data(opening) + b"\xa9" + bt.push_data(wrong) +
          b"\x88" + bt.push_data(payload), exact_cell_lock, False)
    check("extra_payload_cell",
          bt.push_data(b"\x43") + bt.push_data(opening) + suffix,
          exact_cell_lock, False)
    check("unsupported_nop_suffix",
          bt.push_data(opening) + b"\xa9" + bt.push_data(digest) +
          b"\x61" + bt.push_data(payload), exact_cell_lock, False)
    # Core can parse this noncanonical short PUSHDATA1, but the restricted
    # Lean directPush deliberately rejects it.
    check("pushdata1_opening_outside_fragment",
          b"\x4c" + bytes([len(opening)]) + opening + suffix,
          exact_cell_lock, True)

    report = {
        "scope": "isolated Core 27.2 acceptance cases; no opcode trace or full QSB refinement",
        "core_version": "27.2",
        "core_api_version": 2,
        "core_flags": "bitcoinconsensus_SCRIPT_FLAGS_VERIFY_ALL",
        "image": PINNED_IMAGE,
        "builder_sha256": PINNED_BUILDER_SHA256,
        "native_files_sha256": native_hashes,
        "cases": cases,
    }
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps([{"name": c["name"], "accepted": c["accepted"]}
                      for c in cases], indent=2))


if __name__ == "__main__":
    main()
