"""Test the scriptSig-to-bare-script boundary in pinned Core 27.2.

These are synthetic, isolated scripts. They do not exercise QSB's lock or
establish a Core-to-Lean interpreter refinement.
"""

import argparse
import hashlib
import json
import subprocess
import sys
from pathlib import Path

PINNED_BUILDER_SHA256 = "c7e52af90bd0d9fce9834fce26dcd67aee0d7751ee228d9730873c4d12659a5c"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--app-root", type=Path, required=True)
    parser.add_argument("--native-root", type=Path, required=True)
    parser.add_argument("--image", required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    builder_hash = hashlib.sha256(
        (args.app_root / "worker/cpu/bitcoin_tx.py").read_bytes()).hexdigest()
    assert builder_hash == PINNED_BUILDER_SHA256
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
        payload = f"{raw_tx.hex()}\n2\n1000\n51\n100000\n{lock.hex()}\n"
        result = subprocess.run(
            ["docker", "run", "--rm", "--network", "none", "--read-only",
             "--cap-drop=ALL", "--security-opt=no-new-privileges",
             "--platform=linux/arm64", "-i", "-v", f"{native}:/native:ro",
             args.image, "/native/qsb-consensus"],
            input=payload, text=True, capture_output=True, timeout=30,
        )
        if result.returncode not in (0, 1):
            raise RuntimeError(result.stderr)
        accepted = (result.returncode == 0 and
                    result.stdout.strip() == "core-27.2-api2-all-inputs-valid")
        case = {
            "name": name, "accepted": accepted, "expected": expected,
            "script_sig_hex": script_sig.hex(), "lock_hex": lock.hex(),
            "raw_tx_sha256": hashlib.sha256(raw_tx).hexdigest(),
        }
        cases.append(case)
        assert accepted == expected, case

    # 1 1 ADD is non-push-only; the bare lock must receive its result, 2.
    check("nonpush_scriptsig_stack_handoff", b"\x51\x51\x93",
          b"\x52\x87", True)  # 2 EQUAL
    check("failing_scriptsig_cannot_be_repaired", b"\x93",
          b"\x51", False)

    # OP_NOP counts, while OP_TRUE does not. The two EvalScript calls have
    # independent 201-opcode counters; a 202nd counted opcode fails either.
    check("independent_201_opcode_budgets", b"\x61" * 201,
          b"\x61" * 201 + b"\x51", True)
    check("scriptsig_202_opcodes_rejected", b"\x61" * 202,
          b"\x51", False)
    check("bare_lock_202_opcodes_rejected", b"\x61" * 201,
          b"\x61" * 202 + b"\x51", False)

    # Each data push is at most 499 bytes and is immediately dropped. These
    # truthy scripts use only 20 counted OP_DROP instructions, so the size
    # limit is isolated from element, stack, and opcode-count limits.
    def truthy_lock_of_size(size):
        base = (bt.push_data(b"\x00" * 499) + b"\x75") * 19
        tail_size = size - len(base) - 1
        tail_data = b"\x00" * (tail_size - 4)
        lock = base + bt.push_data(tail_data) + b"\x75\x51"
        assert len(tail_data) <= 520 and len(lock) == size
        return lock

    check("bare_lock_9981_bytes_accepted", b"",
          truthy_lock_of_size(9981), True)
    check("bare_lock_10000_bytes_accepted", b"",
          truthy_lock_of_size(10000), True)
    check("bare_lock_10001_bytes_rejected", b"",
          truthy_lock_of_size(10001), False)

    report = {
        "scope": "isolated bare legacy scripts; not a full QSB spend or formal refinement",
        "core_flags": "bitcoinconsensus_SCRIPT_FLAGS_VERIFY_ALL",
        "image": args.image,
        "source_revision": subprocess.check_output(
            ["git", "-C", str(args.app_root), "rev-parse", "HEAD"],
            text=True).strip(),
        "builder_sha256": builder_hash,
        "native_executable_sha256": hashlib.sha256(
            (native / "qsb-consensus").read_bytes()).hexdigest(),
        "native_library_sha256": hashlib.sha256(
            (native / "libbitcoinconsensus.so.0").read_bytes()).hexdigest(),
        "cases": cases,
    }
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps([{"name": c["name"], "accepted": c["accepted"]}
                      for c in cases], indent=2))


if __name__ == "__main__":
    main()
