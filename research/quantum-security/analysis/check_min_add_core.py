"""Probe the first signed OP_MIN; OP_ADD byte path against pinned Core 27.2.

Each input is a four-byte-or-shorter ScriptNum encoding parsed without
MINIMALDATA. The lock compares Core's serialized output after MIN 152 and ADD
151 with an independent sign-magnitude encoding. This is a finite bare-script
probe, not a full QSB lock execution or a Core-to-Lean theorem.
"""

import argparse
import hashlib
import json
import subprocess
import sys
from pathlib import Path

from check_scriptnum_core import encode_scriptnum, scriptnum


def corpus() -> list[tuple[str, bytes]]:
    return [
        ("empty_zero", b""),
        ("one_byte_zero", b"\x00"),
        ("negative_zero", b"\x80"),
        ("one", b"\x01"),
        ("two", b"\x02"),
        ("nonminimal_ten", b"\x0a\x00"),
        ("below_cap", b"\x97\x00"),
        ("at_cap", b"\x98\x00"),
        ("nonminimal_cap", b"\x98\x00\x00"),
        ("above_cap", b"\x99\x00"),
        ("one_byte_127", b"\x7f"),
        ("two_byte_32767", b"\xff\x7f"),
        ("four_byte_max", b"\xff\xff\xff\x7f"),
        ("negative_one", b"\x81"),
        ("nonminimal_negative_one", b"\x01\x80"),
        ("negative_152", b"\x98\x80"),
        ("four_byte_negative_max", b"\xff\xff\xff\xff"),
    ]


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--app-root", type=Path, required=True)
    parser.add_argument("--native-root", type=Path, required=True)
    parser.add_argument("--image", required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    inventory = json.loads((root / "evidence/source-inventory.json").read_text())
    for relative in ("worker/cpu/bitcoin_tx.py", "consensus/verify.cpp"):
        digest = hashlib.sha256((args.app_root / relative).read_bytes()).hexdigest()
        assert digest == inventory["app"]["files"][relative], relative
    sys.path.insert(0, str(args.app_root / "worker/cpu"))
    import bitcoin_tx as bt

    native = args.native_root.resolve()
    pinned = json.loads((root / "evidence/scriptnum-core.json").read_text())
    assert args.image == pinned["image"]
    for name, digest in pinned["native_files_sha256"].items():
        assert hashlib.sha256((native / name).read_bytes()).hexdigest() == digest

    rows = corpus()
    assert all(len(raw) <= 4 for _, raw in rows)
    tx = bt.Transaction(version=1, locktime=0)
    tx.add_input(bt.TxIn(b"\x11" * 32, 0, bytes([bt.OP_1])))
    tx.add_input(bt.TxIn(b"\x22" * 32, 0,
                         b"".join(bt.push_data(raw) for _, raw in reversed(rows))))
    tx.add_output(bt.TxOut(90000, bytes([bt.OP_1])))

    def lock_for(delta: int = 0) -> bytes:
        lock = bytearray()
        for i, (_, raw) in enumerate(rows):
            expected = encode_scriptnum(151 + min(152, scriptnum(raw)))
            if i == 0:
                expected = encode_scriptnum(151 + delta)
            lock += bt.push_data(encode_scriptnum(152))
            lock.append(bt.OP_MIN)
            lock += bt.push_data(encode_scriptnum(151))
            lock.append(bt.OP_ADD)
            lock += bt.push_data(expected)
            lock.append(bt.OP_EQUALVERIFY)
        lock.append(bt.OP_1)
        return bytes(lock)

    def check(script_sig: bytes, lock: bytes) -> tuple[bool, str, str]:
        tx.inputs[1].script_sig = script_sig
        raw = tx.serialize()
        payload = f"{raw.hex()}\n2\n1000\n51\n100000\n{lock.hex()}\n"
        run = subprocess.run([
            "docker", "run", "--rm", "--network", "none", "--read-only",
            "--cap-drop=ALL", "--security-opt=no-new-privileges",
            "--platform=linux/arm64", "-i", "-v", f"{native}:/native:ro",
            args.image, "/native/qsb-consensus"],
            input=payload, text=True, capture_output=True, timeout=30)
        if run.returncode not in (0, 1):
            raise RuntimeError(run.stderr)
        accepted = (run.returncode == 0 and
                    run.stdout.strip() == "core-27.2-api2-all-inputs-valid")
        return (accepted, hashlib.sha256(raw).hexdigest(),
                hashlib.sha256(lock).hexdigest())

    good = check(tx.inputs[1].script_sig, lock_for())
    wrong = check(tx.inputs[1].script_sig, lock_for(1))
    oversized = check(bt.push_data(b"\x01\x00\x00\x00\x00"),
                      bt.push_data(encode_scriptnum(152)) +
                      bytes([bt.OP_MIN, bt.OP_1]))
    assert (good[0], wrong[0], oversized[0]) == (True, False, False)
    report = {
        "scope": "isolated first signed MIN 152; ADD 151 path, not full QSB",
        "source_revision": subprocess.check_output(
            ["git", "-C", str(args.app_root), "rev-parse", "HEAD"],
            text=True).strip(),
        "image": args.image,
        "native_executable_sha256": pinned["native_files_sha256"]["qsb-consensus"],
        "native_library_sha256": pinned["native_files_sha256"]["libbitcoinconsensus.so.0"],
        "case_count": len(rows),
        "cases": [{"name": name, "raw_hex": raw.hex(),
                   "parsed": scriptnum(raw),
                   "expected_hex": encode_scriptnum(
                       151 + min(152, scriptnum(raw))).hex()}
                  for name, raw in rows],
        "valid_path": {"accepted": good[0], "transaction_sha256": good[1],
                       "lock_sha256": good[2]},
        "wrong_expected_control": {"accepted": wrong[0],
                                   "transaction_sha256": wrong[1],
                                   "lock_sha256": wrong[2]},
        "five_byte_rejection": {"accepted": oversized[0],
                                "transaction_sha256": oversized[1],
                                "lock_sha256": oversized[2]},
    }
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"case_count": len(rows),
                      "valid_path": good[0], "wrong_control": wrong[0],
                      "five_byte_rejected": not oversized[0]}))


if __name__ == "__main__":
    main()
