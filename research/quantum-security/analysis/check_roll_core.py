"""Finite pinned-Core probes of bare-script OP_ROLL depth and byte parsing.

The first input is a trivial true script. The second input pushes a known
bottom-first byte stack and raw index; its bare lock rolls and compares the
selected cell. These are isolated opcode tests, not QSB withdrawals.
"""

import argparse
import hashlib
import json
import subprocess
import sys
from pathlib import Path


def run_case(bt, native_root: Path, image: str, name: str,
             cells: list[bytes], raw: bytes, expected: bytes,
             should_accept: bool) -> dict:
    tx = bt.Transaction(version=1, locktime=0)
    tx.add_input(bt.TxIn(b"\x11" * 32, 0, bytes([bt.OP_1])))
    script_sig = b"".join(bt.push_data(cell) for cell in cells)
    script_sig += bt.push_data(raw)
    tx.add_input(bt.TxIn(b"\x22" * 32, 0, script_sig))
    tx.add_output(bt.TxOut(90000, bytes([bt.OP_1])))
    lock = bytes([bt.OP_ROLL]) + bt.push_data(expected) + b"\x87"  # OP_EQUAL
    payload = f"{tx.serialize().hex()}\n2\n1000\n51\n100000\n{lock.hex()}\n"
    result = subprocess.run(
        ["docker", "run", "--rm", "--network", "none", "--read-only",
         "--cap-drop=ALL", "--security-opt=no-new-privileges",
         "--platform=linux/arm64", "-i",
         "-v", f"{native_root.resolve()}:/native:ro", image,
         "/native/qsb-consensus"],
        input=payload, text=True, capture_output=True, timeout=30,
    )
    if result.returncode not in (0, 1):
        raise RuntimeError(f"Core adapter unavailable: {result.stderr}")
    accepted = (result.returncode == 0 and
                result.stdout.strip() == "core-27.2-api2-all-inputs-valid")
    assert accepted == should_accept, (name, result)
    return {
        "name": name,
        "cell_count": len(cells),
        "raw_index_hex": raw.hex(),
        "expected_top_hex": expected.hex(),
        "accepted": accepted,
        "transaction_sha256": hashlib.sha256(tx.serialize()).hexdigest(),
        "test_lock_sha256": hashlib.sha256(lock).hexdigest(),
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--app-root", type=Path, required=True)
    parser.add_argument("--native-root", type=Path, required=True)
    parser.add_argument("--image", required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    inventory = json.loads((Path(__file__).resolve().parents[1] /
                            "evidence/source-inventory.json").read_text())
    source_hashes = {}
    for relative in ("worker/cpu/bitcoin_tx.py", "consensus/verify.cpp"):
        digest = hashlib.sha256((args.app_root / relative).read_bytes()).hexdigest()
        if digest != inventory["app"]["files"][relative]:
            raise RuntimeError(f"unpinned app source: {relative}")
        source_hashes[relative] = digest
    sys.path.insert(0, str(args.app_root / "worker/cpu"))
    import bitcoin_tx as bt

    three = [b"\xa1", b"\xb2", b"\xc3"]
    deep = [b"\xa1"] + [b"\xc3"] * 152
    cases = [
        ("top_zero", three, b"", b"\xc3", True),
        ("top_negative_zero", three, b"\x80", b"\xc3", True),
        ("middle_one", three, b"\x01", b"\xb2", True),
        ("middle_one_nonminimal", three, b"\x01\x00", b"\xb2", True),
        ("bottom_two", three, b"\x02", b"\xa1", True),
        ("negative_one", three, b"\x81", b"\xa1", False),
        ("past_bottom_three", three, b"\x03", b"\xa1", False),
        ("deep_152", deep, b"\x98\x00", b"\xa1", True),
        ("deep_152_nonminimal", deep, b"\x98\x00\x00\x00", b"\xa1", True),
        ("max_positive_out_of_range", three, b"\xff\xff\xff\x7f", b"\xa1", False),
        ("five_byte_operand", three, b"\x01\x00\x00\x00\x00", b"\xb2", False),
    ]
    results = [run_case(bt, args.native_root, args.image, *case) for case in cases]
    report = {
        "scope": "finite OP_ROLL probe on a disposable two-input bare-script transaction",
        "source_revision": subprocess.check_output(
            ["git", "-C", str(args.app_root), "rev-parse", "HEAD"], text=True
        ).strip(),
        "source_file_sha256": source_hashes,
        "native_files_sha256": {
            p.name: hashlib.sha256(p.read_bytes()).hexdigest()
            for p in args.native_root.iterdir() if p.is_file()
        },
        "image": args.image,
        "cases": results,
    }
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({row["name"]: row["accepted"] for row in results}))


if __name__ == "__main__":
    main()
