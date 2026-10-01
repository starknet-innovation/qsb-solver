"""Compare Lean-checked wire vectors with the pinned app field serializer.

This checks selected boundaries of CompactSize and a nonnegative CAmount.
The matching Lean examples live in QSB/WireIntegers.lean. Pinned Core source
inspection remains the C++ serializer bridge; these app vectors are finite.
"""

import argparse
import hashlib
import json
import sys
from pathlib import Path


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--app-root", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    pinned = json.loads((root / "evidence/source-inventory.json").read_text())["app"]
    source = args.app_root / "worker/cpu/bitcoin_tx.py"
    source_hash = hashlib.sha256(source.read_bytes()).hexdigest()
    assert source_hash == pinned["files"]["worker/cpu/bitcoin_tx.py"]
    sys.path.insert(0, str(args.app_root / "worker/cpu"))
    import bitcoin_tx as bt

    expected_compact = {
        252: "fc",
        253: "fdfd00",
        65535: "fdffff",
        65536: "fe00000100",
        2**32: "ff0000000001000000",
    }
    compact = {str(n): bt.serialize_varint(n).hex() for n in expected_compact}
    for n, expected in expected_compact.items():
        assert compact[str(n)] == expected, (n, compact[str(n)])
    amount = bt.TxOut(90000, b"").serialize()[:8].hex()
    assert amount == "905f010000000000", amount
    report = {
        "scope": "finite pinned-app field vectors matching checked Lean examples",
        "source_revision": pinned["revision"],
        "source_sha256": source_hash,
        "compactsize_hex": compact,
        "nonnegative_amount_90000_le64_hex": amount,
    }
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
