"""Show that pinned Core script-API success need not mean transaction validity.

Both disposable transactions have two inputs and one OP_TRUE output. The
second case repeats the first input's prevout, which Core 27.2's
CheckTransaction rejects before contextual checks. The script API is run for
both inputs, with no funding, signing, RPC, or broadcast.
"""

import argparse
import hashlib
import json
import subprocess
from pathlib import Path


PINNED_LIBRARY_SHA256 = "5d7874783dc4989357600b3f273a44627d8ca6ac037f63d851572ff64a756983"
PINNED_IMAGE = "sha256:f77ac9e44ae96ef2c90b8053ea08c31f8be030f824196b0ae4db6d462c84e51f"


def input_bytes(txid_byte: int) -> bytes:
    return (bytes([txid_byte]) * 32 + (0).to_bytes(4, "little")
            + b"\x00" + (0xFFFFFFFE).to_bytes(4, "little"))


def transaction(second_txid_byte: int) -> bytes:
    return (b"\x02\x00\x00\x00" + b"\x02"
            + input_bytes(0x11) + input_bytes(second_txid_byte)
            + b"\x01" + (1000).to_bytes(8, "little") + b"\x01\x51"
            + b"\x00\x00\x00\x00")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--native-root", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    native_root = args.native_root.resolve()
    assert hashlib.sha256((native_root / "libbitcoinconsensus.so.0").read_bytes()).hexdigest() == PINNED_LIBRARY_SHA256
    adapter = Path(__file__).with_name("core_variable_inputs_adapter.py").resolve()
    cases = []
    for name, second_byte, duplicate in (
            ("distinct_prevouts", 0x22, False),
            ("duplicate_prevout", 0x11, True)):
        raw = transaction(second_byte)
        request = {
            "transaction_hex": raw.hex(),
            "spent_outputs": [
                {"script_pubkey_hex": "51", "value": 1000},
                {"script_pubkey_hex": "51", "value": 1000},
            ],
        }
        process = subprocess.run([
            "docker", "run", "--rm", "--network", "none", "--read-only",
            "--cap-drop=ALL", "--security-opt=no-new-privileges",
            "--platform=linux/arm64", "-i",
            "-v", f"{native_root}:/native:ro",
            "-v", f"{adapter}:/adapter.py:ro", PINNED_IMAGE,
            "python3", "/adapter.py",
        ], input=json.dumps(request) + "\n", text=True, capture_output=True,
            timeout=30)
        if process.returncode:
            raise RuntimeError(f"{name}: {process.stderr}")
        response = json.loads(process.stdout)
        assert response["api_version"] == 2
        assert response["inputs"] == [
            {"valid": True, "error": 0}, {"valid": True, "error": 0}], (name, response)
        cases.append({
            "name": name,
            "duplicate_prevout": duplicate,
            "transaction_hex": raw.hex(),
            "transaction_sha256": hashlib.sha256(raw).hexdigest(),
            "script_api": response,
            "check_transaction_source_result": (
                "bad-txns-inputs-duplicate" if duplicate else "passes duplicate-prevout check"),
        })
    report = {
        "scope": "Finite pinned Core 27.2 script-API differential; CheckTransaction conclusion follows from pinned source, not an invoked validation API",
        "image": PINNED_IMAGE,
        "library_sha256": PINNED_LIBRARY_SHA256,
        "adapter_sha256": hashlib.sha256(adapter.read_bytes()).hexdigest(),
        "check_transaction_source": "https://github.com/bitcoin/bitcoin/blob/v27.2/src/consensus/tx_check.cpp",
        "script_api_source": "https://github.com/bitcoin/bitcoin/blob/v27.2/src/script/bitcoinconsensus.cpp",
        "cases": cases,
    }
    args.output.write_text(json.dumps(report, sort_keys=True, indent=2) + "\n")
    print("Checked two pinned Core transactions; both pass both input scripts")


if __name__ == "__main__":
    main()
