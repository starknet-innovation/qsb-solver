"""Probe transaction framing boundaries in pinned Core 27.2.

Each transaction is disposable and spends a synthetic OP_TRUE output only
inside libbitcoinconsensus. No funding, network submission, or signing.
"""

import argparse
import hashlib
import json
import subprocess
from pathlib import Path


PINNED_LIBRARY_SHA256 = "5d7874783dc4989357600b3f273a44627d8ca6ac037f63d851572ff64a756983"
PINNED_IMAGE = "sha256:06da5a3362eda00c5114227ac81abe56dd9b943395553b7c64a310457f4d9e2b"


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--native-root", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    native_root = args.native_root.resolve()
    assert hashlib.sha256((native_root / "libbitcoinconsensus.so.0").read_bytes()).hexdigest() == PINNED_LIBRARY_SHA256
    adapter = Path(__file__).with_name("core_variable_inputs_adapter.py").resolve()

    version = (2).to_bytes(4, "little")
    outpoint = bytes([0x11]) * 32 + (0).to_bytes(4, "little")
    sequence = (0xFFFFFFFE).to_bytes(4, "little")
    amount = (1000).to_bytes(8, "little")
    locktime = (0).to_bytes(4, "little")

    def transaction(input_count: bytes = b"\x01", script_sig_length: bytes = b"\x00",
                    output_count: bytes = b"\x01", output_script_length: bytes = b"\x01") -> bytes:
        return (version + input_count + outpoint + script_sig_length + sequence
                + output_count + amount + output_script_length + b"\x51" + locktime)

    cases = {
        "canonical": transaction(),
        "input_count_overlong_16": transaction(input_count=b"\xfd\x01\x00"),
        "input_count_overlong_32": transaction(input_count=b"\xfe\x01\x00\x00\x00"),
        "input_count_overlong_64": transaction(input_count=b"\xff\x01" + b"\x00" * 7),
        "script_sig_length_overlong": transaction(script_sig_length=b"\xfd\x00\x00"),
        "output_count_overlong": transaction(output_count=b"\xfd\x01\x00"),
        "output_script_length_overlong": transaction(output_script_length=b"\xfd\x01\x00"),
        "segwit_all_witnesses_empty": version + b"\x00\x01" + transaction()[4:-4] + b"\x00" + locktime,
        "segwit_unknown_flag": version + b"\x00\x02" + transaction()[4:-4] + locktime,
    }
    results = []
    for name, raw in cases.items():
        request = {
            "transaction_hex": raw.hex(),
            "spent_outputs": [{"script_pubkey_hex": "51", "value": 1000}],
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
        assert len(response["inputs"]) == 1
        result = response["inputs"][0]
        assert result["valid"] == (name == "canonical"), (name, result)
        if name != "canonical":
            assert result["error"] != 0, (name, result)
        results.append({"name": name, "transaction_hex": raw.hex(),
                        "transaction_sha256": hashlib.sha256(raw).hexdigest(),
                        **result})

    report = {
        "scope": "Finite libbitcoinconsensus API v2 parser differential, not a consensus proof",
        "image": PINNED_IMAGE,
        "library_sha256": PINNED_LIBRARY_SHA256,
        "adapter_sha256": hashlib.sha256(adapter.read_bytes()).hexdigest(),
        "cases": results,
    }
    args.output.write_text(json.dumps(report, sort_keys=True, indent=2) + "\n")
    print(f"Checked {len(results)} pinned Core cases; {sum(r['valid'] for r in results)} accepted")


if __name__ == "__main__":
    main()
