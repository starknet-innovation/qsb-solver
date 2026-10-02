"""Compare pinned Linux and host-native Core full-lock fixture results."""

import argparse
import hashlib
import json
from pathlib import Path


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--linux-report", type=Path, required=True)
    parser.add_argument("--host-report", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    linux_bytes = args.linux_report.read_bytes()
    host_bytes = args.host_report.read_bytes()
    linux = json.loads(linux_bytes)
    host = json.loads(host_bytes)
    assert linux["cases"] == host["cases"]
    assert host["adapter_mode"] == "host-library"
    for field in ("builder_sha256", "helper_files_sha256", "exact_lock_sha256",
                  "test_lock_sha256", "bug_message_scalar_hex",
                  "in_range_message_scalar_hex"):
        assert linux[field] == host[field], field
    report = {
        "matching_cases": len(linux["cases"]),
        "all_case_records_identical": True,
        "linux_report_sha256": hashlib.sha256(linux_bytes).hexdigest(),
        "host_report_sha256": hashlib.sha256(host_bytes).hexdigest(),
        "host_archive_sha256": host["core_archive_sha256"],
        "host_original_library_sha256": host["archived_library_sha256"],
        "host_loaded_library_sha256": host["native_files_sha256"],
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
