"""Generate a descriptor bound to the release image and tested range contract."""
import hashlib
import json
import os
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "worker"))
from search_ranges import VERSION, work_range


def search_contract(path=None):
    """Hash canonical JSON only after checking the vectors against this worker."""
    value = json.loads((path or ROOT / "contracts/ranked-v2.json").read_text())
    if value.get("searchVersion") != VERSION or not value.get("cases") or not value.get("invalid"):
        raise ValueError("Invalid search contract")
    for case in value["cases"]:
        if work_range(case["stage"], case["attempt"]) != case["range"]:
            raise ValueError("Search contract does not match worker")
    for case in value["invalid"]:
        try:
            work_range(case["stage"], case["attempt"])
        except ValueError:
            continue
        raise ValueError("Search contract invalid case accepted by worker")
    canonical = json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=False)
    return hashlib.sha256(canonical.encode("utf-8")).hexdigest()


def descriptor(commit, digest):
    if not re.fullmatch("[0-9a-f]{40}", commit):
        raise ValueError("Invalid solver commit")
    if not re.fullmatch("sha256:[0-9a-f]{64}", digest):
        raise ValueError("Invalid registry digest")
    return {"schemaVersion": 3, "id": "qsb-ranked-v2-" + commit[:12] + "-" + digest[7:19],
            "protocol": "qsb-config-a-v1", "generatorCommit": "2c9172051d5c150ef0a994ca6b988a08a3ef9e85",
            "searchVersion": VERSION, "searchContract": search_contract(),
            "solverRepository": "https://github.com/starknet-innovation/qsb-solver",
            "solverCommit": commit, "kernelCommit": "2791ed0588f5014ccd688d48ba5502df2879f2f1",
            "image": "ghcr.io/starknet-innovation/qsb-solver@" + digest}


if __name__ == "__main__":
    value = descriptor(os.environ["SOLVER_COMMIT"], os.environ["IMAGE_DIGEST"])
    target = pathlib.Path("release-output")
    target.mkdir(exist_ok=True)
    (target / "solver.json").write_text(json.dumps(value, indent=2) + "\n")
