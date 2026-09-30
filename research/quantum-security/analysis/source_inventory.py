"""Record the exact local, public source used by this analysis. No wallet reads."""
import argparse
import hashlib
import json
import subprocess
from pathlib import Path

APP_FILES = [
    "AGENTS.md", "worker/cpu/bitcoin_tx.py", "worker/cpu/secp256k1.py",
    "worker/cpu/qsb_pipeline.py", "worker/cpu/verify_hit.py", "worker/cpu/handler.py",
    "public/qsb/bridge.py", "public/qsb/bitcoin_tx.py", "public/qsb/qsb_pipeline.py",
    "src/lib/backup.ts", "src/lib/transactions.ts", "src/lib/model.ts",
    "src/lib/wallet.ts", "src/TransactionDialog.tsx",
    "sdk/client.ts", "sdk/runtime.ts", "sdk/signer.ts", "sdk/cli.ts",
    "server/consensus.ts", "consensus/verify.cpp", "consensus/build.mjs",
    "scripts/vendor.py", "scripts/patch_upstream.py", "docs/KEY-CUSTODY.md",
]
SOLVER_FILES = ["README.md", "worker/prepare_kernels.py", "contracts/ranked-v2.json",
                "vendor/challenge/provenance.json", "worker/promotion/README.md"]

def git(root, *args):
    return subprocess.check_output(["git", "-C", str(root), *args], text=True).strip()

def inventory(root, paths):
    return {"revision": git(root, "rev-parse", "HEAD"),
            "files": {p: hashlib.sha256((root / p).read_bytes()).hexdigest() for p in paths},
            "tracked_modifications": git(root, "status", "--porcelain", "--untracked-files=no")}

if __name__ == "__main__":
    p = argparse.ArgumentParser()
    p.add_argument("--app-root", type=Path, required=True)
    p.add_argument("--output", type=Path, required=True)
    a = p.parse_args()
    solver = Path(__file__).resolve().parents[3]
    result = {"app": inventory(a.app_root, APP_FILES), "solver": inventory(solver, SOLVER_FILES)}
    a.output.write_text(json.dumps(result, indent=2) + "\n")
