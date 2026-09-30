"""Check every project theorem is audited and uses only standard Lean axioms."""
import json
import re
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}

def main():
    build = subprocess.run(["lake", "build"], cwd=ROOT, text=True, capture_output=True)
    (ROOT / "evidence/lean-build.txt").write_text(build.stdout + build.stderr)
    if build.returncode:
        raise SystemExit(build.stdout + build.stderr)
    result = subprocess.run(["lake", "env", "lean", "QSB.lean"], cwd=ROOT,
                            text=True, capture_output=True)
    output = result.stdout + result.stderr
    (ROOT / "evidence/axioms.txt").write_text(output)
    if result.returncode:
        raise SystemExit(output)
    expected = set()
    for path in (ROOT / "QSB").glob("*.lean"):
        source = path.read_text()
        # This complements, but does not replace, kernel dependency inspection.
        if re.search(r"^\s*(axiom|opaque)\b|\b(sorry|admit|native_decide)\b", source, re.M):
            raise SystemExit(f"Unreviewed proof escape or opaque declaration in {path.name}")
        namespace = re.search(r"^namespace\s+([\w.]+)", source, re.M)
        if not namespace:
            raise SystemExit(f"Expected a namespace in {path.name}")
        expected.update(namespace.group(1) + "." + name
                        for name in re.findall(r"^theorem\s+(\w+)", source, re.M))
    audited = {}
    for name, axioms in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", output):
        dependencies = {x.strip() for x in axioms.split(",") if x.strip()}
        if dependencies - ALLOWED:
            raise SystemExit(f"Unexpected dependency: {name}: {dependencies - ALLOWED}")
        audited[name] = sorted(dependencies)
    for name in re.findall(r"'([^']+)' does not depend on any axioms", output):
        audited[name] = []
    if set(audited) != expected:
        raise SystemExit(f"Theorem audit mismatch: {expected ^ set(audited)}")
    report = {"theorem_count": len(audited), "allowed_foundations": sorted(ALLOWED),
              "theorems": dict(sorted(audited.items()))}
    (ROOT / "evidence/axiom-audit.json").write_text(json.dumps(report, indent=2) + "\n")
    print(f"Checked {len(audited)} theorem dependency lists; no additional axioms.")

if __name__ == "__main__":
    main()
