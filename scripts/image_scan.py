"""Scan an image with a pinned Grype and fail on critical findings that have a fix.

Severity is the worst of Grype's matched record (for Ubuntu packages, Ubuntu's
priority) and its related records (NVD CVSS). Ubuntu rates many CVEs below their
NVD score, so the matched severity alone would pass images that registry scanners
report as critical. Unfixed findings are reported but do not block: a rebuild
cannot remove them.
"""
import argparse
import hashlib
import io
import json
import os
import pathlib
import subprocess
import sys
import tarfile
import tempfile
import urllib.request

GRYPE_VERSION = "0.119.0"
# From grype_0.119.0_checksums.txt, whose Sigstore signature was checked against
# anchore/grype's release workflow identity before pinning.
GRYPE_SHA256 = {
    "linux_amd64": "3fa2dc4b924621ab65404cf08d0b8438d896d80ab949c9d5a4ca283c36004c9b",
    "linux_arm64": "29f0ec7c549ddb0e2b6a0ca714851f7399438afc399b80c12808e065edc9a8f8",
}
RANK = {"Unknown": 0, "Negligible": 1, "Low": 2, "Medium": 3, "High": 4, "Critical": 5}
NAMES = {rank: name for name, rank in RANK.items()}


def install(dest, platform="linux_amd64"):
    name = f"grype_{GRYPE_VERSION}_{platform}.tar.gz"
    url = f"https://github.com/anchore/grype/releases/download/v{GRYPE_VERSION}/{name}"
    with urllib.request.urlopen(url, timeout=120) as response:
        data = response.read()
    if hashlib.sha256(data).hexdigest() != GRYPE_SHA256[platform]:
        raise ValueError("Grype archive does not match the pinned hash")
    with tarfile.open(fileobj=io.BytesIO(data)) as archive:
        binary = archive.extractfile("grype").read()
    path = pathlib.Path(dest) / "grype"
    path.write_bytes(binary)
    path.chmod(0o755)
    return path


def severity(match):
    ranks = [RANK.get(match["vulnerability"].get("severity"), 0)]
    ranks += [RANK.get(r.get("severity"), 0) for r in match.get("relatedVulnerabilities", [])]
    return max(ranks)


def finding(match):
    v, a = match["vulnerability"], match["artifact"]
    return {"id": v["id"], "package": a["name"], "version": a["version"], "type": a["type"],
            "fixState": v["fix"]["state"], "fixVersions": v["fix"].get("versions", []),
            "matchedSeverity": v.get("severity"),
            "relatedSeverity": {r["id"] + "@" + r.get("namespace", ""): r.get("severity")
                                for r in match.get("relatedVulnerabilities", [])}}


def evaluate(report):
    counts = {name: {"total": 0, "fixable": 0} for name in RANK if name != "Unknown"}
    counts["Unknown"] = {"total": 0, "fixable": 0}
    blocking, unfixed = [], []
    for match in report["matches"]:
        rank = severity(match)
        fixable = match["vulnerability"]["fix"]["state"] == "fixed"
        counts[NAMES[rank]]["total"] += 1
        counts[NAMES[rank]]["fixable"] += fixable
        if rank == RANK["Critical"]:
            (blocking if fixable else unfixed).append(finding(match))
    descriptor = report.get("descriptor", {})
    target = report.get("source", {}).get("target", {})
    return {
        "source": {k: target.get(k) for k in ("userInput", "imageID", "manifestDigest", "repoDigests")},
        "scanner": {"name": descriptor.get("name"), "version": descriptor.get("version"),
                    "dbBuilt": descriptor.get("db", {}).get("status", {}).get("built")},
        "policy": "fail on Critical with a fix available; severity is the worst of the matched and related records",
        "counts": counts,
        "blocking": blocking,
        "unfixedCritical": unfixed,
        "passed": not blocking,
    }


def trimmed(report):
    """Keep the full match list, but not Grype's runtime configuration."""
    descriptor = report.get("descriptor", {})
    return {**report, "descriptor": {k: descriptor.get(k) for k in ("name", "version", "db", "timestamp")}}


def scan(grype, source, output):
    env = {**os.environ, "GRYPE_CHECK_FOR_APP_UPDATE": "false"}
    raw = subprocess.run([str(grype), source, "--platform", "linux/amd64", "-o", "json", "-q"],
                         check=True, capture_output=True, text=True, env=env, timeout=1800).stdout
    report = json.loads(raw)
    output.mkdir(parents=True, exist_ok=True)
    (output / "grype.json").write_text(json.dumps(trimmed(report), indent=1) + "\n")
    summary = evaluate(report)
    (output / "image-scan.json").write_text(json.dumps(summary, indent=2) + "\n")
    return summary


def main():
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("source", help="Grype source, e.g. docker:IMAGE or registry:IMAGE@sha256:DIGEST")
    parser.add_argument("output", type=pathlib.Path)
    parser.add_argument("--grype", type=pathlib.Path, help="existing Grype binary; default installs the pinned release")
    args = parser.parse_args()
    with tempfile.TemporaryDirectory() as tmp:
        summary = scan(args.grype or install(tmp), args.source, args.output)
    print(json.dumps({"source": summary["source"], "scanner": summary["scanner"],
                      "counts": summary["counts"], "passed": summary["passed"]}, indent=2))
    for item in summary["blocking"]:
        print(f"BLOCKING {item['id']} {item['package']} {item['version']} -> {','.join(item['fixVersions'])}")
    for item in summary["unfixedCritical"]:
        print(f"unfixed  {item['id']} {item['package']} {item['version']} ({item['fixState']})")
    return 0 if summary["passed"] else 1


if __name__ == "__main__":
    sys.exit(main())
