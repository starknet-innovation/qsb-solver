"""Offline source identity comparison; never a correctness or performance gate."""
import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath


def blob_map(document):
    if document.get("truncated") is not False:
        raise ValueError("a complete recursive Git tree is required")
    result = {}
    seen = set()
    for entry in document["tree"]:
        name = entry["path"]
        path = PurePosixPath(name)
        if path.is_absolute() or ".." in path.parts or str(path) != name:
            raise ValueError("invalid tree path")
        if name in seen:
            raise ValueError("duplicate tree path")
        seen.add(name)
        if entry["type"] == "blob":
            result[name] = {"sha": entry["sha"], "mode": entry["mode"]}
    return result


def compare_trees(before, after):
    old, new = blob_map(before), blob_map(after)
    return [{"path": name, "before": old.get(name), "after": new.get(name)}
            for name in sorted(old.keys() | new.keys())
            if old.get(name) != new.get(name)]


def compare_lock(root, lock, upstream, prefix=""):
    root = Path(root).resolve()
    blobs = blob_map(upstream)
    rows = []
    for name, expected in sorted(lock["files"].items()):
        path = PurePosixPath(name)
        if path.is_absolute() or ".." in path.parts or str(path) != name:
            raise ValueError("invalid locked path")
        source = root / name
        if not source.resolve().is_relative_to(root):
            raise ValueError("locked path escapes source root")
        upstream_name = f"{prefix.rstrip('/')}/{name}" if prefix else name
        remote = blobs.get(upstream_name)
        data = source.read_bytes() if source.is_file() else None
        sha256 = hashlib.sha256(data).hexdigest() if data is not None else None
        git_sha = (hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data)
                   .hexdigest() if data is not None else None)
        rows.append({"path": name, "upstreamPath": upstream_name,
                     "expectedSha256": expected, "actualSha256": sha256,
                     "matchesLock": sha256 == expected,
                     "presentUpstream": remote is not None,
                     "matchesUpstreamBytes": remote is not None and git_sha == remote["sha"]})
    return rows


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--before", type=Path, required=True)
    parser.add_argument("--after", type=Path, required=True)
    parser.add_argument("--lock", type=Path, required=True)
    parser.add_argument("--root", type=Path, required=True)
    parser.add_argument("--prefix", default="")
    args = parser.parse_args()
    before, after, lock = [json.loads(p.read_text()) for p in
                           (args.before, args.after, args.lock)]
    rows = compare_lock(args.root, lock, after, args.prefix)
    print(json.dumps({"scope": "offline source identity only; no runtime attestation",
                      "changedBlobs": compare_trees(before, after),
                      "lockedFiles": rows}, indent=2))
    return 0 if all(row["matchesLock"] for row in rows) else 1


if __name__ == "__main__":
    raise SystemExit(main())
