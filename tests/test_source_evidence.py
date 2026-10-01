import hashlib
import importlib.util
from pathlib import Path
import tempfile
import unittest

spec = importlib.util.spec_from_file_location(
    "compare_sources", Path(__file__).resolve().parents[1] / "tools/evidence/compare_sources.py")
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)


def tree(entries):
    return {"truncated": False, "tree": [
        {"path": name, "sha": sha, "mode": mode, "type": "blob"}
        for name, sha, mode in entries]}


class SourceEvidenceTests(unittest.TestCase):
    def test_rejects_incomplete_or_duplicate_tree(self):
        for value in (True, None):
            with self.assertRaises(ValueError):
                module.blob_map({"truncated": value, "tree": []})
        with self.assertRaises(ValueError):
            module.blob_map(tree([("x", "a", "100644"), ("x", "b", "100644")]))

    def test_uncapped_changes_include_deletion_and_mode(self):
        before = tree([(f"a/{i}", "a", "100644") for i in range(350)] +
                      [("removed", "a", "100644"), ("mode", "a", "100644")])
        after = tree([(f"a/{i}", "b", "100644") for i in range(350)] +
                     [("new", "a", "100644"), ("mode", "a", "100755")])
        result = module.compare_trees(before, after)
        self.assertEqual(len(result), 353)
        self.assertTrue(any(r["path"] == "removed" and r["after"] is None for r in result))

    def test_lock_and_upstream_identity_are_independent(self):
        with tempfile.TemporaryDirectory() as d:
            Path(d, "x").write_bytes(b"same")
            sha = hashlib.sha1(b"blob 4\0same").hexdigest()
            lock = {"files": {"x": "incorrect", "missing": "a"}}
            rows = module.compare_lock(d, lock, tree([("prefix/x", sha, "100644")]), "prefix")
            self.assertFalse(rows[1]["matchesLock"])
            self.assertTrue(rows[1]["matchesUpstreamBytes"])
            self.assertFalse(rows[0]["matchesLock"])
            self.assertFalse(rows[0]["presentUpstream"])

    def test_rejects_escape_and_symlink(self):
        with tempfile.TemporaryDirectory() as d:
            for name in ("../x", "/tmp/x"):
                with self.assertRaises(ValueError):
                    module.compare_lock(d, {"files": {name: "a"}}, tree([]))
            Path(d, "link").symlink_to(Path(d).parent / "outside")
            with self.assertRaises(ValueError):
                module.compare_lock(d, {"files": {"link": "a"}}, tree([]))
