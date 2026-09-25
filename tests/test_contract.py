"""Shared published protocol vectors; no CUDA or credentials required."""
import json
import sys
import unittest
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "worker"))
from search_ranges import VERSION, work_range

class RangeContractTest(unittest.TestCase):
    def test_published_contract(self):
        vectors = json.loads((ROOT / "contracts/ranked-v2.json").read_text())
        self.assertEqual(vectors["searchVersion"], VERSION)
        for case in vectors["cases"]:
            with self.subTest(case=case):
                self.assertEqual(work_range(case["stage"], case["attempt"]), case["range"])
        for case in vectors["invalid"]:
            with self.subTest(case=case), self.assertRaises(ValueError):
                work_range(case["stage"], case["attempt"])

if __name__ == "__main__":
    unittest.main()
