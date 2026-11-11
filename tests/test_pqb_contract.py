"""pqb-ranked-v1 range vectors and the partition they describe. No CUDA or credentials."""
import json
import sys
import unittest
from math import comb
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'worker/pqb'))
import pqb_ranges as ranges  # noqa: E402


class PqbRangeContractTest(unittest.TestCase):
    def test_published_contract(self):
        vectors = json.loads((ROOT / 'contracts/pqb-ranked-v1.json').read_text())
        self.assertEqual(vectors['searchVersion'], ranges.VERSION)
        self.assertNotEqual(ranges.VERSION, 'ranked-v2')
        for case in vectors['cases']:
            with self.subTest(case=case):
                self.assertEqual(ranges.work_range(case['stage'], case['attempt']), case['range'])
        for case in vectors['invalid']:
            with self.subTest(case=case), self.assertRaises(ValueError):
                ranges.work_range(case['stage'], case['attempt'])

    def test_round_units_tile_every_subset_once(self):
        for stage, (n, t) in ranges.ROUNDS.items():
            position = 0
            for attempt in range(ranges.unit_count(stage)):
                unit = ranges.work_range(stage, attempt)
                self.assertEqual(int(unit['start']), position)
                self.assertGreater(unit['count'], 0)
                position += unit['count']
            self.assertEqual(position, comb(n, t))
            with self.assertRaises(ValueError):
                ranges.work_range(stage, ranges.unit_count(stage))

    def test_pinning_units_cover_the_usable_nonces(self):
        last = ranges.work_range('pinning', ranges.unit_count('pinning') - 1)
        self.assertEqual(last['sequence'] + last['sequenceCount'] - 1, 0xFFFFFFFD)
        self.assertEqual(int(last['start']) + last['count'], ranges.SEQ_COUNT * ranges.LT_SPAN)
        first = ranges.work_range('pinning', 0)
        self.assertEqual((first['sequence'], first['locktime'], first['locktimeCount']),
                         (0x80000000, 500000000, 1200000000))

    def test_a_prefix_range_is_a_contiguous_subset_range(self):
        # brute force on a small table: prefixes in lexicographic order own consecutive subsets
        from itertools import combinations
        n, t = 9, 4
        subsets = list(combinations(range(n), t))
        prefixes = list(combinations(range(n - 1), t - 1))
        saved = dict(ranges.ROUNDS)
        ranges.ROUNDS['tiny'] = (n, t)
        try:
            for rank, prefix in enumerate(prefixes):
                first = ranges.subset_rank_of_prefix('tiny', rank)
                owned = [s for s in subsets if s[:-1] == prefix]
                self.assertEqual(subsets[first:first + len(owned)], owned)
                self.assertEqual(ranges.subset_rank_of_prefix('tiny', rank + 1), first + len(owned))
        finally:
            ranges.ROUNDS.clear()
            ranges.ROUNDS.update(saved)


if __name__ == '__main__':
    unittest.main()
