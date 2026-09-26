import importlib.util
import math
from pathlib import Path
import random
import unittest

ROOT = Path(__file__).resolve().parents[1]
def module(name, path):
    spec = importlib.util.spec_from_file_location(name, ROOT/path)
    value = importlib.util.module_from_spec(spec); spec.loader.exec_module(value)
    return value
check = module('candidate_range', 'worker/promotion/validation/candidate_range.py')
ranges = module('search_ranges', 'worker/search_ranges.py')
audit = module('edge_audit', 'worker/promotion/validation/run_edge_audit.py')


class Membership(unittest.TestCase):
    def test_all_range_edges_and_sampled_ranks(self):
        total = math.comb(150,9); rng = random.Random(20260925)
        ranks = [0,1,total-2,total-1] + [rng.randrange(total) for _ in range(1000)]
        ranks += [r for a in range((total+ranges.CHUNK-1)//ranges.CHUNK)
                  for r in (a*ranges.CHUNK,min(total-1,(a+1)*ranges.CHUNK-1))]
        for rank in ranks:
            indices = audit.unrank(rank)
            self.assertEqual(check.subset_rank(indices),rank)
            line = 'indices=' + ','.join(map(str,indices)) + '\n'
            self.assertEqual(check.validate_candidates_in_range('round1',[line],ranges.work_range('round1',rank//ranges.CHUNK)),1)

    def test_pin_exclusive_boundaries(self):
        unit = ranges.work_range('pinning',18); lo=unit['sequence']; lt=unit['locktime']; end=lt+unit['count']//16
        for sequence, locktime, valid in [(lo,lt,True),(lo+15,end-1,True),(lo-1,lt,False),(lo+16,lt,False),(lo,end,False),(lo,lt-1,False)]:
            candidate = f'sequence={sequence}\nlocktime={locktime}\n'
            if valid:self.assertEqual(check.validate_candidates_in_range('pinning',[candidate],unit),1)
            else:
                with self.assertRaises(ValueError):check.validate_candidates_in_range('pinning',[candidate],unit)

    def test_subset_outside_assigned_range(self):
        for stage in ('round1','round2'):
            with self.assertRaises(ValueError):
                check.validate_candidates_in_range(stage,['indices=0,1,2,3,4,5,6,7,8\n'],ranges.work_range(stage,1))

    def test_malformed_records(self):
        unit=ranges.work_range('round1',0)
        for candidates in ([''],['indices=0,1,2,3,4,5,6,7,7'],['indices=0,1,2,3,4,5,6,8,7'],['indices=0,1,2,3,4,5,6,7,150'],['sequence=1'],['x'*16384],[None], 'not-a-list', ['x']*33):
            with self.assertRaises(ValueError):check.validate_candidates_in_range('round1',candidates,unit)

    def test_all_records_checked(self):
        unit=ranges.work_range('pinning',0); good='sequence=2147483648\nlocktime=500000000\n'
        self.assertEqual(check.validate_candidates_in_range('pinning',[good+good],unit),2)
        with self.assertRaises(ValueError):check.validate_candidates_in_range('pinning',[good+'sequence=1\nlocktime=500000000\n'],unit)

    def test_no_candidates_grants_no_solution(self):
        self.assertEqual(check.validate_candidates_in_range('pinning',[],ranges.work_range('pinning',0)),0)

if __name__=='__main__':unittest.main()
