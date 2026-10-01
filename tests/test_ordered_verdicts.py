"""Synthetic control-flow checks; no cryptographic evaluation or search."""
from pathlib import Path
import sys
import time
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'experiments/generic-sha-vector'))
from ordered_verdicts import first_verified


def delayed_verdict(job):
    delay, verdict = job
    time.sleep(delay)
    return int(verdict)


class ObservedSequence:
    def __init__(self, values):
        self.values, self.reads = values, []

    def __len__(self):
        return len(self.values)

    def __getitem__(self, index):
        self.reads.append(index)
        return self.values[index]


class OrderedVerdictTests(unittest.TestCase):
    def test_late_error_does_not_replace_first_acceptance(self):
        for workers in (1, 2, 4):
            self.assertEqual(first_verified(int, ['0', 'invalid'], workers),
                             dict(acceptedIndex=0, derOnly=False))

    def test_earlier_error_is_not_hidden_by_later_acceptance(self):
        for workers in (1, 2):
            with self.assertRaises(ValueError):
                first_verified(int, ['invalid', '0'], workers)

    def test_exhaustion_and_der_only_semantics(self):
        for workers in (1, 2):
            for jobs, expected in [([], False), (['3', '3'], True),
                                   (['3', '1'], False), (['1'], False)]:
                self.assertEqual(first_verified(int, jobs, workers),
                                 dict(acceptedIndex=None, derOnly=expected))

    def test_first_in_input_order_wins_not_first_completion(self):
        jobs = [(0.1, '1'), (0.1, '0'), (0, '0')]
        self.assertEqual(first_verified(delayed_verdict, jobs, 3),
                         dict(acceptedIndex=1, derOnly=False))

    def test_prefetch_is_bounded_and_stops_after_acceptance(self):
        jobs = ObservedSequence(['0', 'invalid', 'invalid', 'invalid'])
        self.assertEqual(first_verified(int, jobs, 2)['acceptedIndex'], 0)
        self.assertEqual(jobs.reads, [0, 1])

    def test_serial_does_not_read_after_acceptance(self):
        jobs = ObservedSequence(['0', 'invalid'])
        first_verified(int, jobs)
        self.assertEqual(jobs.reads, [0])

    def test_invalid_resource_limit(self):
        for workers in (0, -1, 5):
            with self.assertRaises(ValueError):
                first_verified(int, [], workers)
