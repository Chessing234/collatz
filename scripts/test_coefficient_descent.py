#!/usr/bin/env python3
"""Independent direct-orbit tests for certificates and the transfer theorem.

These tests do not replace Lean proofs. The direct oracle compares orbit
values with the input; it never uses coefficient inequalities to choose a stop.
"""
from __future__ import annotations

from collections import Counter
import json
import random
import unittest

from coefficient_descent import BOUND, HORIZON, REPORT, crossing, gap_bound, generated
from descent_intervals import exact_interval, trace

COUNTS: Counter = Counter()


def direct_stop(n: int, limit: int) -> tuple[int | None, int]:
    state = n
    for k in range(1, limit + 1):
        state = (3 * state + 1) // 2 if state % 2 else state // 2
        if state < n:
            return k, state
    return None, state


def first_light(n: int, k: int) -> bool:
    _, counts = trace(n, k)
    return (3 ** counts[-1] < 2 ** k and
            all(2 ** j <= 3 ** counts[j] for j in range(k)))


def cutoff(k: int, r: int) -> int:
    return sum(trace(r, k)[0]) + 1


class CoefficientDescentTests(unittest.TestCase):
    def test_all_small_inputs(self) -> None:
        for n in range(2, BOUND):
            row = crossing(n)
            self.assertEqual(direct_stop(n, row['k']), (row['k'], row['endpoint']))
            self.assertTrue(first_light(n, row['k']))
            COUNTS['small_input_oracles'] += 1

    def test_gap_bound_and_minimality(self) -> None:
        self.assertEqual(gap_bound(HORIZON)[0], BOUND)
        for k in range(HORIZON + 1):
            for a in range(k + 1):
                if 3 ** a < 2 ** k:
                    self.assertLess(a * 3 ** a, 3 * (2 ** k - 3 ** a) * BOUND)
                COUNTS['gap_pairs'] += 1
        self.assertGreaterEqual(147 * 3 ** 147, 3 * (2 ** 233 - 3 ** 147) * (BOUND - 1))

    def test_infinite_ray_samples(self) -> None:
        _, manifest = generated()
        for row in manifest['rows']:
            for m in [0, 1, 7, 2 ** 128 + 3]:
                n = 2 ** row['k'] * m + row['n']
                k, endpoint = direct_stop(n, row['k'])
                self.assertEqual(k, row['k'])
                self.assertEqual(endpoint, 3 ** row['odd_count'] * m + row['endpoint'])
                COUNTS['ray_samples'] += 1

    def test_manifest_partition(self) -> None:
        _, manifest = generated()
        expected = 3
        observed = []
        for batch in manifest['batches']:
            self.assertEqual(batch['lo'], expected)
            self.assertEqual(batch['rows'], (batch['hi'] - batch['lo']) // 2)
            observed.extend(range(batch['lo'], batch['hi'], 2))
            expected = batch['hi']
        self.assertEqual(expected, BOUND)
        self.assertEqual(observed, list(range(3, BOUND, 2)))
        self.assertEqual(len(set(observed)), len(observed))
        self.assertEqual(manifest['max_witness_time'], 81)

    def test_effective_transfer(self) -> None:
        for k in range(10):
            for r in range(2 ** k + 4):
                boundary = cutoff(k, r)
                for m in [boundary, boundary + 1, 10 ** 40 + boundary]:
                    n = 2 ** k * m + r
                    self.assertEqual(direct_stop(n, k)[0] == k, first_light(r, k))
                    self.assertEqual(exact_interval(k, r).contains(m), first_light(r, k))
                    COUNTS['transfer_cases'] += 1

    def test_interval_upward_closure(self) -> None:
        rng = random.Random(20261006)
        for _ in range(2500):
            k = rng.randrange(1, HORIZON + 1)
            r = rng.getrandbits(k + 2)
            interval = exact_interval(k, r)
            self.assertNotEqual(interval.kind, 'finite')
            for m in [0, 1, 4, 2 ** 100]:
                if interval.contains(m):
                    self.assertTrue(interval.contains(m + 1))
                    self.assertTrue(first_light(r, k))
            COUNTS['random_intervals'] += 1

    def test_no_uniform_horizon(self) -> None:
        n = 2 ** (HORIZON + 1) - 1
        states, counts = trace(n, HORIZON)
        self.assertTrue(all(n <= state for state in states))
        self.assertTrue(all(2 ** k <= 3 ** counts[k] for k in range(HORIZON + 1)))
        self.assertEqual(direct_stop(n, HORIZON)[0], None)
        COUNTS['mersenne_prefixes'] += len(states)

    def test_boundaries_and_invalid_inputs(self) -> None:
        for invalid in [0, 1, -3, True, 2.5]:
            with self.assertRaises(ValueError):
                crossing(invalid)
        with self.assertRaises(RuntimeError):
            crossing(27, limit=58)
        self.assertEqual(crossing(27)['k'], 59)
        self.assertEqual(crossing(4591)['k'], 65)
        self.assertFalse(first_light(1, 1))
        self.assertTrue(first_light(1, 2))
        self.assertEqual(direct_stop(1, HORIZON)[0], None)
        self.assertEqual(exact_interval(1, 0).lower, 1)
        self.assertEqual(exact_interval(2, 1).lower, 1)


def main() -> None:
    suite = unittest.defaultTestLoader.loadTestsFromTestCase(CoefficientDescentTests)
    result = unittest.TextTestRunner(verbosity=2).run(suite)
    report = {'status': 'passed' if result.wasSuccessful() else 'failed',
              'test_methods': result.testsRun, 'checks': dict(COUNTS),
              'counted_checks': sum(COUNTS.values()),
              'failures': len(result.failures), 'errors': len(result.errors),
              'scope': 'Exact-integer experiments; the general statements are proved separately in Lean.'}
    REPORT.mkdir(parents=True, exist_ok=True)
    (REPORT / 'python-tests.json').write_text(json.dumps(report, indent=2) + '\n')
    if not result.wasSuccessful():
        raise SystemExit(1)


if __name__ == '__main__':
    main()
