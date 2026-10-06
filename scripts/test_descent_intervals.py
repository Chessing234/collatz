#!/usr/bin/env python3
"""Independent dynamics, boundary, refinement, and cycle checks.

The direct dynamics oracle never calls the interval classifier or its trace.
Python checks are experiments; the Lean equivalents carry infinite scope.
"""
from collections import Counter
from itertools import product
import json
from pathlib import Path
import random
import unittest

from descent_intervals import (
    Interval, REPORT, census, cutoff, exact_interval, pullback, solve_le, trace,
)

COUNTS = Counter()


def direct_states(n, depth):
    values = [n]
    for _ in range(depth):
        if n & 1:
            n = 3 * n + 1
        n //= 2
        values.append(n)
    return values


def direct_first(n, depth):
    values = direct_states(n, depth)
    return depth > 0 and values[-1] < n and all(v >= n for v in values[:-1])


class IntervalTests(unittest.TestCase):
    def test_exhaustive_affine_arithmetic(self):
        for a, b, c, d in product(range(6), repeat=4):
            result = solve_le(a, b, c, d)
            for m in range(16):
                self.assertEqual(result.contains(m), a*m+b <= c*m+d, (a, b, c, d, m))
                COUNTS["affine_cases"] += 1

    def test_large_integer_boundaries(self):
        rng = random.Random(20261006)
        for _ in range(1000):
            a, b, c, d = (rng.randrange(10**50) for _ in range(4))
            result = solve_le(a, b, c, d)
            points = {0, 1, 10**80, result.lower, max(0, result.lower-1), result.lower+1}
            if result.upper is not None:
                points.update({result.upper, max(0, result.upper-1), result.upper+1})
            for m in points:
                self.assertEqual(result.contains(m), a*m+b <= c*m+d)
                COUNTS["large_affine_cases"] += 1

    def test_intersection(self):
        rng = random.Random(17)
        for _ in range(3000):
            first = Interval(rng.randrange(20), rng.choice([None, rng.randrange(20)]))
            second = Interval(rng.randrange(20), rng.choice([None, rng.randrange(20)]))
            m = rng.randrange(25)
            self.assertEqual(first.intersect(second).contains(m), first.contains(m) and second.contains(m))
            COUNTS["intersection_cases"] += 1

    def test_refinement_and_composition(self):
        rng = random.Random(31)
        for _ in range(10000):
            interval = Interval(rng.randrange(100), rng.choice([None, rng.randrange(150)]))
            s, u = rng.randrange(1, 50), rng.randrange(1, 50)
            q, v, m = (rng.randrange(150) for _ in range(3))
            self.assertEqual(pullback(interval, s, q).contains(m), interval.contains(s*m+q))
            self.assertEqual(pullback(pullback(interval, s, q), u, v),
                             pullback(interval, s*u, s*v+q))
            COUNTS["refinement_cases"] += 1

    def test_refinement_conserves_finite_cardinality(self):
        for lower in range(20):
            for upper in range(30):
                interval = Interval(lower, upper)
                for scale in range(1, 10):
                    children = [pullback(interval, scale, q) for q in range(scale)]
                    total = sum(max(0, child.upper-child.lower) for child in children)
                    self.assertEqual(total, max(0, upper-lower))
                    COUNTS["finite_cardinality_cases"] += 1

    def test_full_census_against_dynamics(self):
        for row in census(12):
            k, r = row["depth"], row["residue"]
            interval = Interval(row["lower"], row["upper"])
            for m in (0, 1, 2, 3, 10, 9999, 10**60):
                n = (1 << k)*m+r
                self.assertEqual(interval.contains(m), direct_first(n, k), (k, r, m))
                self.assertEqual(direct_states(n, k)[-1], 3**row["odd_count"]*m+row["endpoint"])
                COUNTS["cylinder_dynamics_cases"] += 1

    def test_noncanonical_representatives(self):
        rng = random.Random(71)
        for _ in range(2000):
            k, r, m = rng.randrange(1, 80), rng.randrange(1, 10**10), rng.randrange(10**20)
            self.assertEqual(exact_interval(k, r).contains(m), direct_first((1 << k)*m+r, k))
            COUNTS["noncanonical_cases"] += 1

    def test_long_known_first_times(self):
        for n, k in ((3, 4), (7, 7), (27, 59), (4591, 65), (1, 2), (0, 1)):
            for m in (0, 1, 13, 10**100):
                self.assertEqual(exact_interval(k, n).contains(m), direct_first((1 << k)*m+n, k))
                COUNTS["long_ray_cases"] += 1

    def test_zero_depth(self):
        for n in range(100):
            for m in range(5):
                self.assertFalse(exact_interval(0, n).contains(m))
                self.assertFalse(direct_first(n+m, 0))

    def test_orbit_trace_independent(self):
        for n in range(1000):
            values, counts = trace(n, 40)
            self.assertEqual(values, direct_states(n, 40))
            self.assertEqual(counts[-1], sum(v % 2 for v in values[:-1]))
            COUNTS["trace_cases"] += 1

    def test_canonical_decomposition(self):
        rng = random.Random(13)
        for _ in range(3000):
            n, k = rng.randrange(10**40), rng.randrange(1, 80)
            m, r = divmod(n, 1 << k)
            self.assertEqual(exact_interval(k, r).contains(m), direct_first(n, k))
            COUNTS["canonical_cases"] += 1

    def test_finite_depth_obstruction(self):
        for maximum in range(1, 100):
            n = (1 << maximum)*2-1
            for k in range(maximum+1):
                m, r = divmod(n, 1 << k)
                self.assertFalse(exact_interval(k, r).contains(m))
                self.assertFalse(direct_first(n, k))
                COUNTS["obstruction_cases"] += 1

    def test_cycle_intervals(self):
        for k in range(1, 10):
            for r in range(1 << k):
                states, counts = trace(r, k)
                a, p, b = 3**counts[-1], 1 << k, states[-1]
                interval = solve_le(a, b, p, r).intersect(solve_le(p, r, a, b))
                hits = []
                for m in range(8):
                    self.assertEqual(interval.contains(m), direct_states(p*m+r, k)[-1] == p*m+r)
                    if interval.contains(m):
                        hits.append(m)
                    COUNTS["cycle_cases"] += 1
                self.assertLessEqual(len(hits), 1)

    def test_late_endpoint_is_not_first(self):
        self.assertLess(direct_states(3, 5)[-1], 3)
        self.assertFalse(direct_first(3, 5))
        self.assertFalse(exact_interval(5, 3).contains(0))

    def test_bad_inputs(self):
        for args in ((-1, 0, 0, 0), (0, -1, 0, 0), (True, 0, 0, 0)):
            with self.assertRaises(ValueError):
                solve_le(*args)
        with self.assertRaises(ValueError):
            exact_interval(-1, 0)
        with self.assertRaises(ValueError):
            cutoff(1, 0, 0)

    def test_census_is_complete_and_unique(self):
        rows = census(9)
        pairs = {(row["depth"], row["residue"]) for row in rows}
        self.assertEqual(len(pairs), 1022)
        self.assertEqual(pairs, {(k, r) for k in range(1, 10) for r in range(1 << k)})


def main():
    suite = unittest.defaultTestLoader.loadTestsFromTestCase(IntervalTests)
    result = unittest.TextTestRunner(verbosity=2).run(suite)
    report = {"status": "passed" if result.wasSuccessful() else "failed",
              "test_methods": result.testsRun, "case_counts": dict(sorted(COUNTS.items())),
              "scope": "Python experiment, not a substitute for Lean kernel checking"}
    REPORT.mkdir(parents=True, exist_ok=True)
    (REPORT / "python-tests.json").write_text(json.dumps(report, indent=2) + "\n")
    raise SystemExit(0 if result.wasSuccessful() else 1)


if __name__ == "__main__":
    main()
