#!/usr/bin/env python3
"""Independent orbit tests for finite populations and first-descent transport.

Counts include multiplicity of inputs. Fixed-time populations use half-open
intervals including zero; stopping-time experiments use [2,N] and explicitly
record unresolved inputs. No finite experiment asserts universal descent.
"""
import argparse
import json
import random
from collections import Counter, defaultdict
from fractions import Fraction
from pathlib import Path


def step(n: int) -> int:
    return n // 2 if n % 2 == 0 else (3 * n + 1) // 2


def orbit(n: int, k: int) -> int:
    for _ in range(k):
        n = step(n)
    return n


def closed_counts(k: int) -> list[int]:
    return [1, 2**k - (k % 2), 2**(k + 1) - (1 - k % 2)]


def population_probe(depth: int) -> dict:
    census = []
    total = 0
    for k in range(depth + 1):
        size = 3 * 2**k
        counts = Counter(orbit(n, k) % 3 for n in range(size))
        actual = [counts[r] for r in range(3)]
        assert actual == closed_counts(k), (k, actual)
        assert sum(actual) == size
        if k:
            previous = census[-1]['counts']
            assert actual == [previous[0], previous[2], 3 * 2**(k - 1) + previous[1]]
        total += size
        census.append({'depth': k, 'input_period': size, 'counts': actual})
    rng = random.Random(20261005)
    shifts = 0
    for k in range(65):
        size = 3 * 2**k
        for _ in range(32):
            n = rng.randrange(10**40)
            q = rng.randrange(10**40)
            assert orbit(size * q + n, k) % 3 == orbit(n, k) % 3
            shifts += 1
            d = rng.randrange(1, 10**40)
            if d % size:
                assert orbit(d, k) % 3 != orbit(0, k) % 3
                shifts += 1
    windows = 0
    for k in range(9):
        size = 3 * 2**k
        for cutoff in (0, 1, size - 1, size, size + 1, 3 * size - 1, 3 * size + 1):
            q, remainder = divmod(cutoff, size)
            actual = Counter(orbit(n, k) % 3 for n in range(cutoff))
            partial = Counter(orbit(n, k) % 3 for n in range(remainder))
            for r in range(3):
                expected = q * closed_counts(k)[r] + partial[r]
                assert actual[r] == expected
                assert q * closed_counts(k)[r] <= actual[r] <= (q + 1) * closed_counts(k)[r]
                windows += 1
    return {'complete_periods': census, 'input_orbit_checks': total,
            'large_integer_period_checks': shifts, 'window_checks': windows}


def first_descent_probe(limit: int, fuel: int) -> dict:
    landed = Counter()
    sources = defaultdict(Counter)
    times = Counter()
    unresolved = []
    best_ratio = Fraction(0)
    best = None
    steps = 0
    for n in range(2, limit + 1):
        current = n
        for k in range(1, fuel + 1):
            previous = current
            current = step(current)
            steps += 1
            if current < n:
                assert previous >= n and previous % 2 == 0
                assert (k == 1) == (n % 2 == 0)
                assert (k == 2) == (n % 4 == 1)
                assert k != 3
                assert n <= 2 * current < 2 * n
                assert (2 * current == n) == (n % 2 == 0)
                assert (current % 3 == 0) == (n % 6 == 0)
                if current % 3 == 0:
                    assert k == 1
                if k > 1:
                    assert current % 3 != 0
                landed[current % 3] += 1
                sources[n % 3][current % 3] += 1
                times[k] += 1
                ratio = Fraction(current, n)
                if ratio > best_ratio:
                    best_ratio = ratio
                    best = {'input': n, 'landing': current, 'stopping_time': k,
                            'ratio_exact': [ratio.numerator, ratio.denominator]}
                break
        else:
            unresolved.append(n)
    assert times[1] == limit // 2
    assert times[2] == (limit - 1) // 4
    assert times[3] == 0
    assert landed[0] == limit // 6
    assert sum(landed.values()) + len(unresolved) == limit - 1
    return {'input_interval_inclusive': [2, limit], 'fuel': fuel,
            'orbit_steps': steps, 'landing_residue_counts': [landed[r] for r in range(3)],
            'source_to_landing_counts': {str(r): [sources[r][s] for s in range(3)] for r in range(3)},
            'stopping_time_counts': dict(sorted(times.items())),
            'unresolved_inputs': unresolved, 'weakest_observed_drop': best}



def exact_first(n: int, k: int) -> bool:
    if k == 0:
        return False
    current = n
    for j in range(1, k + 1):
        current = step(current)
        if current < n:
            return j == k
    return False


def class_probe(depth: int = 11) -> dict:
    certified = rejected = ray_checks = interval_checks = 0
    census = []
    for k in range(1, depth + 1):
        size = 2**k
        per_depth = 0
        for r in range(size):
            current = r
            odds = 0
            prefix = []
            for j in range(k):
                prefix.append((j, odds, current))
                odds += current % 2
                current = step(current)
            certificate = exact_first(r, k) and 3**odds < size and all(
                2**j <= 3**a for j, a, _ in prefix)
            values = []
            for m in (0, 1, 2, 3, 4, 5, 6):
                first = exact_first(size * m + r, k)
                values.append(first)
                if certificate:
                    assert first, (k, r, m)
                ray_checks += 1
            # A true-false-true pattern would contradict interval convexity.
            successes = [m for m, ok in enumerate(values) if ok]
            if successes:
                assert all(values[m] for m in range(min(successes), max(successes) + 1))
            interval_checks += 1
            if certificate:
                certified += 1
                per_depth += 1
                for m in (17, 1024, 10**30 + 1):
                    assert exact_first(size * m + r, k), (k, r, m)
                    assert orbit(size * m + r, k) == 3**odds * m + current
                    ray_checks += 1
            else:
                rejected += 1
                if not exact_first(r, k):
                    witness = 0
                elif 3**odds >= size:
                    witness = r + 1
                else:
                    bad = [(j, value) for j, a, value in prefix if 3**a < 2**j]
                    assert bad, (k, r)
                    witness = bad[0][1] + 1
                assert not exact_first(size * witness + r, k), (k, r, witness)
                ray_checks += 1
        census.append({'depth': k, 'certified_complete_classes': per_depth})
    for m in (0, 1, 2, 17, 1024, 10**40 + 1):
        n = 2**65 * m + 4591
        assert exact_first(n, 65)
        endpoint = orbit(n, 65)
        assert endpoint == 3**41 * m + 4541
        assert 49 * n < 50 * endpoint < 50 * n
        ray_checks += 1
    return {'depth_inclusive': depth, 'certified_classes': certified,
            'rejected_classes_with_explicit_failure_witness': rejected,
            'ray_checks': ray_checks, 'interval_convexity_checks': interval_checks,
            'census': census}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--depth', type=int, default=14)
    parser.add_argument('--limit', type=int, default=200000)
    parser.add_argument('--fuel', type=int, default=1000)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    assert args.depth >= 0 and args.limit >= 2 and args.fuel >= 1
    result = {'population': population_probe(args.depth),
              'first_descent': first_descent_probe(args.limit, args.fuel),
              'complete_classes': class_probe(),
              'status': 'passed', 'scope': 'finite regression, not universal descent'}
    text = json.dumps(result, indent=2) + '\n'
    if args.output:
        args.output.write_text(text)
    print(text, end='')


if __name__ == '__main__':
    main()
