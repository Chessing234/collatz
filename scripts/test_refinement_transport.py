#!/usr/bin/env python3
"""Independent deterministic arithmetic and dynamics tests, not proof evidence."""
import json
import random
from pathlib import Path
from refinement_atlas import orbit

ROOT = Path(__file__).resolve().parents[1]


def cutoff(t, s, q):
    assert s > 0
    return 0 if t <= q else (t-q-1)//s+1


def main():
    rng = random.Random(20261005)
    arithmetic = 0
    for _ in range(100000):
        t, q, v, m = (rng.randrange(10**20) for _ in range(4))
        s, u = rng.randrange(1, 10**6), rng.randrange(1, 10**6)
        c = cutoff(t, s, q)
        assert (t <= s*m+q) == (c <= m)
        assert (c == 0) == (t <= q)
        assert cutoff(c, u, v) == cutoff(t, s*u, s*v+q)
        assert t <= s*c+q
        if c:
            assert s*(c-1)+q < t
        arithmetic += 1
    histogram = 0
    for _ in range(10000):
        t, s = rng.randrange(10**12), rng.randrange(1, 129)
        values = [cutoff(t, s, q) for q in range(s)]
        assert sum(values) == t
        assert max(values)-min(values) <= 1
        assert all(c == t//s + (q < t%s) for q, c in enumerate(values))
        histogram += 1
    returns = 0
    for modulus in range(1, 65):
        for K in range(1, 33):
            n = 2**K*(2*modulus)-1
            assert n > 1
            for j in range(1, K+1):
                _, value = orbit(n, j)
                assert value+1 == 3**j*2**(K-j)*2*modulus
                assert value > n and value % modulus == n % modulus
                returns += 1
    census = []
    for k in range(1, 19):
        contracting = exceptional = max_cutoff = 0
        maximizers = []
        for r in range(1, 2**k):
            a, b = orbit(r, k)
            gap = 2**k-3**a
            if gap <= 0:
                continue
            t = 0 if b < r else (b-r)//gap+1
            contracting += 1
            exceptional += t > 0
            if t > max_cutoff:
                max_cutoff, maximizers = t, [r]
            elif t == max_cutoff and t > 0:
                maximizers.append(r)
        census.append(dict(depth=k, contracting=contracting,
                           exceptional=exceptional, max_cutoff=max_cutoff,
                           exceptional_representatives=maximizers))
    report = dict(seed=20261005, arithmetic_tests=arithmetic, histogram_tests=histogram,
                  simultaneous_return_tests=returns, canonical_census=census,
                  status='experimental; these tests are not used as Lean hypotheses')
    path = ROOT/'Collatz/Research/RefinementAtlas/experiments.json'
    path.write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps({k: report[k] for k in ('arithmetic_tests','histogram_tests','simultaneous_return_tests')}))


if __name__ == '__main__':
    main()
