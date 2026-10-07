#!/usr/bin/env python3
"""Independent scalar trajectories, affine-family sharpness, and sign controls."""
from collections import Counter
from test_barrier_kernel import trajectory


def main():
    hits = Counter()
    finite_survivors = 0
    for m in range(2, 200001):
        values = trajectory(m, 8)
        if min(values) >= m:
            assert 4*values[5] == 27*m+19 or 16*values[8] == 81*m+85
            first = next((k for k, n in enumerate(values) if 16*n >= 81*m+85), None)
            assert first is not None, (m, values)
            assert max(values) > 5*m
            hits[first] += 1
            finite_survivors += 1
        assert not all(m <= n <= 5*m for n in values)
    samples = list(range(4096)) + [2**64, 2**128, 10**100]
    for q in samples:
        m = 32*q+27
        values = trajectory(m, 8)
        expected = [m, 96*q+82, 48*q+41, 144*q+124, 72*q+62,
                    36*q+31, 108*q+94, 54*q+47, 162*q+142]
        assert values == expected
        assert min(values) >= m
        assert 16*values[8] == 81*m+85
        assert all(16*n < 81*m+85 for n in values[:8])
        assert all(16*n < 81*m+86 for n in values)
    # Test the arbitrary-start band-exit corollary by direct scalar evaluation.
    exits = Counter()
    band_tests = 0
    for b in range(2, 251):
        for start in range(b, 5*b+1):
            n = start
            seen = set()
            steps = 0
            while b <= n <= 5*b:
                assert n not in seen, (b, start, n)
                seen.add(n)
                n = n//2 if n % 2 == 0 else 3*n+1
                steps += 1
            exits[steps] += 1
            band_tests += 1
    assert finite_survivors > 0 and hits[8] > 0
    # The m>1 hypothesis is essential: the ordinary trivial cycle stays in [1,5].
    assert all(1 <= n <= 5 for n in trajectory(1, 100))
    assert max(16*n for n in trajectory(1, 8)) < 81+85
    # 3n-1 has an actual nontrivial cycle wholly inside [5,25]. The +1 map matters.
    n = 5
    minus_values = [n]
    for _ in range(100):
        n = n//2 if n % 2 == 0 else 3*n-1
        minus_values.append(n)
    assert minus_values[:6] == [5, 14, 7, 20, 10, 5]
    assert all(5 <= n <= 25 for n in minus_values)
    assert 16*max(minus_values) < 81*5+85
    print(f'199999 ordinary starts; {finite_survivors} eight-step survivors; '
          f'exact dichotomy and hit times {dict(sorted(hits.items()))}; '
          f'{len(samples)} sharp-family samples; '
          f'{band_tests} arbitrary-start exits (maximum observed {max(exits)} steps); '
          'trivial-cycle and 3n-1 controls passed')


if __name__ == '__main__':
    main()
