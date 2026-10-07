#!/usr/bin/env python3
"""Independent prefix enumeration for anchored barriers and interval certificates."""
from itertools import product


def trajectory(n, length, multiplier=3):
    values = [n]
    for _ in range(length):
        n = n // 2 if n % 2 == 0 else multiplier * n + 1
        values.append(n)
    return values


def test_windows():
    checks = 0
    for n, b, j, k in product(range(81), range(12), range(8), range(8)):
        values = trajectory(n, j + k)
        whole = min(values) >= b
        split = min(values[:j + 1]) >= b and min(values[j:]) >= b
        assert whole == split, (n, b, j, k)
        # Budget-preserving shift has the same anchor, not values[j].
        if whole:
            assert min(trajectory(values[j], k)) >= b
        checks += 1
    return checks


def test_cycles():
    checks = accepted = 0
    for b, u in product(range(12), range(12)):
        for n in range(24):
            # Natural subtraction agrees with the Lean checker, even b>u.
            budget = max(u - b, 0) + 1
            values = trajectory(n, budget)
            if all(b <= value <= u for value in values):
                seen = {}
                for j, value in enumerate(values):
                    if value in seen:
                        i = seen[value]
                        assert i < j <= budget
                        assert trajectory(value, j - i)[-1] == value
                        break
                    seen[value] = j
                else:
                    raise AssertionError((b, u, n, values))
                accepted += 1
            checks += 1
    assert accepted > 0
    return checks, accepted


def test_negative_controls():
    # Resetting the barrier fails; keeping it fixed works.
    assert min(trajectory(3, 1)) >= 3
    assert min(trajectory(10, 1)) < 10
    assert min(trajectory(10, 1)) >= 3
    # Insufficient budget: an accepted prefix can have no repetition.
    short = trajectory(3, 1)
    assert min(short) >= 3 and max(short) <= 10
    assert len(set(short)) == len(short)
    assert not all(3 <= x <= 10 for x in trajectory(3, 8))
    # The same structural argument allows a genuine nontrivial 5n+1 cycle.
    # This prevents treating the invariant-kernel reduction as convergence.
    cycle = trajectory(13, 10, multiplier=5)
    assert cycle == [13, 66, 33, 166, 83, 416, 208, 104, 52, 26, 13]
    long = trajectory(13, 416 - 13 + 1, multiplier=5)
    assert all(13 <= x <= 416 for x in long)
    assert 1 not in long


if __name__ == '__main__':
    windows = test_windows()
    intervals, accepted = test_cycles()
    test_negative_controls()
    print(f'{windows} split-window checks; {intervals} interval checks '
          f'({accepted} accepted); moving-barrier, short-prefix, and 5n+1 controls passed')
