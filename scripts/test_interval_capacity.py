#!/usr/bin/env python3
"""Enumerate ordinary Collatz sources independently of the parity-count formulas."""
from test_barrier_kernel import trajectory


def size(b, u):
    return max(u // 2 + 1 - b, 0) + max((u + 2) // 6 - b // 2, 0)


def label(b, u, n):
    if n % 2 == 0:
        return n // 2 - b
    return max(u // 2 + 1 - b, 0) + n // 2 - b // 2


def decode(b, u, r):
    evens = max(u // 2 + 1 - b, 0)
    return 2 * (b + r) if r < evens else 2 * (b // 2 + r - evens) + 1


def size_two(b, u):
    return max(u // 4 + 1 - b, 0) + 2 * max((u + 2) // 6 - b // 2, 0)


def label_two(b, u, n):
    fours = max(u // 4 + 1 - b, 0)
    odds = max((u + 2) // 6 - b // 2, 0)
    if n % 4 == 0:
        return n // 4 - b
    if n % 4 == 2:
        return fours + n // 4 - b // 2
    return fours + odds + n // 2 - b // 2


def decode_two(b, u, r):
    fours = max(u // 4 + 1 - b, 0)
    odds = max((u + 2) // 6 - b // 2, 0)
    if r < fours:
        return 4 * (b + r)
    if r < fours + odds:
        return 4 * (b // 2 + r - fours) + 2
    return 2 * (b // 2 + r - fours - odds) + 1


def main():
    intervals = states = two_states = remainders = cycles = two_cycles = 0
    for b in range(1, 81):
        for u in range(151):
            # Directly apply the map; do not use the parity-band constraints.
            viable = [n for n in range(b, u + 1)
                      if b <= trajectory(n, 1)[-1] <= u]
            count = size(b, u)
            assert count == len(viable), (b, u, count, viable)
            assert sorted(label(b, u, n) for n in viable) == list(range(count))
            assert sorted(decode(b, u, r) for r in range(count)) == viable
            assert all(decode(b, u, label(b, u, n)) == n for n in viable)
            assert all(label(b, u, decode(b, u, r)) == r for r in range(count))
            assert count <= max(u - b, 0) + 1
            viable_two = [n for n in range(b, u + 1)
                          if all(b <= x <= u for x in trajectory(n, 2))]
            count_two = size_two(b, u)
            assert count_two == len(viable_two) <= count
            assert sorted(label_two(b, u, n) for n in viable_two) == list(range(count_two))
            assert sorted(decode_two(b, u, r) for r in range(count_two)) == viable_two
            assert all(decode_two(b, u, label_two(b, u, n)) == n for n in viable_two)
            assert all(label_two(b, u, decode_two(b, u, r)) == r for r in range(count_two))
            if u >= 3 * b + 1:
                assert 6 * count + 9 * b + 3 * (u % 2) + (u + 2) % 6 == (
                    4 * u + 8 + 3 * (b % 2))
                remainders += 1
            if u <= 3 * b:
                assert all(n % 2 == 0 for n in viable)
                assert all(not all(b <= x <= u for x in trajectory(n, 2))
                           for n in range(b, u + 1))
                assert count_two == 0
            for n in viable:
                values = trajectory(n, count + 1)
                if all(b <= x <= u for x in values):
                    # Only the first count+1 points are used for repetition.
                    sources = values[:-1]
                    assert len(sources) == count + 1
                    assert len(set(sources)) < len(sources)
                    cycles += 1
            for n in viable_two:
                values = trajectory(n, count_two + 2)
                if all(b <= x <= u for x in values):
                    sources = values[:-2]
                    assert len(sources) == count_two + 1
                    assert len(set(sources)) < len(sources)
                    two_cycles += 1
            intervals += 1
            states += len(viable)
            two_states += len(viable_two)
    assert cycles > 0 and two_cycles > 0
    assert trajectory(2, size(1, 2)) == [2, 1]  # no repetition without extra endpoint
    assert size(100, 1000) + 1 == 519
    assert size_two(100, 1000) + 2 == 387
    # The 3n+1 count is not transferable to the different 5n+1 map.
    five_count = sum(13 <= trajectory(n, 1, multiplier=5)[-1] <= 416
                     for n in range(13, 417))
    assert five_count != size(13, 416)
    print(f'{intervals} exact counts/bijections, {states} viable states, '
          f'{two_states} two-step viable states, {remainders} remainder identities, '
          f'{cycles}/{two_cycles} accepted one-/two-step cycle prefixes; '
          'endpoint and 5n+1 controls passed')


if __name__ == '__main__':
    main()
