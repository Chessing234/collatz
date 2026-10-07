#!/usr/bin/env python3
"""Direct scalar exits, bounded-window frequency, and essential-hypothesis controls."""
from collections import Counter
import random
from test_barrier_kernel import trajectory


def exit_time(b, start):
    n = start
    for k in range(13):
        if n < b or 5*b < n:
            return k
        n = n//2 if n % 2 == 0 else 3*n+1
    raise AssertionError((b, start, 'accepted 12-step corridor'))


def main():
    exits = Counter()
    exhaustive = large = windows = blocks = 0
    for b in range(2, 501):
        for n in range(5*b+3):
            exits[exit_time(b, n)] += 1
            exhaustive += 1
    # Independently check the stronger relation: 3n+1 is allowed at even sources.
    relaxed = 0
    for b in range(2, 101):
        for start in range(b, 5*b+1):
            states = {start}
            for _ in range(12):
                next_states = set()
                for n in states:
                    options = [3*n+1] + ([n//2] if n % 2 == 0 else [])
                    next_states.update(m for m in options if b <= m <= 5*b)
                states = next_states
            assert not states, (b, start, states)
            relaxed += 1
    rng = random.Random(73017)
    for _ in range(10000):
        b = rng.randrange(2, 10**120)
        for n in (0, b, 2*b, 5*b, 5*b+1, rng.randrange(b, 5*b+1)):
            exits[exit_time(b, n)] += 1
            large += 1
    assert max(exits) == 12
    sharp = trajectory(114, 12)
    assert sharp == [114, 57, 172, 86, 43, 130, 65, 196, 98, 49, 148, 74, 37]
    assert all(40 <= n <= 200 for n in sharp[:-1]) and sharp[-1] < 40
    seeds = list(range(2, 2002)) + [2**90-1, 2**180-1]
    for seed in seeds:
        values = trajectory(seed, 511)
        for b in sorted({2, max(2, seed//5), max(2, seed//2), seed}):
            end = next((i for i, n in enumerate(values) if n < b), len(values))
            prefix = values[:end]
            # Finite lower survival supplies the frequency premise in each window.
            for t in range(max(0, len(prefix)-12)):
                assert any(n > 5*b for n in prefix[t:t+13]), (seed, b, t)
                windows += 1
            witnesses = []
            for q in range(len(prefix)//13):
                s = next(i for i in range(13*q, 13*q+13) if prefix[i] > 5*b)
                witnesses.append(s)
                blocks += 1
            assert all(a < c for a, c in zip(witnesses, witnesses[1:]))
            assert sum(n > 5*b for n in prefix[:13*len(witnesses)]) >= len(witnesses)
    # Anchor 1 supports the ordinary trivial cycle; it cannot use the clock theorem.
    assert all(1 <= n <= 5 for n in trajectory(1, 100))
    # Keeping only initial positivity/lower survival does not imply a later high visit.
    assert max(trajectory(2, 12)) <= 10
    # The changed map 3n-1 defeats both uniform exit and conditional high frequency.
    n = 5
    minus = [n]
    for _ in range(100):
        n = n//2 if n % 2 == 0 else 3*n-1
        minus.append(n)
    assert all(5 <= n <= 25 for n in minus)
    print(f'{exhaustive} exhaustive and {large} large-integer exit cases; '
          f'maximum exit {max(exits)}; {relaxed} relaxed-transition starts; '
          f'{windows} lower-surviving windows; '
          f'{blocks} distinct block witnesses; sharpness and hypothesis controls passed')


if __name__ == '__main__':
    main()
