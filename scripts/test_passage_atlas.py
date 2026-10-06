#!/usr/bin/env python3
"""Independent scalar orbits, symbolic-word counts, thresholds, and rejection tests."""
from collections import Counter
import json
from passage_atlas import REPORT, HORIZON, THRESHOLD, SMALL_HORIZON, write_or_check


def direct(n, horizon, stop_at_crossing=False):
    start = n
    a = 0
    first = crossing = None
    for k in range(1, horizon + 1):
        odd = n % 2
        a += odd
        n = n // 2 if odd == 0 else (3 * n + 1) // 2
        if first is None and n < start:
            first = k
        if crossing is None and 3 ** a < 2 ** k:
            crossing = k
            if stop_at_crossing:
                break
    return first, crossing, n, a


def word_events(horizon):
    """Count surviving binary words by odd count; do not iterate integer orbits."""
    alive = {0: 1}
    events = {}
    for k in range(1, horizon + 1):
        next_alive = Counter()
        for a, count in alive.items():
            next_alive[a] += count
            next_alive[a + 1] += count
        killed = sum(count for a, count in next_alive.items() if 3 ** a < 2 ** k)
        survivors = {a: count for a, count in next_alive.items() if 3 ** a >= 2 ** k}
        assert 2 * sum(alive.values()) == killed + sum(survivors.values())
        events[k] = killed
        alive = survivors
    return events


def main():
    manifest = write_or_check(True)
    checks = Counter()
    census = Counter()
    tails = []
    for row in manifest['rows']:
        k, r = row['depth'], row['residue']
        census[row['kind']] += 1
        for m in (0, 1, 2, 17, 1 << 100):
            first, crossing, end, a = direct(2 ** k * m + r, k)
            belongs = row['lower'] <= m and (row['upper'] is None or m < row['upper'])
            assert (first == k) == belongs, (row, m, first)
            assert end == 3 ** row['odd_count'] * m + row['endpoint']
            assert a == row['odd_count']
            if 2 ** k * m + r > 1:
                assert (first == k) == (crossing == k)
            checks['class_samples'] += 1
        if row['kind'] == 'tail':
            assert row['lower'] == 0
            assert row['odd_count'] == 9
            tails.append(r)
    assert census == Counter(empty=32595, tail=173)
    assert len({row['residue'] for row in manifest['rows']}) == 32768
    events = word_events(200)
    assert events[14] == 0 and events[15] == len(tails) == 173
    checks['symbolic_word_horizons'] += 200
    maximum, witness = 0, None
    for n in range(2, THRESHOLD):
        first, crossing, end, a = direct(n, SMALL_HORIZON, True)
        assert first is not None and first == crossing and end < n, (n, first, crossing)
        if crossing > maximum:
            maximum, witness = crossing, n
        checks['exceptional_starts'] += 1
    assert (maximum, witness) == (164, 270271)
    # Check every light exponent, not only the maximal count used by the Lean checker.
    p3 = [3 ** a for a in range(HORIZON + 2)]
    max_threshold, worst = 0, None
    for k in range(1, HORIZON + 1):
        for a in range(k + 1):
            if p3[a] >= 2 ** k:
                break
            threshold = a * p3[a] // (3 * (2 ** k - p3[a])) + 1
            assert threshold <= THRESHOLD
            if threshold > max_threshold:
                max_threshold, worst = threshold, [k, a]
            checks['gap_pairs'] += 1
    next_threshold = 1636 * 3 ** 1636 // (3 * (2 ** 2593 - 3 ** 1636)) + 1
    assert (max_threshold, worst, next_threshold) == (330588, [1539, 971], 583015)
    # The power band is sparse and has at most one power of three at every tested time.
    allowed = []
    for k in range(1, HORIZON + 1):
        band = [a for a in range(k + 1) if 2 ** (k - 1) <= p3[a] < 2 ** k]
        assert len(band) <= 1
        if band:
            allowed.append(k)
            if k <= 200:
                assert events[k] > 0
                checks['occupied_symbolic_bands'] += 1
        else:
            assert events.get(k, 0) == 0
        checks['power_bands'] += 1
    # Prefix discrepancy is checked at every remainder; full periods cancel exactly.
    count = 0
    for N in range(32769):
        assert abs(32768 * count - 173 * N) <= 5638935
        if N < 32768:
            first, _, _, _ = direct(N + 2, 15)
            count += first == 15
        checks['count_remainders'] += 1
    assert count == 173
    assert direct(1, 2)[0] is None
    assert direct(270271, 163, True)[1] is None
    assert direct(tails[0], 15)[0] == 15
    checks['negative_controls'] += 3
    report = {'status': 'passed', 'checks': dict(checks), 'total_checks': sum(checks.values()),
              'census': dict(census), 'period_numerator': count,
              'small_maximum_crossing': maximum, 'small_maximum_witness': witness,
              'gap_max_threshold': max_threshold, 'gap_worst_pair': worst,
              'next_threshold': next_threshold, 'allowed_band_count': len(allowed),
              'symbolic_events_first_30': {k: events[k] for k in range(1, 31)},
              'limitations': ['Finite scalar checks are independent corroboration, not universal proofs.',
                             'Binary-word counting does not prove convergence of every positive integer.']}
    (REPORT / 'python-tests.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))

if __name__ == '__main__':
    main()
