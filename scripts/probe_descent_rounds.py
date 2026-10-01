"""Finite exact-integer checks of record minima and first-descent rounds."""
import json
from pathlib import Path


def step(n):
    return n // 2 if n % 2 == 0 else (3 * n + 1) // 2


def orbit_to_one(n, cap=10000):
    values = [n]
    while values[-1] != 1 and len(values) <= cap:
        values.append(step(values[-1]))
    assert values[-1] == 1, ("unresolved input at finite cap", n)
    return values


def main():
    cutoff = 10000
    requested = [1, 2, 4, 8, 16, 32]
    counts = {k: 0 for k in requested}
    largest_depth = (0, 1)
    largest_time = (0, 1)
    total_rounds = 0
    for n in range(1, cutoff + 1):
        values = orbit_to_one(n)
        indices = [0]
        for t, value in enumerate(values[1:], 1):
            if value < values[indices[-1]]:
                indices.append(t)
        chain = [values[t] for t in indices]
        assert chain[-1] == min(values) == 1
        depth = len(chain) - 1
        assert depth <= n
        for k, (a, b) in enumerate(zip(chain, chain[1:])):
            assert b < a <= 2 * b
            segment = values[indices[k]:indices[k + 1]]
            assert min(segment) >= a
            # Independently recover the first-descent endpoint by iteration.
            t, current = 0, a
            while current >= a:
                current = step(current)
                t += 1
                assert t <= len(values)
            assert current == b and t == indices[k + 1] - indices[k]
        for k, current in enumerate(chain):
            assert n <= 2 ** k * current
        for k in requested:
            counts[k] += depth >= k
        total_rounds += depth
        largest_depth = max(largest_depth, (depth, n))
        largest_time = max(largest_time, (len(values) - 1, n))
    result = {
        "all_checks_passed": True,
        "positive_starts_checked": cutoff,
        "first_descent_segments_checked": total_rounds,
        "largest_round_depth": {"rounds": largest_depth[0], "start": largest_depth[1]},
        "largest_accelerated_time": {"steps": largest_time[0], "start": largest_time[1]},
        "starts_with_at_least_k_descents": counts,
        "universal_convergence_proved": False,
        "noncomputable_lean_map_evaluated": False,
    }
    root = Path(__file__).resolve().parents[1]
    (root / "Research/DescentRoundsProbe.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
