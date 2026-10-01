"""Measure first terminal times on finite, fully observed Collatz trajectories.

Classical choices in Lean are not evaluated here. First attainment times are
lower bounds for all choices reaching the same observed minimum.
"""
import json
from pathlib import Path
from probe_descent_rounds import orbit_to_one, step


def main():
    horizons = [0, 1, 4, 16, 32, 64, 128]
    sample_cutoffs = [1000, 10000, 100000]
    step_tails = {k: 0 for k in horizons}
    round_tails = {k: 0 for k in horizons}
    rows = []
    observed_image = set()
    # The complete 1 -> 2 -> 1 cycle certifies that 1 never drops.
    assert step(1) == 2 and step(2) == 1
    for n in range(1, max(sample_cutoffs) + 1):
        values = orbit_to_one(n)
        minimum = min(values)
        assert minimum == 1
        observed_image.add(minimum)
        first_time = values.index(minimum)
        assert first_time == len(values) - 1
        record = n
        depth = 0
        for value in values[1:]:
            if value < record:
                record = value
                depth += 1
        assert record == minimum and depth <= n
        # Every earlier record is a genuinely descending start, witnessed
        # by the next smaller record already in this finite trajectory.
        assert (depth > 0) == (n > 1)
        assert first_time >= depth
        for k in horizons:
            step_tails[k] += first_time > k
            round_tails[k] += depth > k
        if n in sample_cutoffs:
            rows.append({
                "positive_starts_through": n,
                "minimum_image": sorted(observed_image),
                "minimum_preimage_with_finite_stopping": 0,
                "first_minimum_step_time_exceeds": step_tails.copy(),
                "first_terminal_round_exceeds": round_tails.copy(),
            })
    result = {
        "all_checks_passed": True,
        "samples": rows,
        "evaluates_classical_lean_choices": False,
        "proves_universal_convergence": False,
    }
    destination = Path(__file__).resolve().parents[1] / "Research/MinimumTransportProbe.json"
    destination.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
