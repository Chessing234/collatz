#!/usr/bin/env python3
"""Independent integer checks for the bounded-distortion height obstruction.

Finite tests support the implementation; the Lean theorem quantifies over all
heights satisfying its bounds and all finite horizons and cutoffs.
"""
import json


def step(n):
    return n // 2 if n % 2 == 0 else (3 * n + 1) // 2


def iterate(n, k):
    for _ in range(k):
        n = step(n)
    return n


def check_formula():
    cases = 0
    for q in range(1, 8):
        for length in range(1, 25):
            n = q * 2**length - 1
            for i in range(length + 1):
                assert iterate(n, i) == q * 3**i * 2 ** (length - i) - 1
                assert (i + 2) * 2**i <= 2 * 3**i
                for factor in range(11):
                    if 2 * factor + 1 <= i:
                        assert factor * (n + 1) < iterate(n, i) + 1
                cases += 1
    return cases


def find_obstruction(height, factor, horizon, cutoff, policy):
    rounds = 2 * factor + 1
    length = horizon * rounds + 1
    start = (cutoff + 3) * 2**length - 1
    current = start
    elapsed = 0
    for chosen in range(rounds + 1):
        assert cutoff < current and 1 < current
        assert current + 1 <= height(current) <= factor * (current + 1)
        assert height(current) <= height(start)
        candidates = []
        endpoint = current
        for k in range(1, horizon + 1):
            endpoint = step(endpoint)
            if height(endpoint) <= height(current):
                candidates.append((k, endpoint))
        if not candidates:
            return chosen, elapsed, current.bit_length()
        assert chosen < rounds, "The bounded-distortion obstruction was violated"
        if policy == "earliest":
            k, current = candidates[0]
        elif policy == "latest":
            k, current = candidates[-1]
        else:
            k, current = min(candidates, key=lambda pair: height(pair[1]))
        elapsed += k
        assert elapsed <= horizon * (chosen + 1) < length
        assert current == iterate(start, elapsed)
    raise AssertionError("No obstruction found")


def main():
    families = [
        ("size", 1, lambda n: n + 1),
        ("parity_oscillation", 2, lambda n: (n + 1) * (1 + n % 2)),
        ("residue_oscillation", 7, lambda n: (n + 1) * (1 + n % 7)),
        ("binary_digit_oscillation", 4, lambda n: (n + 1) * (1 + n.bit_count() % 4)),
    ]
    summaries = []
    for name, factor, height in families:
        results = [
            find_obstruction(height, factor, horizon, cutoff, policy)
            for horizon in (1, 2, 3, 5, 8, 13)
            for cutoff in (0, 100, 10000)
            for policy in ("earliest", "latest", "lowest")
        ]
        summaries.append({
            "height": name,
            "factor": factor,
            "cases": len(results),
            "max_successful_choices_before_obstruction": max(r[0] for r in results),
            "max_elapsed_time_before_obstruction": max(r[1] for r in results),
            "max_obstruction_input_bits": max(r[2] for r in results),
        })
    print(json.dumps({
        "odd_run_formula_cases": check_formula(),
        "schedule_cases": sum(s["cases"] for s in summaries),
        "all_checks_passed": True,
        "families": summaries,
        "proves_collatz": False,
    }, indent=2))


if __name__ == "__main__":
    main()
