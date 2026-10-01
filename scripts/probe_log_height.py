#!/usr/bin/env python3
"""Finite tests for bounded additive perturbations of binary-log height."""
import json
from probe_comparable_height import iterate, step


def log_height(n):
    return (n + 1).bit_length() - 1


def check_schedule(height, error, horizon, cutoff, policy):
    distortion = 2 ** (2 * error + 1)
    rounds = 2 * distortion + 1
    length = horizon * rounds + 1
    start = (cutoff + 3) * 2**length - 1
    current = start
    elapsed = 0
    for choices in range(rounds + 1):
        assert cutoff < current and current > 1
        value = height(current)
        assert abs(value - log_height(current)) <= error
        assert current + 1 <= 2 ** (error + 1) * 2**value
        assert 2**value <= 2**error * (current + 1)
        assert value <= height(start)
        candidates = []
        endpoint = current
        for k in range(1, horizon + 1):
            endpoint = step(endpoint)
            if height(endpoint) <= value:
                candidates.append((k, endpoint))
        if not candidates:
            return choices, elapsed, current.bit_length()
        assert choices < rounds
        if policy == "earliest":
            k, current = candidates[0]
        elif policy == "latest":
            k, current = candidates[-1]
        else:
            k, current = min(candidates, key=lambda pair: height(pair[1]))
        elapsed += k
        assert elapsed <= horizon * (choices + 1) < length
        assert current == iterate(start, elapsed)
    raise AssertionError("A bounded-log-height schedule escaped the obstruction")


def main():
    families = [
        ("binary_log", 0, log_height),
        ("residue_correction", 2, lambda n: log_height(n) + n % 3),
        ("digit_correction", 2, lambda n: log_height(n) + n.bit_count() % 3),
        ("signed_correction", 2, lambda n: max(0, log_height(n) + n % 5 - 2)),
    ]
    summaries = []
    pointwise = 0
    for name, error, height in families:
        for n in range(10000):
            value = height(n)
            assert abs(value - log_height(n)) <= error
            assert n + 1 <= 2 ** (error + 1) * 2**value
            assert 2**value <= 2**error * (n + 1)
            pointwise += 1
        results = [
            check_schedule(height, error, horizon, cutoff, policy)
            for horizon in (1, 2, 3, 5, 8, 13)
            for cutoff in (0, 100, 10000)
            for policy in ("earliest", "latest", "lowest")
        ]
        summaries.append({
            "height": name,
            "max_additive_error": error,
            "cases": len(results),
            "max_successful_choices_before_obstruction": max(r[0] for r in results),
            "max_elapsed_time_before_obstruction": max(r[1] for r in results),
            "max_obstruction_input_bits": max(r[2] for r in results),
        })
    print(json.dumps({
        "pointwise_comparison_checks": pointwise,
        "schedule_cases": sum(s["cases"] for s in summaries),
        "all_checks_passed": True,
        "families": summaries,
        "proves_collatz": False,
    }, indent=2))


if __name__ == "__main__":
    main()
