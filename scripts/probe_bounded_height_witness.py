#!/usr/bin/env python3
"""Exhaust the finite witness runs from BoundedHeightWitness.lean."""
import json
from probe_comparable_height import step, iterate


def check_run(height, factor, horizon, cutoff):
    q = cutoff + 3
    last = horizon * (2 * factor + 1)
    length = last + 1
    start = q * 2**length - 1
    states = [start]
    for _ in range(last):
        states.append(step(states[-1]))
    assert all(x + 1 <= height(x) <= factor * (x + 1) for x in states)
    failures = []
    for t, x in enumerate(states):
        if all(height(x) < height(iterate(x, k)) for k in range(1, horizon + 1)):
            failures.append((t, x))
    assert failures
    for _, x in failures:
        assert cutoff < x and 1 < x and x < q * 3**length
    first_time, first_input = failures[0]
    return {
        "factor": factor,
        "horizon": horizon,
        "cutoff": cutoff,
        "states_checked": len(states),
        "failure_states": len(failures),
        "first_failure_time": first_time,
        "first_failure_input": first_input,
    }


def main():
    families = [
        ("size", 1, lambda n: n + 1),
        ("residue", 7, lambda n: (n + 1) * (n % 7 + 1)),
        ("binary_digits", 4, lambda n: (n + 1) * (n.bit_count() % 4 + 1)),
    ]
    records = []
    examples = []
    for name, factor, height in families:
        results = [check_run(height, factor, horizon, cutoff)
                   for horizon in range(7) for cutoff in (0, 3, 100)]
        records.append({
            "height": name,
            "cases": len(results),
            "states_checked": sum(r["states_checked"] for r in results),
            "max_first_failure_time": max(r["first_failure_time"] for r in results),
        })
        example = check_run(height, factor, 2, 0)
        examples.append({"height": name, **example})
    print(json.dumps({
        "all_checks_passed": True,
        "cases": sum(r["cases"] for r in records),
        "states_checked": sum(r["states_checked"] for r in records),
        "families": records,
        "examples": examples,
        "counterexamples_to_collatz": False,
    }, indent=2))


if __name__ == "__main__":
    main()
