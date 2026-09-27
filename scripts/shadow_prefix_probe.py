#!/usr/bin/env python3
"""Exact finite-prefix probes; these are experiments, not a Collatz proof.

Construct integer starts realizing prescribed finite valuation words and check
real shadow recurrences using rational arithmetic. No floating point is used.
"""
from fractions import Fraction as Q
from pathlib import Path
import json


def realize(word):
    total, offset, odd_steps = 0, 0, 0
    for a in word:
        assert a >= 1
        offset = 3 * offset + 2**total
        total += a
        odd_steps += 1
    modulus = 2 ** (total + 1)
    seed = ((2**total - offset) * pow(3**odd_steps, -1, modulus)) % modulus
    assert seed > 0 and seed % 2 == 1
    xs = [seed]
    for a in word:
        numerator = 3 * xs[-1] + 1
        observed = (numerator & -numerator).bit_length() - 1
        assert observed == a
        xs.append(numerator // 2**a)
    return seed, xs


def shadow_from_terminal(word, terminal):
    es = [terminal]
    for a in reversed(word):
        es.append((1 + 2**a * es[-1]) / 3)
    return list(reversed(es))


def check_pair(word, xs, es):
    for i, a in enumerate(word):
        assert 2**a * xs[i + 1] == 3 * xs[i] + 1
        assert 2**a * es[i + 1] == 3 * es[i] - 1
        assert 2**a * (xs[i + 1] + es[i + 1]) == 3 * (xs[i] + es[i])
    return {
        "steps": len(word),
        "seed": str(xs[0]),
        "seed_bits": xs[0].bit_length(),
        "endpoint": str(xs[-1]),
        "shadow_min": str(min(es)),
        "shadow_max": str(max(es)),
    }


def main():
    output = {"scope": "Exact finite checks only. Terminal shadows are prescribed, not the actual infinite-orbit boundary."}
    periodic = []
    for blocks in (1, 4, 16, 64):
        word = [1, 1, 1, 1, 2] * blocks
        seed, xs = realize(word)
        es = shadow_from_terminal(word, Q(211, 179))
        report = check_pair(word, xs, es)
        assert all(es[i + 5] == es[i] for i in range(len(es) - 5))
        assert all(Q(1) < e < Q(2) for e in es)
        grid_bound = 179 * (seed + 2) + 1
        assert 2 ** len(word) < grid_bound
        report["exact_shadow_period"] = 5
        report["grid_denominator"] = 179
        report["finite_grid_bound_rhs"] = str(grid_bound)
        report["finite_grid_max_allowed_steps"] = (grid_bound - 1).bit_length() - 1
        report["blocks"] = blocks
        periodic.append(report)
    output["periodic_prefixes"] = periodic

    # Thue--Morse chooses runs of four or five valuation-one steps.
    runs = [4 + (i.bit_count() % 2) for i in range(64)]
    word = [a for r in runs for a in [1] * r + [2]]
    seed, xs = realize(word)
    es = shadow_from_terminal(word, Q(211, 179))
    report = check_pair(word, xs, es)
    assert all(Q(1) < e < Q(2) for e in es)
    report["run_lengths"] = runs
    report["terminal_shadow"] = "211/179"
    output["nonperiodic_word_prefix"] = report

    destination = Path(__file__).resolve().parents[1] / "Devices" / "ShadowPrefixProbe.json"
    destination.write_text(json.dumps(output, indent=2) + "\n")
    print(f"Checked {sum(r['steps'] for r in periodic) + report['steps']} exact steps.")
    print(f"Wrote {destination}")


if __name__ == "__main__":
    main()
