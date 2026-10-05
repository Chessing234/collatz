#!/usr/bin/env python3
"""Exact stress tests for the finite shadow near-return device.

These experiments use rational arithmetic and genuine finite integer Collatz
traces. Assigned finite shadows are not the infinite canonical boundary.
Lean proofs, not these experiments, establish the universal statements.
"""
from fractions import Fraction as Q
from math import factorial, ceil
from pathlib import Path
import json
import random

from shadow_prefix_probe import realize, shadow_from_terminal, check_pair


def block(coefficients):
    product, offset = 1, 0
    for c in coefficients:
        product, offset = product * c, 3 * offset + product
    return product, offset


def anchor(es, cs, j, p, r, cap, eta):
    assert 0 < p and j + p <= r and es[j] >= 1
    assert all(1 <= c <= cap for c in cs[:r])
    assert cap**r * eta < 1 and abs(es[j + p] - es[j]) <= eta
    pre_p, pre_c = block(cs[:j])
    ret_p, ret_c = block(cs[j : j + p])
    denominator_gap = 3**p - ret_p
    assert denominator_gap > 0
    q = 3**j * denominator_gap
    m = pre_p * ret_c + denominator_gap * pre_c
    assert 0 < q <= 3**r
    error = q * es[0] - m
    assert error == pre_p * ret_p * (es[j + p] - es[j])
    assert abs(error) <= cap**r * eta
    grid = factorial(3**r)
    assert grid % q == 0
    numerator = (grid // q) * m
    assert abs(grid * es[0] - numerator) <= grid * cap**r * eta
    return q, error != 0


def main():
    rng = random.Random(20260928)
    checks = nonzero = steps = 0
    samples = []
    # Rational periodic models perturbed by tiny, nonzero terminal errors.
    # Every associated x trace is independently checked for exact valuations.
    for word in ([1], [1, 2], [1, 1, 2], [1, 1, 1, 1, 2]):
        cs0 = [2**a for a in word]
        product, offset = block(cs0)
        terminal = Q(offset, 3**len(word) - product)
        for repetitions in (1, 3, 8):
            vals = list(word) * repetitions
            seed, xs = realize(vals)
            r = len(word)
            exact = shadow_from_terminal(vals, terminal)
            maximum = ceil(max(exact)) + 1
            cap = 3 * maximum
            eta = Q(1, 12 * factorial(3**r) * cap**r * (maximum + 1))
            for perturbation in (Q(0), eta / 100, -eta / 100):
                # The negative perturbation is excluded when it crosses E=1.
                es = shadow_from_terminal(vals, terminal + perturbation)
                if min(es) < 1:
                    continue
                check_pair(vals, xs, es)
                assert max(es) <= maximum
                cs = [2**a for a in vals]
                for start in range(len(vals) - r + 1):
                    shifted = es[start:]
                    if abs(shifted[r] - shifted[0]) <= eta:
                        q, nz = anchor(shifted, cs[start:], 0, r, r, cap, eta)
                        checks += 1
                        nonzero += nz
                length = len(vals) - r
                # Every r-window has its return of length r within eta.
                assert all(abs(es[i+r] - es[i]) <= eta for i in range(length+1))
                assert 2**length < factorial(3**r) * (seed + maximum) + 1
                steps += len(vals)
            samples.append({"word": list(word), "repetitions": repetitions,
                            "seed": str(seed), "levels": len(word),
                            "bound_holds": True})

    # Random finite real recurrences test anchors at nonzero prefix offsets.
    random_checks = 0
    for _ in range(5000):
        r = rng.randint(2, 8)
        vals = [rng.randint(1, 3) for _ in range(r)]
        cs = [2**a for a in vals]
        es = shadow_from_terminal(vals, Q(rng.randint(1, 30), 7))
        cap = max(cs)
        eta = Q(1, 2 * cap**r)
        j = rng.randrange(r)
        p = rng.randint(1, r-j)
        if es[j] >= 1 and abs(es[j+p]-es[j]) <= eta:
            anchor(es, cs, j, p, r, cap, eta)
            random_checks += 1

    # A nonvacuous finite separated-window instance on the true cycle x=1.
    # Its finite shadow grows backwards, so it cannot extend to a bounded
    # positive shadow for all future time.
    length, r = 80, 2
    horizon = length + r
    vals = [2] * horizon
    xs = [1] * (horizon + 1)
    es = shadow_from_terminal(vals, Q(1))
    check_pair(vals, xs, es)
    maximum = ceil(max(es))
    cap = 3 * maximum
    eta = Q(1, 12 * factorial(3**r) * cap**r * (maximum + 1))
    assert factorial(3**r) * (1 + maximum) + 1 <= 2**length
    separated = next(i for i in range(length+1)
                     if all(abs(es[i+k]-es[i+j]) > eta
                            for j in range(r+1) for k in range(j+1, r+1)))
    # Integrality is essential: an infinite positive REAL trace can follow
    # the periodic correction for word [1,2] exactly. It is not an integer orbit.
    real_x = Q(1)
    real_e = Q(5)
    real_noninteger = False
    for i in range(30):
        c = (2, 4)[i % 2]
        real_x = (3*real_x+1)/c
        real_e = (3*real_e-1)/c
        real_noninteger |= real_x.denominator != 1
        assert real_x > 0 and real_e in (5, 7)
    assert real_noninteger

    report = {
        "scope": "Exact finite experiments, not an infinite-boundary computation or proof oracle.",
        "periodic_and_perturbed_anchor_checks": checks,
        "nonzero_error_anchor_checks": nonzero,
        "random_trials": 5000,
        "random_trials_meeting_anchor_hypotheses": random_checks,
        "genuine_integer_steps_checked": steps + horizon,
        "finite_examples": samples,
        "nonvacuous_separated_window": {"orbit": "x_i = 1", "L": length,
            "r": r, "M": maximum, "first_separated_window": separated,
            "length_hypothesis_verified": True},
        "positive_real_countermodel_without_integrality": True,
    }
    destination = Path(__file__).resolve().parents[1] / "Research" / "ShadowWindowProbe.json"
    destination.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({k: v for k, v in report.items() if k != "finite_examples"}, indent=2))


if __name__ == "__main__":
    main()
