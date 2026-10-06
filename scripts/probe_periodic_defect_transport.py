#!/usr/bin/env python3
"""Independent finite checks; these are regression tests, not the proof.

The main checks enumerate forward integer orbits. They do not use the
transfer recurrence to compute the defect counts being tested.
"""

from collections import Counter
from functools import lru_cache
import json


def step(n):
    return n // 2 if n % 2 == 0 else (3 * n + 1) // 2


def orbit(n, k):
    for _ in range(k):
        n = step(n)
    return n


@lru_cache(None)
def weight(k, n):
    if k == 0:
        return int(n % 3 != 0)
    return weight(k - 1, 2 * n) + (
        3 * weight(k - 1, (2 * n - 1) // 3) if n % 3 == 2 else 0
    )


def run():
    cases = 0
    plateaus = 0
    minima = []
    for m in (3, 6, 9, 12):
        M = 2 * m
        # Histograms use actual forward orbits on the full specified ranges.
        hist = [Counter(orbit(n, k) % M for n in range((2**k) * M))
                for k in range(9)]
        for bits in range(2**m):
            def label(n):
                return (bits >> (n % m)) & 1

            errors = [int(label(step(n)) != label(n)) for n in range(M)]
            D = [sum(hist[k][r] * errors[r] for r in range(M))
                 for k in range(9)]
            C = sum(errors[r] for r in range(M) if r % 3)
            assert D[1] == D[0] + 3 * sum(errors[r] for r in range(M) if r % 3 == 2)
            assert all(D[2*k] >= D[0] + 3*k*C for k in range(5))
            assert all(D[4*k] >= 4**k * C for k in range(3))
            assert (D[2] == D[0]) == (C == 0)
            if C == 0:
                plateaus += 1
                assert all(d == D[0] for d in D)
            cases += 1

    # Independent validation of every column of the four-step duality matrix.
    M = 243
    columns = Counter(orbit(n, 4) % M for n in range(16*M) if n % 3)
    assert all(columns[r] == weight(4, r) for r in range(M))
    assert min(columns[r] for r in range(M) if r % 3) == 4

    balanced_cases = 0
    for m in (1, 2, 4, 5, 7, 8, 10):
        M = 2*m
        hist = [Counter(orbit(n, k) % M for n in range((2**k)*M))
                for k in range(9)]
        for bits in range(2**m):
            def label(n):
                return (bits >> (n % m)) & 1

            errors = [int(label(step(n)) != label(n)) for n in range(M)]
            D = [sum(hist[k][r]*errors[r] for r in range(M)) for k in range(9)]
            assert all(D[k] == 2**k*D[0] for k in range(9))
            balanced_cases += 1
    for k in range(8):
        value, residue = min((weight(k, n), n) for n in range(3**(k+1)) if n % 3)
        minima.append({"steps": k, "minimum": value, "witness": residue})

    # Tightness of the factor four for arbitrary periodic nonnegative errors.
    g = lambda n: int(n % 243 == 4)
    assert sum(g(n) for n in range(243) if n % 3) == 1
    assert sum(g(orbit(n, 4)) for n in range(16*243) if n % 3) == 4

    return {
        "status": "passed",
        "boolean_periods_exhausted": [3, 6, 9, 12],
        "boolean_labels_checked": cases,
        "scales_checked_per_label": list(range(9)),
        "constant_towers_checked": plateaus,
        "independent_transfer_columns_checked": 243,
        "exact_doubling_periods_exhausted": [1, 2, 4, 5, 7, 8, 10],
        "exact_doubling_labels_checked": balanced_cases,
        "four_step_sharpness": {"period": 243, "support_residue": 4,
                                "initial_core_mass": 1, "four_step_core_mass": 4},
        "computed_weight_minima_not_all_formalized": minima,
        "scope": "Finite regression only; Lean supplies the universal proof. No novelty claim.",
    }


if __name__ == "__main__":
    print(json.dumps(run(), indent=2))
