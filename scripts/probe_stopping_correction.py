"""Exact finite-prefix and first-arrival tests of odd-state correction bounds."""
from fractions import Fraction
import json
from pathlib import Path


def step(n):
    return n // 2 if n % 2 == 0 else (3 * n + 1) // 2


def main():
    prefix_checks = 0
    for n in range(501):
        x, q, minimum_odd = n, 0, None
        for k in range(41):
            parameters = {0, 1, 3, 1000 if minimum_odd is None else minimum_odd}
            for lower in parameters:
                if minimum_odd is None or lower <= minimum_odd:
                    assert lower ** q * 2 ** k * x <= (3 * lower + 1) ** q * n
                    prefix_checks += 1
            if x % 2:
                minimum_odd = x if minimum_odd is None else min(minimum_odd, x)
                q += 1
            x = step(x)
    cutoff = 100000
    best_ratio = Fraction(1)
    best = {"start": 1, "time": 0, "odd_steps": 0}
    one_bit_examples = 0
    for n in range(1, cutoff + 1):
        x, k, q = n, 0, 0
        while x != 1:
            assert k < 10000, ("unresolved at finite cap", n)
            if x % 2:
                assert x >= 3
                q += 1
            x = step(x)
            k += 1
        assert 3 ** q * n <= 2 ** k
        assert 3 ** q * 2 ** k <= 10 ** q * n
        ratio = Fraction(2 ** k, 3 ** q * n)
        one_bit_examples += ratio < 2
        if ratio > best_ratio:
            best_ratio = ratio
            best = {"start": n, "time": k, "odd_steps": q}
    assert 3 ** 1 * 2 ** 2 > 10 ** 1  # Later return 1 -> 2 -> 1.
    result = {
        "all_checks_passed": True,
        "scaled_prefix_checks": prefix_checks,
        "first_arrivals_checked": cutoff,
        "observed_one_bit_slack_cases": one_bit_examples,
        "maximum_observed_ratio": {
            **best,
            "numerator": best_ratio.numerator,
            "denominator": best_ratio.denominator,
            "approximation": float(best_ratio),
        },
        "proves_uniform_one_bit_slack": False,
        "proves_universal_convergence": False,
    }
    root = Path(__file__).resolve().parents[1]
    (root / "Research/StoppingCorrectionProbe.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
