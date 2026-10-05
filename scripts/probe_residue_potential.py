"""Independent exact-integer tests for fixed-block potential obstructions.

Run with Python's standard library. This is experimental validation, not the
Lean proof. The orbit is iterated independently of the closed-form endpoint.
The tests check every intermediate odd step, congruence, growth, and examples
of potentials whose coefficients vary by residue. Assertions must stay enabled.
"""
from __future__ import annotations


def accelerated_step(n: int) -> int:
    return n // 2 if n % 2 == 0 else (3 * n + 1) // 2


def check_witness(modulus: int, horizon: int) -> None:
    assert modulus > 0 and horizon > 0
    initial = (2 ** (horizon + 1)) * modulus - 1
    current = initial
    for index in range(horizon):
        assert current % 2 == 1, (modulus, horizon, index, current)
        expected = (3 ** index) * (2 ** (horizon + 1 - index)) * modulus - 1
        assert current == expected, (modulus, horizon, index)
        current = accelerated_step(current)
    endpoint = 2 * (3 ** horizon) * modulus - 1
    assert current == endpoint, (modulus, horizon)
    assert initial > 1 and endpoint > initial
    assert initial % modulus == endpoint % modulus == modulus - 1

    # Coefficients vary by residue; same-residue growth still prevents a drop.
    def affine_potential(n: int) -> int:
        residue = n % modulus
        slope = (residue * residue + 7) % 13
        intercept = 17 * residue + 31
        return slope * n + intercept

    def nonlinear_potential(n: int) -> int:
        return n * n + (n % modulus) ** 3

    assert affine_potential(initial) <= affine_potential(endpoint)
    assert nonlinear_potential(initial) < nonlinear_potential(endpoint)


def main() -> None:
    moduli = list(range(1, 65)) + [97, 255, 256, 257, 1024, 65537]
    horizons = list(range(1, 41)) + [59, 100, 200, 500]
    checked = 0
    for modulus in moduli:
        for horizon in horizons:
            check_witness(modulus, horizon)
            checked += 1
    print(f"Passed {checked} growing same-residue witnesses; horizons up to 500.")
    print("No numerical result is promoted to universal convergence.")


if __name__ == "__main__":
    main()
