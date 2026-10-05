"""Independently construct convergent members of finite dyadic classes.

The Lean theorem proves existence for all dyadic moduli. This Python probe is
an independent finite check of the construction, not a substitute for it. It
searches a complete ternary period for the endpoint exponent, then checks the
actual forward orbit. It does not treat one convergent member as a proof that
all members of that residue class converge.
"""
from __future__ import annotations


def accelerated(n: int) -> int:
    return n // 2 if n % 2 == 0 else (3 * n + 1) // 2


def standard(n: int) -> int:
    return n // 2 if n % 2 == 0 else 3 * n + 1


def profile(n: int, horizon: int) -> tuple[list[int], int]:
    parities = []
    for _ in range(horizon):
        parities.append(n % 2)
        n = accelerated(n)
    return parities, n


def power_index(multiplier: int, offset: int, period: int) -> int:
    residue = 1 % multiplier
    for exponent in range(period):
        if residue == offset % multiplier:
            return exponent
        residue = (2 * residue) % multiplier
    raise AssertionError("Unit was not covered within the ternary period")


def construct(horizon: int, residue: int, index_bound: int, mode: str) -> tuple[int, int]:
    modulus = 1 << horizon
    assert 0 <= residue < modulus
    parities, offset = profile(residue, horizon)
    odd_count = sum(parities)
    multiplier = 3 ** odd_count
    assert odd_count == 0 or offset % 3 != 0
    period = 1 if odd_count == 0 else 2 * (3 ** (odd_count - 1))
    exponent = power_index(multiplier, offset, period)
    threshold = multiplier * index_bound + offset
    if mode == "binary_jump":
        if (1 << exponent) <= threshold:
            bits = max(1, threshold.bit_length())
            exponent += period * (bits // period + 1)
        assert exponent < max(1, threshold.bit_length()) + 2 * period
    else:
        assert mode == "minimal_jump"
        while (1 << exponent) <= threshold:
            exponent += period
    endpoint = 1 << exponent
    assert (endpoint - offset) % multiplier == 0
    index = (endpoint - offset) // multiplier
    initial = modulus * index + residue
    assert index > index_bound and initial > index_bound
    assert initial % modulus == residue
    actual_parities, actual_endpoint = profile(initial, horizon)
    assert actual_parities == parities
    assert actual_endpoint == endpoint

    # Check standard transitions too, paying one or two steps per accelerated
    # transition, then check the entire terminal halving path to 1.
    current = initial
    standard_steps = 0
    for parity in actual_parities:
        assert current % 2 == parity
        transitions = 1 if parity == 0 else 2
        for _ in range(transitions):
            current = standard(current)
            standard_steps += 1
    assert current == endpoint
    for _ in range(exponent):
        assert current % 2 == 0
        current = standard(current)
        standard_steps += 1
    assert current == 1
    return exponent, standard_steps


def main() -> None:
    checked = 0
    max_exponent = 0
    max_steps = 0
    for horizon in range(9):
        for residue in range(1 << horizon):
            for bound in [0, 1000]:
                for mode in ["minimal_jump", "binary_jump"]:
                    exponent, steps = construct(horizon, residue, bound, mode)
                    max_exponent = max(max_exponent, exponent)
                    max_steps = max(max_steps, steps)
                    checked += 1
    print(f"Passed {checked} independently constructed convergent inputs.")
    print(f"Every residue tested modulo 2^k for 0 <= k <= 8, at two index bounds and with two exponent-raising procedures.")
    print(f"Largest endpoint exponent: {max_exponent}; standard steps: {max_steps}.")
    print("These are member-existence checks, not universal class-convergence checks.")


if __name__ == "__main__":
    main()
