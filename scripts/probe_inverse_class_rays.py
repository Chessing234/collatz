"""Replay geometric inverse rays against both forward Collatz conventions.

This finite probe verifies the exact index recurrence, affine endpoints,
residue membership, and explicit successful-time certificates. It deliberately
checks families, not every number in any dyadic residue class.
"""
from __future__ import annotations

from probe_dyadic_convergent_classes import profile, power_index, standard


def check_ray(horizon: int, residue: int, bound: int, length: int) -> tuple[int, int]:
    parities, offset = profile(residue, horizon)
    odds = sum(parities)
    multiplier = 3 ** odds
    period = 1 if odds == 0 else 2 * 3 ** (odds - 1)
    period_power = 1 << period
    assert (period_power - 1) % multiplier == 0
    coefficient = (period_power - 1) // multiplier
    assert coefficient > 0
    seed_exponent = power_index(multiplier, offset, period)
    threshold = multiplier * bound + offset
    if (1 << seed_exponent) <= threshold:
        bits = max(1, threshold.bit_length())
        seed_exponent += period * (bits // period + 1)
    seed_index = ((1 << seed_exponent) - offset) // multiplier
    assert seed_index > bound
    index = seed_index
    previous_input = 0
    max_bits = 0
    max_time = 0
    for j in range(length):
        exponent = seed_exponent + period * j
        endpoint = 1 << exponent
        initial = (1 << horizon) * index + residue
        assert multiplier * index + offset == endpoint
        assert initial % (1 << horizon) == residue
        assert initial > previous_input
        actual_parities, actual_endpoint = profile(initial, horizon)
        assert actual_parities == parities
        assert actual_endpoint == endpoint
        current = initial
        clock = 0
        for parity in actual_parities:
            assert current % 2 == parity
            for _ in range(1 + parity):
                current = standard(current)
                clock += 1
        assert clock == horizon + odds
        assert current == endpoint
        for _ in range(exponent):
            assert current > 1 and current % 2 == 0
            current = standard(current)
        assert current == 1
        successful_time = clock + exponent
        assert successful_time <= 2 * horizon + period * j + seed_exponent
        max_bits = max(max_bits, initial.bit_length())
        max_time = max(max_time, successful_time)
        previous_input = initial
        index = period_power * index + coefficient * offset
    return max_bits, max_time


def main() -> None:
    rays = 0
    members = 0
    largest_bits = 0
    largest_time = 0
    length = 6
    for horizon in range(8):
        for residue in range(1 << horizon):
            for bound in [0, 17, 1000]:
                bits, time = check_ray(horizon, residue, bound, length)
                largest_bits = max(largest_bits, bits)
                largest_time = max(largest_time, time)
                rays += 1
                members += length
    print(f"Passed {rays} independently constructed rays and {members} members.")
    print(f"Largest input: {largest_bits} binary digits; successful time: {largest_time}.")
    print("Infinite-family theorems are checked in Lean; this finite replay checks implementation agreement.")


if __name__ == "__main__":
    main()
