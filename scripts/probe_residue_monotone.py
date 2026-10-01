#!/usr/bin/env python3
"""Independent integer checks of residue-preserving all-odd orbit witnesses.

This is a finite implementation check, not the universal proof (see Lean).
Run from any directory. No third-party packages are required.
"""
import json


def step(n: int) -> int:
    return n // 2 if n % 2 == 0 else (3 * n + 1) // 2


def main() -> None:
    cases = transitions = 0
    for modulus in range(1, 41):
        for multiplier in (1, 2, 3, 11):
            for horizon in range(33):
                n = modulus * multiplier * 2 ** (horizon + 1) - 1
                current = n
                # Deliberately unrelated slopes and offsets on each class.
                height = lambda x: (1 + (x % modulus) ** 2) * x + 7 * (x % modulus)
                for i in range(horizon + 1):
                    expected = modulus * multiplier * 3**i * 2 ** (horizon + 1 - i) - 1
                    assert current == expected, (modulus, multiplier, horizon, i)
                    assert current % modulus == n % modulus
                    if i:
                        assert current > n
                        assert height(current) > height(n)
                        transitions += 1
                    current = step(current)
                cases += 1
    print(json.dumps({"status": "passed", "starting_values": cases,
                      "positive_time_checks": transitions,
                      "moduli": [1, 40], "horizons": [0, 32]}, indent=2))


if __name__ == "__main__":
    main()
