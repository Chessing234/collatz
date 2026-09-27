#!/usr/bin/env python3
"""Independently check the cyclic scan against exact geometric sums.

Uses Fraction and the full finite geometric period, not the cyclic update.
This is a program check, not a Lean verification of the reported probabilities.
"""
from fractions import Fraction
import json
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]


def exact_laws(levels):
    previous = [Fraction(1)]
    for n in range(1, levels + 1):
        modulus = 3**n
        period = 2 * 3 ** (n - 1)
        current = [Fraction(0)] * modulus
        for v in range(1, period + 1):
            weight = Fraction(2 ** (period - v), 2**period - 1)
            inverse = pow(2, -v, modulus)
            for y, mass in enumerate(previous):
                current[((3 * y + 1) * inverse) % modulus] += weight * mass
        assert sum(current) == 1
        yield current
        previous = current


def main():
    with tempfile.TemporaryDirectory(prefix="collatz-cycle-check-") as tmp:
        executable = Path(tmp) / "scan"
        subprocess.run([
            "clang++", "-O2", "-std=c++17", "-Wall", "-Wextra",
            str(ROOT / "scripts/syracuse_cycle_scan.cpp"), "-o", str(executable),
        ], check=True)
        exact = list(exact_laws(5))
        checks = 0
        for precision in (8, 20, 60):
            lines = subprocess.check_output(
                [str(executable), "5", str(precision), "atoms"], text=True
            ).splitlines()
            for line, law in zip(lines, exact, strict=True):
                row = json.loads(line)
                scale, error = row["scale"], row["atom_error_numerator"]
                for b, mass in zip(row["atoms"], law, strict=True):
                    assert b <= scale * mass <= b + error, (row["level"], precision)
                    checks += 1
                units = [i for i in range(len(law)) if i % 3]
                low = min(row["atoms"][r] for r in units)
                assert row["minimum_atom_lower"] == low
                assert Fraction(low, scale) <= min(law[r] for r in units)
                assert min(law[r] for r in units) <= Fraction(low + error, scale)
        # Re-evaluate every saved large comparison with unbounded Python integers.
        previous = None
        rows = [json.loads(line) for line in
                (ROOT / "Devices/SyracuseCycleScan.jsonl").read_text().splitlines()]
        for n, row in enumerate(rows, 1):
            assert row["level"] == n
            m, s = row["modulus"], row["scale"]
            b, e = row["minimum_atom_lower"], row["atom_error_numerator"]
            assert m == 3**n and e == 2*n
            pair_refuted = (row["pair_numerator_lower"] + 5*e)*(s + 3*m*b) < 21*b*s
            assert row["sufficient_pair_bound_refuted"] == pair_refuted
            if previous:
                p = previous["minimum_atom_lower"]
                u = p + previous["atom_error_numerator"]
                certified = 3*b*(s + m*u) >= u*s
                refuted = 3*(b+e)*(s + m*p) < p*s
                assert row["logistic_certified"] == certified
                assert row["logistic_refuted"] == refuted
            previous = row
        print(f"Passed {checks} exact atom enclosure checks at levels 1..5, "
              f"precisions 8/20/60, and {len(rows)} saved comparison rows.")


if __name__ == "__main__":
    main()
