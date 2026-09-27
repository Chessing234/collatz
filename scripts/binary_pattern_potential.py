#!/usr/bin/env python3
"""Search or recheck exact obstructions to additive binary-pattern descent.

Search uses SciPy/HiGHS, but a result is retained only after an exact integer
histogram check. Generated Lean connects the check to the actual odd map.
The certificates cover the listed widths, not every finite width.
"""
import argparse
from collections import Counter
from fractions import Fraction
import json
from math import lcm
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DATA = ROOT / "Devices/BinaryPatternCertificates.json"
LEAN = ROOT / "ProofAtlasAttack/CollatzTargetDensity/BinaryPatternCertificates.lean"


def odd_step(n):
    x = 3*n+1
    return x//(x & -x)


def profile(n, k):
    text = "2"*(k-1) + bin(n)[2:] + "2"*(k-1)
    return Counter(int(text[i:i+k], 3) for i in range(len(text)-k+1))


def validate(row):
    k = row["width"]
    assert k >= 1 and row["edges"]
    balance = Counter()
    for n, s, multiplicity in row["edges"]:
        expected = n
        for _ in range(row.get("odd_steps", 1)):
            expected = odd_step(expected)
        assert n > 1 and n % 2 and s == expected and multiplicity > 0
        for code, count in profile(s, k).items():
            balance[code] += multiplicity*count
        for code, count in profile(n, k).items():
            balance[code] -= multiplicity*count
    assert all(x == 0 for x in balance.values()), f"nonzero exact balance at width {k}"


def search(k):
    import numpy as np
    from scipy.optimize import linprog
    from scipy.sparse import csr_matrix, vstack

    limit = 2**max(10, k+5)
    starts = list(range(3, limit, 2))
    columns, rows = {}, []
    for n in starts:
        delta = profile(odd_step(n), k)
        delta.subtract(profile(n, k))
        row = {}
        for pattern, value in delta.items():
            if value:
                if pattern not in columns:
                    columns[pattern] = len(columns)
                row[columns[pattern]] = value
        rows.append(row)
    data, indices, pointer = [], [], [0]
    for row in rows:
        for j, value in row.items():
            data.append(value)
            indices.append(j)
        pointer.append(len(data))
    matrix = csr_matrix((data, indices, pointer), shape=(len(rows), len(columns)), dtype=float)
    primal = linprog(np.zeros(matrix.shape[1]), A_ub=matrix,
                    b_ub=-np.ones(matrix.shape[0]), bounds=(None, None), method="highs")
    if primal.status != 2:
        raise RuntimeError(f"width {k}: no infeasibility certificate; solver status {primal.status}")
    constraints = vstack([matrix.T, csr_matrix(np.ones((1, matrix.shape[0])))])
    rhs = np.zeros(constraints.shape[0])
    rhs[-1] = 1
    dual = linprog(np.log2(starts), A_eq=constraints, b_eq=rhs, bounds=(0, None), method="highs")
    if not dual.success:
        raise RuntimeError(dual.message)
    support = [(i, Fraction(float(x)).limit_denominator(10**7))
               for i, x in enumerate(dual.x) if x > 1e-9]
    denominator = lcm(*(x.denominator for _, x in support))
    row = {"width": k, "search_limit": limit,
           "edges": [[starts[i], odd_step(starts[i]), int(x*denominator)] for i, x in support]}
    validate(row)
    return row


def emit(rows):
    lines = ["import CollatzTargetDensity.BinaryPatternPotential", "",
             "/-! Generated exact certificates; ordinary kernel reduction checks the data. -/",
             "namespace CollatzTargetDensity.BinaryPatternPotential", "",
             "set_option maxRecDepth 100000", "set_option maxHeartbeats 10000000", ""]
    for row in rows:
        validate(row)
        assert row.get("odd_steps", 1) == 1
        k = row["width"]
        lines += [f"def certificate{k} : List Edge := ["]
        edges = []
        for n, s, c in row["edges"]:
            exponent = ((3*n+1) & -(3*n+1)).bit_length()-1
            edges.append(f"  ⟨{n}, {s}, {exponent}, {c}⟩")
        lines += [",\n".join(edges), "]", "",
                  f"theorem certificate{k}_checked : check {k} certificate{k} = true := by decide", ""]
    assert [r["width"] for r in rows] == list(range(1, 8))
    lines += ["/-- This covers widths one through seven, with arbitrary real weights.",
              "It makes no assertion about larger widths or other potential families. -/",
              "theorem no_width_le_seven (k : ℕ) (hk : 1 ≤ k) (hK : k ≤ 7) (w : ℕ → ℝ) :",
              "    ¬StrictDescent k w := by", "  interval_cases k"]
    for k in range(1, 8):
        lines += [f"  · exact check_not_descent {k} certificate{k} certificate{k}_checked w"]
    lines += ["", "end CollatzTargetDensity.BinaryPatternPotential", ""]
    return "\n".join(lines)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--search", action="store_true", help="rerun the search with SciPy")
    parser.add_argument("--emit", action="store_true", help="regenerate the Lean certificate file")
    args = parser.parse_args()
    if args.search:
        rows = [search(k) for k in range(1, 8)]
        DATA.write_text(json.dumps(rows, indent=2)+"\n")
    else:
        rows = json.loads(DATA.read_text())
    for row in rows:
        validate(row)
    if args.emit:
        LEAN.write_text(emit(rows))
    print(f"Exact integer balances verified for {len(rows)} widths, "
          f"{sum(len(row['edges']) for row in rows)} weighted edges.")
    block_path = ROOT / "Devices/BinaryPatternBlockProbe.json"
    if block_path.exists():
        blocks = json.loads(block_path.read_text())
        for row in blocks:
            validate(row)
        print(f"Also rechecked {len(blocks)} block probes in exact integers; "
              "these block probes are not Lean certificates.")


if __name__ == "__main__":
    main()
