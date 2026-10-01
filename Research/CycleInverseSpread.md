# Cycle spread forced by inverse residues

For a positive accelerated cycle with minimum m and maximum M, Lean now
proves the following necessary bounds:

| m modulo 9 | Lower bound on M |
| --- | --- |
| 1 or 4 | 2m |
| 2 or 5 | 4m |
| 7 | 8m |
| 8 | 16m |

The other three residue classes are excluded because no point of a positive
cycle is divisible by three. The existing library already proves M ≥ 2m;
these residue-sensitive refinements follow from which inverse branches can
actually belong to a cycle. They do not assert that any nontrivial cycle
exists, and no historical novelty or globally optimal bound is claimed.

The formal statement starts the orbit at its minimum and assumes
m ≤ T^i(m) for every i, together with a positive return period. The library's
existing cycle-minimum construction supplies this representation for an
arbitrary positive cycle.

## Two restrictions on inverse branches

Every target v has the even predecessor 2v. An odd predecessor is possible
only when v ≡ 2 modulo 3, and then it is (2v−1)/3.

Two target classes therefore force doubling when following predecessors
inside a positive cycle:

- If v ≡ 1 modulo 3, the odd predecessor does not exist as an integer.
- If v ≡ 5 modulo 9, the odd predecessor exists but is divisible by three,
  so it cannot be part of the cycle.

`forced_double` states this precisely: if T(p)=v, p is not divisible by
three, and v lies in either of these target classes, then p=2v.
The exclusion of multiples of three is essential. The kernel-checked
example T(9)=14 has 14 ≡ 5 modulo 9 and is not a doubling predecessor.
This branch exists in the inverse graph; it is excluded only from cycles.

## Starting at the minimum

The immediate predecessor of m must be 2m. Its odd alternative would be
smaller than m, contradicting minimality. Every forced predecessor is an
attained cycle point, so its size is a lower bound on the cycle maximum.

If m ≡ 2 modulo 3, then 2m ≡ 1 modulo 3, forcing the next predecessor 4m.
This supplies the factor-four bound for residues 2, 5, and initially 8
modulo nine.

If m ≡ 7 modulo 9, the backward chain is forced through

    m ← 2m ← 4m ← 8m.

At 2m the odd branch is a multiple of three, and at 4m there is no odd
branch. If m ≡ 8 modulo 9, the chain is forced through

    m ← 2m ← 4m ← 8m ← 16m.

Here the extra exclusion occurs at 4m, which is 5 modulo nine; 8m then has
no odd inverse branch. The Lean lemmas prove actual attainment of each
endpoint, stronger than just the resulting maximum inequality.

The compact `spreadFactor` definition records the table. Its periodicity
modulo nine and the final `residue_spread` inequality are both proved.
No cycle-length computation or new numerical convergence sweep is used.

## Independent arithmetic tests

The Python probe checks the inverse-branch formula on all 100,000 source
values below 100,000. Among them, 22,222 satisfy the forced-doubling
hypotheses. It also considers every odd candidate minimum below 20,000
that is not divisible by three, filtering inverse branches by both
minimality and exclusion of multiples of three. All 14,444 required inverse
steps agree with the residue table.

At the stated endpoint, the probe finds a remaining odd predecessor
compatible with those two elementary filters. This explains where this
particular forced chain stops in the tested cases; it does not prove that
the predecessor belongs to a cycle, that the maximum can equal the bound,
or that stronger global arguments cannot improve it.

These tests concern necessary inverse arithmetic. They do not construct
hypothetical cycles from the candidate minima or establish convergence.

## Verification

All 12 theorem endpoints are included in the dedicated axiom audit. The
main-library integrity check includes forced doubling, the factor-eight
and factor-sixteen attainment results, and the combined spread inequality.

```sh
lake build Collatz.Structure.CycleInverseSpread
lake env lean scripts/audit_cycle_inverse_spread.lean
python3 scripts/probe_cycle_inverse_spread.py
bash scripts/check_integrity.sh
```

[Lean proof](../Collatz/Structure/CycleInverseSpread.lean),
[axiom audit](CycleInverseSpreadAxioms.txt),
[probe](CycleInverseSpreadProbe.json),
[existing cycle extrema](../Collatz/Structure/CycleExtremes.lean),
[exclusion of multiples of three](../Collatz/Structure/CycleModThree.lean).
