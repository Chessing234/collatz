# Residue-monotone heights: a bounded-horizon obstruction

2026-10-01. The eight endpoints in
[`ResidueMonotoneObstruction.lean`](../Collatz/Strategy/ResidueMonotoneObstruction.lean)
compile in Lean 4.33.0-rc1. This is an obstruction to a specified proof strategy,
not a proof or disproof of Collatz. No historical novelty is claimed.

## Statement and argument

Let M be any positive modulus, B any finite horizon, and C any cutoff.
There is n > max(C,1) such that for every 1 ≤ i ≤ B,

    T^i(n) > n,       T^i(n) ≡ n (mod M).

Here T is the accelerated map with one division by two per step.
For any positive q, use n = M q 2^(B+1) - 1. The exact identity is

    T^i(n) = M q 3^i 2^(B+1-i) - 1.

All these values are -1 modulo M, and 3^i > 2^i gives strict growth.
Taking q = C+3 places the entire witness beyond the cutoff.

Suppose H is a natural-valued height that increases within each residue class:

    x < y and x ≡ y (mod M) imply H(x) < H(y).

The witness forces H(T^i(n)) > H(n) for every positive i ≤ B. Thus no bounded
schedule can make H descend on every sufficiently large starting value.
The same proof rules out choosing a stopping length from any finite menu.
The class includes H(n) = a_(n mod M) n + b_(n mod M) with every a_r > 0 and
natural offsets b_r, even with completely unrelated slopes between classes.

## What this adds, and what it leaves open

The repository already has the Mersenne witness in `DensitySaturation` and,
more directly, the same-modulus returning witness in
[`AnyModulusRanking`](../Collatz/Strategy/AnyModulusRanking.lean). The latter
rules out class-constant ranks at a fixed positive time, in arbitrary codomains.
The contribution here is the simultaneous whole-run statement, witnesses above
any cutoff, and natural-valued heights increasing within classes rather than
constant there. A further theorem permits weak nondecrease only above the
cutoff, unifying class-constant and increasing heights for bounded schedules.
The elementary orbit identity is reproved using only `Collatz.Accelerated` to
keep this check independent of the large finite-verification dependency chain.
It does not exclude unbounded stopping times, heights that decrease along
some residue classes, dynamically changing moduli, or arbitrary ranking
functions. The Lean height theorem currently has natural-valued codomain.
The positive integers witnessing different horizons need not be the same;
this argument constructs no infinite rising positive-integer orbit.

## Verification

```sh
lake build Collatz.Strategy.ResidueMonotoneObstruction
lake env lean scripts/audit_residue_monotone.lean
python3 scripts/probe_residue_monotone.py
```

The [axiom audit](ResidueMonotoneAxioms.txt) contains eight endpoints, with
only `propext` and `Quot.sound` (the affine-height lemma uses no axioms).
The independent [integer probe](ResidueMonotoneProbe.json) checks 5,280
starting values and 84,480 positive-time instances, including modulus one
and horizon zero. The universal result rests on Lean, not those samples.

## Classical results guiding the investigation

- [Terras (1976), *A stopping time problem on the positive integers*](https://www.impan.pl/en/publishing-house/journals-and-series/acta-arithmetica/all/30/3/101028/a-stopping-time-problem-on-the-positive-integers):
  the classical finite-stopping-time density result motivates looking for
  the missing passage from almost every input to every input. The publisher
  citation was retrieved; the original PDF was unavailable during this pass.
  Existing repository work includes coefficient stopping and density bounds.
- [Krasikov and Lagarias (2003)](https://arxiv.org/abs/math/0205002):
  difference inequalities give an exponent 0.84 lower bound for the number
  of starts reaching 1. This is a counting theorem, not universal descent.
  The repository's similarly named core proposition allows a weaker exponent;
  its name alone should not be read as a formal proof of the published exponent.
- [Tao (2022)](https://arxiv.org/abs/1909.03562):
  for any bound tending to infinity, almost every orbit reaches below that
  bound in logarithmic density. It does not say every orbit reaches 1.
  This motivates controlling exceptional sets; it cannot supply a uniform
  finite horizon, which the elementary witness above already excludes.

These are source-guided comparisons, not new formalizations of the three
complete published proofs. The repository's literature wrappers must be
inspected to distinguish theorem statements from proofs and placeholders.
