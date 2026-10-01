# Harmonic normalization and finite exceptions

2026-10-01. This is a Lean-core formalization of elementary density theory,
not a new classical theorem and not a proof of the Collatz conjecture.
It supplies semantic foundations for the repaired Tao statement.

## Quantitative normalization

Write H(N) = sum_(1 ≤ n ≤ N) 1/n. The checked block estimate is

    H(N+L) ≥ H(N) + L/D       whenever N+L ≤ D.

For N > 0, this gives 2 H(2N) ≥ 2 H(N)+1. Induction then proves
k ≤ 2 H(2^k), and hence H(2^(2K)) ≥ K for every natural K.
Cutoff monotonicity extends this bound to every larger cutoff. Taking an
integer ceiling gives eventual lower bounds for arbitrary rational thresholds.

These estimates ensure the density normalizer is unbounded. No real logarithm,
external analytic theorem, floating-point calculation, or convergence assumption
is used. The sums are rational; unbounded set membership is classical.

## Finite exceptions

The harmonic weights of a set and its complement sum exactly to H(N).
A set supported in [1,C] has mass at most H(C), at every cutoff. Once H(N)
is at least H(C)/epsilon, its contribution is at most epsilon H(N).
This proves `logDensityOne_of_cofinite` for arbitrary cofinite subsets of Nat.

Two consequences check the interpretation of the Collatz literature:

1. **Conditional implication:** assuming the full Collatz conjecture, the
   repaired rational-valued almost-bounded statement follows. Every orbit then
   reaches 1, and a bound tending to infinity is eventually at least 1. The
   hypothesis remains explicit; this is not Tao's unconditional theorem.
2. **Density is not universal membership:** the set excluding any fixed positive
   integer still has logarithmic density one. A checked witness excludes 2.
   This concerns arbitrary sets, not the actual Collatz basin, and provides
   neither a Collatz counterexample nor an independence result.

## Files and verification

- [Harmonic block proofs](../Collatz/Papers/HarmonicBlocks.lean)
- [Cofinite density and the conditional implication](../Collatz/Papers/CofiniteLogDensity.lean)
- [Seventeen-endpoint axiom audit](HarmonicDensityAxioms.txt)

```sh
lake build Collatz.Papers.CofiniteLogDensity
lake env lean scripts/audit_harmonic_density.lean
```

These are supporting results for the [Tao statement repair](TaoStatementRepair.md).
They do not turn its definition into an unconditional theorem.
