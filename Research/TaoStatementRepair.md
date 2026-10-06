# Repairing the core Tao theorem statement

2026-10-01. This change repairs a vacuous proposition in
[`Collatz/Papers/Tao2022.lean`](../Collatz/Papers/Tao2022.lean).
It does not prove Tao's theorem and does not alter the separate Mathlib-based
extension's imported development.

The previous `taoAlmostBoundedOrbits` quantified over a growth function,
an error tolerance, and a cutoff, but concluded `True`. Consequently its
truth was independent of the Collatz orbit. Calling it a recorded statement
of Tao's theorem was inaccurate.

The replacement explicitly defines:

- `harmonicMass P N`: the sum of 1/n over positive n ≤ N satisfying P;
- `LogDensityOne P`: for each positive rational epsilon, eventually that mass
  is at least (1-epsilon) times the full harmonic mass;
- `OrbitBelow n b`: some standard Collatz iterate of n is at most b;
- `taoAlmostBoundedOrbits`: for every rational-valued growth function tending
  to infinity, the corresponding `OrbitBelow` set has logarithmic density one.

The normalization is by the harmonic sum, not by the count N. Membership
uses an unbounded existential over iterates; there is no implicit finite
search limit. The rational-valued formulation is a restriction of the paper's
real-valued statement. This file does not prove its equivalence to the full
real-valued formulation or reprove the published result.

Six elementary checks compile: empty cutoff, empty set, singleton cutoff,
reaching-one implication, starting-value implication, and impossibility of
reaching a nonpositive bound from a positive start (the last theorem uses
bound zero). The [audit](TaoStatementAudit.txt) prints the three proposition
definitions and the theorem footprints. No Collatz theorem is asserted by
these definition checks.

```sh
lake build Collatz.Papers.Tao2022
lake env lean scripts/audit_tao_statement.lean
```

Source: [Tao, *Almost all orbits of the Collatz map attain almost bounded
values*, Forum Math. Pi 10 (2022), e12](https://arxiv.org/abs/1909.03562).
The paper gives logarithmic-density-one control for any bound tending to
infinity; this is neither universal convergence nor a fixed bound for all starts.

The follow-up [`TaoDensityChecks.lean`](../Collatz/Papers/TaoDensityChecks.lean)
proves nine further semantic checks. In particular, `not_logDensityOne_empty`
refutes density one for the empty set; full harmonic mass is strictly positive
at every positive cutoff. Set inclusion preserves harmonic mass inequalities
and logarithmic density one, and increasing the allowed orbit bound preserves
the almost-everywhere conclusion. These tests guard the statement's meaning,
not the validity of Tao's full argument. All fifteen checked helper endpoints
use only the standard Lean axioms listed in the audit.
