# Bounded corrections to logarithmic height cannot give bounded descent

A logarithmic height is a natural candidate when multiplicative orbit growth
is being studied. The new theorem rules out universally bounded descent for
heights that stay within a fixed additive error of floor(log₂(n+1)).

More precisely, suppose a natural-valued height h satisfies, beyond any fixed
finite exceptional range,

    log₂(n+1) ≤ h(n)+D,       h(n) ≤ log₂(n+1)+D.

For any fixed finite B, it is impossible that every eligible start has a
positive iterate within B steps at which h does not increase. In particular,
no such height supplies uniformly bounded strict descent.

## Reduction to the size-comparison obstruction

Define H(n)=2^h(n). The elementary floor-logarithm bounds yield

    n+1 ≤ 2^(D+1) H(n),       H(n) ≤ 2^D (n+1).

A nonincrease of h is also a nonincrease of H. The previously checked
[two-sided size-comparison obstruction](ComparableHeightObstruction.md)
therefore applies with factors A=2^(D+1) and C=2^D.

The error may depend arbitrarily on n. The theorem includes residue-based
and binary-digit-based corrections and does not assume their periodicity or
computability. A separate corollary states the result for h(n)=log₂(n+1)+c(n)
with 0≤c(n)≤D.

This conclusion is narrower than excluding every height of order log(n).
Multiplicative upper and lower comparisons to log(n) can allow an unbounded
additive error. Such heights, and schedules with input-dependent unbounded
horizons, remain outside this result. No historical novelty is claimed.

## Checks

The Lean module builds and its four endpoints pass the standard axiom audit.
The independent probe tests the exponentiation comparison at 40,000 inputs
across four height families. It also follows 216 adaptive candidate schedules
through prescribed all-odd runs, finding a state with no available
nonincrease choice in every case. The largest tested witnesses have 860 bits.
The proof establishes the unbounded statement; these finite checks support
the implementation.

```sh
lake build Collatz.Strategy.LogarithmicHeightObstruction
lake env lean scripts/audit_log_height.lean
python3 scripts/probe_log_height.py
```

[Lean proof](../Collatz/Strategy/LogarithmicHeightObstruction.lean),
[audit](LogHeightAxioms.txt), [probe](LogHeightProbe.json).
