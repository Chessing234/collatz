# The diagonal stopping-time formulation

The historical paper wrapper counts starts in [1,N] which descend by step N.
This statement now has a checked proof, `diagonalDensityOne_proved`.

The proof uses the uniform finite-window estimate. For each positive integer
precision q, choose horizon H=160q and a counting cutoff at least

    max(2q (H3^H+1+2^H), H).

Above this cutoff, at most N/q inputs have no descent by H. Monotonicity of the
bounded checker allows its horizon to increase from H to N. The count convention
is handled explicitly: zero never passes the checker, and the count on [1,N]
contains the count on [0,N).

The rational bridge chooses a positive integer q with 1≤eps·q for each eps>0.
It converts (q−1)N≤qC into (1−eps)N≤C using ordered rational arithmetic.
`densityOne_rat_bound` supplies the same conversion for any predicate satisfying
the library's integer-precision density definition.

This argument establishes the actual diagonal statement, using its original
bounded Boolean predicate and positive counting interval. It relies on uniform
finite-window estimates; pointwise existence of finite stopping times alone
is not the step used to justify the growing horizon.

All four new modules build through the paper wrapper. Eleven proof endpoints
have an axiom audit containing only standard Lean logical axioms. These are
formal bridges for the classical stopping-time theorem, not new historical
results or a proof of universal convergence.

```sh
lake build Collatz.Papers.TerrasDiagonal
lake env lean scripts/audit_terras_diagonal.lean
```

[Bounded counting](../Collatz/Structure/BoundedStoppingCounting.lean),
[rational precision](../Collatz/Structure/RationalDensityPrecision.lean),
[positive counts](../Collatz/Structure/PositiveCounting.lean),
[paper theorem](../Collatz/Papers/TerrasDiagonal.lean),
[audit](TerrasDiagonalAxioms.txt).
