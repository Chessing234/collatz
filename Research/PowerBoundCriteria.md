# Finite exceptions and pointwise power criteria

The supporting density library now proves an explicit finite-exception bound.
If P holds for every n≥B, then its density-one precision-q inequality holds for
all N≥qB. Eventual inclusion P⊆Q loses at most B counted inputs; using twice the
requested precision absorbs this error. Hence finite modifications preserve
natural-density-one status. The empty set and a proper tail distinguish this
notion from a vacuous assertion and from universal membership.

For a fixed start n>1, `PowerBoundCriteria` proves that reaching 1 is equivalent
to reaching below every reciprocal-power target n^(1/q), q>0. In the converse,
the single choice q=n is sufficient: every orbit value at least 2 has nth power
at least 2^n>n. This is a pointwise equivalence, not a consequence of Korec's
almost-all theorem. Universal convergence also implies the recorded rational
Korec statement through the finite-exception density result. The convergence
hypothesis remains unproved.

These are supporting logical and counting results, not claims of historical
novelty. Both modules passed the pinned Lean compiler; twelve proof endpoints
have an axiom audit using only the standard logical axioms.

```sh
lake build Collatz.Papers.PowerBoundCriteria
lake env lean scripts/audit_power_bound_criteria.lean
```

[Counting proofs](../Collatz/Structure/CofiniteNaturalDensity.lean),
[power criteria](../Collatz/Papers/PowerBoundCriteria.lean),
[audit](PowerBoundCriteriaAxioms.txt).
