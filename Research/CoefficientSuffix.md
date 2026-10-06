# Selecting a suffix with no coefficient crossing

2026-09-28. Conditional bridge, not a proof of Collatz and not a novelty claim.

For positive coefficients c_i define P_0=1 and
P_k=product_{i<k}(c_i/3). For Syracuse trajectories c_i=2^a_i, so P_k
is the inverse multiplicative coefficient. A coefficient crossing occurs
when P_k>1; this orientation matters.

**Proved in core Lean:** if there is N such that P_k<=1 for every k>=N,
then there is m<=N such that every multiplier relative to m is at most one:

    product_{i<k}(c_(m+i)/3) <= 1, for all k.

Proof: the tail is bounded by P_0, so P has a global maximum at some m<=N.
The relative product is P_(m+k)/P_m, and P_m>0. It cannot exceed one.
Only a finite maximum is needed. The proof does not silently assume that
an arbitrary bounded infinite sequence attains its supremum.

The contrapositive is also formalized: if every suffix has a coefficient
crossing, then P_k>1 at arbitrarily late indices.

## Connection to the existing proof attempt

The earlier Mathlib file `OrbitDiscrepancy.lean` states that an injective
positive Syracuse orbit has discrepancy D_k tending to positive infinity,
using reciprocal summability. `InverseBoundary.lean` identifies P_k=exp(-D_k).
If those results are supplied, P_k tends to zero and the hypothesis above
follows. Thus that analytic route would select a suffix with no coefficient
crossing on any hypothetical injective orbit.

This connection is a mathematical composition of the displayed statements;
the cross-package composition has NOT been compiled in the current workspace,
whose Mathlib dependency cache is absent. The new core theorem proves the
selection step with the explicit eventual bound as a hypothesis. It does not
replace the analytic premise with an axiom.

## Remaining obligations

To use this route to exclude injective integer orbits, one still needs a
theorem giving a coefficient crossing for every relevant integer start.
No such theorem is obtained here. To conclude Collatz, nontrivial cycles
must also be excluded. The finite first-light theorem through step 128
establishes neither missing assertion.

We also corrected explanatory text in `CoefficientStopping.lean`: permitting
both stopping times to be infinite is not a proof that one conjecture is
strictly weaker than, or does not imply, Collatz. No independence or actual
divergent integer example was supplied there. Its conditional cycle theorem
is unchanged.

## Verification

    lake build Collatz.Strategy.CoefficientSuffix
    lake env lean scripts/audit_coefficient_suffix.lean

Six endpoints, standard Lean axioms only; no sorry, new axioms, native_decide,
or unsafe declarations. Logs: `CoefficientSuffixBuild.txt` and
`CoefficientSuffixAudit.txt` in this directory. This is a targeted audit,
not a rerun of every historical theorem in the repository.
