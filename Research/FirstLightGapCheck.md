# Compact first-crossing certificate infrastructure

2026-10-01. `FirstLightGapCheck` replaces the triangular table over lengths
and odd counts with a linear scan over lengths. At each length k it verifies
an upper candidate a for the light counts:

    2^k ≤ 3^(a+1),    a 3^a < 3 (2^k − 3^a) N.

Every light b then satisfies b≤a. The numerator b 3^b increases with b,
whereas the gap 2^k−3^b decreases. Thus the single checked inequality implies
all inequalities needed at that length. The candidate-update heuristic is
untrusted: the soundness theorem only uses the checked inequalities.

Kernel reduction confirms the entire gap certificate through H=1024 with
N=99730, as well as the previous H=256, N=6701 certificate. **A gap certificate
alone does not establish first-crossing descent:** the exceptional starts
below N must also be checked. The larger exceptional-start build is separate.

`FirstLightIntervals` supplies soundness, completeness, adjacent-interval
composition, and horizon monotonicity for small-start certificates. Composition
allows independently checked chunks to be reused without reducing their orbit
tests again. This is verification infrastructure, not a new Collatz theorem or
an assertion of historical mathematical novelty.

Validation: both modules build; the nine exported proof endpoints have been
audited for axioms. The gap certificates themselves have no axioms. Other
endpoints use only Lean's standard logical axioms. Full repository integration
remains a separate long-running check.

```sh
lake build Collatz.Strategy.FirstLightGapCheck Collatz.Strategy.FirstLightIntervals
lake env lean scripts/audit_first_light_gap_check.lean
```

[Source](../Collatz/Strategy/FirstLightGapCheck.lean),
[interval interface](../Collatz/Strategy/FirstLightIntervals.lean),
[axiom audit](FirstLightGapCheckAxioms.txt).
