# Local parity rules dominate the long corridor test

The earlier 14,186-step corridor criterion is correct, but unnecessarily
weak for the actual Collatz branches. Lean now proves a stronger test using
only two accelerated transitions, and then simplifies it to direct entry
into the already verified range.

For the current verified cutoff V = 3,998,720, the three criteria form a
proved chain of acceptance implications:

    Stay below 4,012,906 through time 14,186
      ⇒ stay below 7,997,440 through time 2
      ⇒ enter the range below 3,998,720 by time 2.

For positive starts, each criterion implies eventual convergence. Both
implications are strict, as witnessed by kernel-checked examples. The direct
range-entry check is therefore the preferred test among these three.

## The local arithmetic observation

No three consecutive accelerated orbit values can all lie in [V,2V).
For V=0 the interval is empty. Otherwise:

- If the first value is even, halving a value below 2V produces a value below V.
- If the first value is odd but the next is even, the second transition does
  the same thing.
- If both are odd, two transitions increase the value by at least a factor
  9/4, forcing it above 2V when it started at or above V.

`no_three_in_band` proves this using natural-number arithmetic and the two
branches of the accelerated map. It assumes no convergence result, cycle
bound, or density statement.

Therefore a positive orbit whose first three values are all below 2V must
enter [1,V) during those steps. A verified convergence theorem below V then
supplies convergence of the original start. The proof does not assert that
1 itself is reached within two steps.

## A simpler and stronger executable check

`twoStepVerified V n` tests whether n, T(n), or T²(n) is below V. Its exact
Boolean semantics and convergence implication are proved in Lean. Unlike
the corridor check, it does not reject a start merely because another value
in the same short prefix exceeds 2V.

The two strict examples are:

| Start | Long corridor | Two-step corridor | Direct verified hit |
| --- | --- | --- | --- |
| 4,012,906 | false | true | true |
| 7,997,440 | false | false | true |

In the second row, the orbit begins 7,997,440 → 3,998,720 → 1,999,360. The
last value is inside the verified range, despite the starting value being
at the wider corridor's excluded boundary.

A false result from any of these tests is inconclusive. It does not establish
nonconvergence. Positivity remains essential: the checks themselves can
accept zero, while their convergence theorems require a positive input.

## What hypothetical counterexamples must do

The contrapositive has a useful local form. Every positive nonconvergent
orbit must contain a value at least 2V in each window of three consecutive
values. Otherwise that window would enter the verified range and imply
convergence. `every_local_window` proves this for arbitrary verified V.

This strengthens the numerical exit constraint obtained from the earlier
pigeonhole/cycle argument: it uses a higher threshold and a much shorter
window. It does not imply divergence, since a hypothetical large cycle
could also meet the condition in every window.

The earlier general corridor theorem remains a correct combination of a
verified range and a cycle bound. This comparison records why exploiting
the actual branch arithmetic is better than that counting argument for
these particular constants. Neither result is claimed as historically new.

## Verification and finite comparison

The independent probe checks the local band exclusion on 500,500 cases.
It compares the three executable tests on 1,402 starts: 1–1,000, a window
around the old corridor boundary, and a window around the new boundary.
Acceptance counts are 1,029, 1,201, and 1,227 respectively. Every sampled
start was independently followed to 1 within an explicit finite cap,
including those rejected by all three tests.

The module's 13 theorem endpoints are audited, and the principal endpoints
are included in the main-library integrity check. The general local proof
does not require the cycle-length theorem, even though it reuses the scan
interface from the earlier corridor module. The current numerical
specialization relies on the existing verified initial range.

```sh
lake build Collatz.Strategy.LocalOrbitCorridor
lake env lean scripts/audit_local_orbit_corridor.lean
python3 scripts/probe_local_orbit_corridor.py
bash scripts/check_integrity.sh
```

[Lean proof and direct checker](../Collatz/Strategy/LocalOrbitCorridor.lean),
[axiom audit](LocalOrbitCorridorAxioms.txt),
[probe](LocalOrbitCorridorProbe.json),
[earlier general corridor argument](VerifiedOrbitCorridor.md).
