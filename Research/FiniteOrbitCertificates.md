# Finite certificates for repeats, convergence, and interval exits

The existing library proves that bounded accelerated Collatz orbits enter
cycles. The new development supplies executable Boolean checks with proved
semantics, keeping three different kinds of finite evidence separate:

| Check | Certificate | What it establishes |
| --- | --- | --- |
| `oneSearch n B` | An index t ≤ B+1 with T^t(n)=1 | This start reaches 1 |
| `exitSearch n B` | An index t ≤ B+1 with T^t(n)>B | This particular bound is exceeded |
| `repeatSearch n B` | Indices i<j≤B+1 with equal values, and no 1 through j | Bounded nonconvergence of this start |

`finite_search_complete` proves that at least one check succeeds for every
n and B. If the prefix never exceeds B, it contains B+2 values drawn from
B+1 possibilities, so two positions repeat. If there was no hit on 1, that
repeat is a valid nonconvergence certificate. This proof includes n=0 and
B=0; positivity is not silently assumed.

The alternatives are not disjoint. An orbit may exceed B and later reach 1
within the same finite window. An exit is not a certificate of divergence.

## Why a repeat is enough

If T^i(n)=T^j(n) with i<j, every later value equals one at an earlier index
strictly below j. The formal reduction uses

    s = t,                          when t < i,
    s = i + ((t−i) mod (j−i)),      otherwise.

Lean proves s<j and T^t(n)=T^s(n). The maximum of the finite prefix therefore
bounds the entire orbit. If the prefix avoids 1, so does the entire orbit.

The supplied-certificate checker `repeatCheck n i j` checks the strict
ordering of the indices, equality of the two orbit values, and avoidance of
1 at every index through j. Its soundness theorem gives both global
boundedness and nonconvergence. Its completeness theorem is exact:

    (∃ i j, repeatCheck n i j = true)
      ↔ bounded accelerated orbit ∧ never reaches 1.

This is complete for bounded nonconvergence only. An unbounded orbit cannot
supply a repeat, so this checker is not a complete test for hypothetical
counterexamples of both types.

## What an infinite family of exit checks means

`all_exits_iff_divergent` proves

    (∀ B, exitSearch n B = true) ↔ the accelerated orbit is unbounded.

The forward direction directly supplies values above every bound. For the
reverse, a failed exit check would produce a finite repeat by pigeonhole,
which would make the orbit bounded. Thus an unbounded orbit must exit each
interval by its corresponding finite horizon.

This is still an infinite universal statement. Success for one bound, or
for any tested finite collection of bounds, does not establish it. The
kernel-checked example n=3, B=3 exits the interval, but reaches 1 at time 5.

## Executability and tests

The Lean searches use finite lists of indices, exact natural-number
iteration, and Boolean tests. They are reference implementations intended
for certificate checking and transparent semantics. They recompute orbit
prefixes and search pairs of indices; they are not optimized large-scale
Collatz search software. B+1 bounds the largest time inspected, not the
number of operations or their bit cost.

The independent Python probe checks all 6,565 combinations of starts
0–100 and bounds 0–64. At least one check succeeds in each combination.
There are 3,093 cases where both a hit and an exit succeed, illustrating
why these cannot be treated as exclusive outcomes. All 65 successful
repeat searches belong to start 0. No positive nonconvergence certificate
was found.

The probe additionally verifies 2,241,954 instances of the index-reduction
formula on repeated trajectories, including the trivial 1/2 cycle. The
Lean kernel checks that zero's repeat is accepted, the trivial cycle's
nonconvergence certificate is rejected, and an interval exit can precede
convergence. These tests support the implementation; the formal proofs
establish soundness and completeness with the stated scopes.

## Verification

All 18 theorem endpoints appear in the dedicated axiom audit. Dependencies
are confined to `propext`, `Classical.choice`, and `Quot.sound`, with no
axioms used for the concrete Boolean examples. The main-library integrity
check includes the certificate equivalence, finite-search completeness,
search soundness, and the all-exits equivalence.

The mathematical ingredients are elementary periodicity and pigeonhole
arguments already represented abstractly in the library. This work makes
the finite evidence executable and proves its exact scope; it does not
claim a new historical result or a resolution of Collatz.

```sh
lake build Collatz.Strategy.FiniteOrbitCertificates
lake env lean scripts/audit_finite_orbit_certificates.lean
python3 scripts/probe_finite_orbit_certificates.py
bash scripts/check_integrity.sh
```

[Lean checks and proofs](../Collatz/Strategy/FiniteOrbitCertificates.lean),
[axiom audit](FiniteOrbitCertificatesAxioms.txt),
[probe results](FiniteOrbitCertificatesProbe.json).

The [verified-corridor extension](VerifiedOrbitCorridor.md) connects these
certificates to the existing numerical cycle and convergence bounds. It also
gives a sufficient finite convergence test based on staying within a corridor.
