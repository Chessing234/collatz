# Residue-class refinement of the Syracuse energy estimate

**Status: checked in Lean and included in the successful full package audit.
Collatz and linear energy growth remain unproved.** No historical novelty is claimed.

For the actual Syracuse probability law mu_n on Z/3^n Z, let

    E_n = 3^n sum_y mu_n(y)^2.

The residue-class argument proves

    E_(n+1) <= (9/7) E_n                         (n >= 1),
    E_(n+1) <= (5/3) (9/7)^n                    (n >= 0),
    E_n     <= (35/27) (9/7)^n                  (n >= 0).

This improves the preceding [5/3 step bound](SyracuseEnergyUpper.md).
The proof uses the exact law and finite-dimensional Euclidean norms.

## The checked lemma chain

Fix n>=1, write X=Z/3^n Z, and define functions on X by

    p(y) = mu_n(y),
    q(y) = mu_(n+1)(3y+1),
    F(y) = 4y+1.

The existing geometric-memory recurrence and the exact factor-two identity
give

    4 q(y) = q(F(y)) + p(F(y)).

Lean checks the modular arithmetic in this equality, including that
lifting F(y) gives four times the lift of y. Because 4 is a unit modulo
3^n, F is a permutation. It cycles the classes 0,1,2 modulo three.

Let a be the Euclidean norm of p restricted to class 1. The input is zero
on class 0. Multiplication by 2 pairs class 1 with class 2, and the exact
factor-two identity shows that the norm on class 2 is 2a. Consequently,

    Q := sum_y p(y)^2 = 5a^2.

Write b_i for the Euclidean norm of q restricted to class i. Apply the
triangle inequality to the exact recurrence on each class, and reindex
using F:

    4b_0 <= b_1 + a,
    4b_1 <= b_2 + 2a,
    4b_2 <= b_0.

These imply

    63b_1 <= 33a,       63b_2 <= 6a.

Cauchy–Schwarz applied separately on the two nonzero input classes gives

    C := sum_y q(y)p(y)
       <= b_1 a + b_2 (2a)
       <= (33+12)a^2/63
        = Q/7.

Finally, the previously proved energy identity is

    E_(n+1) = 3^n (Q + 2C).

Substitution proves the 9/7 step bound. The base estimate E_1<=5/3 gives
the displayed bounds for every depth. No independence of the parity
sequence of a deterministic integer orbit is assumed.

## Connection to predecessor density

The checked theorem `nine_sevenths_target_density` states that for each
integer A>=1 there are constants K>=1 and d>0 such that, whenever
a>0, a is not divisible by 3, t>=1 and a<=t^A,

    P_a(X) >= d X / [a^2 (9/7)^(K t)]

for all sufficiently large X. Here P_a(X) counts positive integers below
X whose ordinary Collatz orbit reaches a. The constants K,d are independent
of a,t; the eventual cutoff may depend on them. The factor 35/27 from the
energy estimate is absorbed into d.

The denominator still grows exponentially in depth. This does not give a
linear upper bound for E_n. More importantly, the
[Collatz lemma chain](CollatzProofChain.md) still requires the unproved
`EnergyTailGap`: an upper bound on the number of integer orbits staying
above a fixed threshold that is smaller than the proved lower bound.
The formalized inverse-logarithmic rate comparison remains an obstruction
to closing that chain using the cited tail bound alone. This statement
compares available estimates; it does not assert that the actual tail is
large or that Collatz is false.

## Files and reproducible verification

- [Proofs and predecessor corollary](../ProofAtlasAttack/CollatzTargetDensity/SyracuseEnergyClasses.lean).
- [Signature and axiom checks](../ProofAtlasAttack/Verification/SyracuseEnergyClasses.lean).
- [Audit script](../ProofAtlasAttack/scripts/verify.py).
- [Machine-readable report](../ProofAtlasAttack/verification/local-report.json).

Run from `ProofAtlasAttack`:

```sh
LEAN_NUM_THREADS=4 python3 scripts/verify.py
```

The audit rebuilds the package, checks upstream and dependency pins,
scans the checked sources for unfinished proofs and proof escapes, and
checks the transitive axiom footprints of the named endpoints.

This stage's full audit passed on 2026-09-08 with 135 named endpoints, including
12 from this module. Their footprints contain only `propext`,
`Classical.choice`, and `Quot.sound`. All 1,485 pinned upstream source hashes
remained unchanged, and all 41 extension hashes matched that stage's
report. The current report also includes the subsequent finite-cutoff work.
The [audit output](../ProofAtlasAttack/verification/syracuse-energy-classes-axioms.log)
prints the actual energy definition and the new theorem signatures.
