# A stronger unconditional Syracuse energy bound

The subsequent [residue-class refinement](SyracuseEnergyClasses.md) sharpens
the step factor to 9/7 at positive input depth. This page records the
preceding 5/3 argument, which supplies the base estimate for that refinement.

**Status: checked in Lean for every depth. This is not a proof of Collatz
or of linear energy growth.** No historical novelty is claimed.

For the actual imported Syracuse probability law mu_n on Z/3^n Z, define

    E_n = 3^n sum_y mu_n(y)^2.

The new local theorem proves

    E_(n+1) <= (5/3) E_n,     E_n <= (5/3)^n.

This improves the previous elementary bound E_n<=2^n. It retains an
exponential dependence on depth.

## Why the factor is 5/3

The geometric-memory recurrence was already proved for the actual law:

    mu_(n+1)(r/2) = [mu_(n+1)(r) + input_n(r)]/2,

where input_n is the injection of mu_n at r=3y+1. All residues here are
taken in Z/3^(n+1) Z. No input is injected in class 2 modulo 3. Substituting
r=2(3y+1) gives the exact relation

    mu_(n+1)(2(3y+1)) = 2 mu_(n+1)(3y+1).

The maps y->3y+1 and y->2(3y+1) are injective and have disjoint images.
Consequently, five times the squared mass on the first image is at most
the total squared mass: the paired second image contributes four times
as much.

Write

    Q = sum_y mu_n(y)^2,
    R = sum_r mu_(n+1)(r)^2,
    L = sum_y mu_(n+1)(3y+1)^2,
    C = sum_y mu_(n+1)(3y+1) mu_n(y).

The proved energy recurrence gives 3R=Q+2C. The disjoint-image estimate
gives 5L<=R, and Cauchy-Schwarz gives C^2<=LQ. Combining them yields

    15 C^2 <= Q^2 + 2CQ,
    (3C-Q)(5C+Q) <= 0.

Since Q,C>=0, this forces 3C<=Q. Hence R<=5Q/9, and multiplication by
3^(n+1) gives E_(n+1)<=(5/3)E_n. Induction starts from E_0=1.

The bound uses the exact relation between residue classes, rather than
assuming uniformity or independence of their masses.

## Connection to the predecessor theorem

The checked corollary `five_thirds_target_density` states that for every
integer A>=1 there exist K>=1 and d>0 such that, for every a>0 with 3 not
dividing a, every t>=1 with a<=t^A, and every sufficiently large X,

    P_a(X) >= d X / [a^2 (5/3)^(K t)].

P_a(X) counts positive integers below X whose ordinary Collatz orbit
reaches a. K,d are independent of a,t; the cutoff in X may depend on a,t.
This follows by inserting the energy bound into the existing unconditional
estimate P_a(X)>=dX/[a^2 E_(Kt)]. No bound on hitting time is imposed.

The estimate does not supply the upper tail needed in the
[least-counterexample chain](CollatzProofChain.md). In particular it does
not establish the separate hypothesis E_n<=Bn used by the conditional
cubic-density theorem.

## Source checks and verification

The formal proof uses only the pinned Tao-Mazur law and the earlier local
energy identity. The related external [R9 correlation probe](https://github.com/mrnathanhumphrey-droid/Collatz/blob/main/results/result_gamma_R9.md)
labels its off-diagonal convergence section as a measurement over finitely
many depths. That section does not provide an all-depth correlation upper
bound to import. Its finite observations are not assumptions here.

- [Proof and predecessor corollary](../ProofAtlasAttack/CollatzTargetDensity/SyracuseEnergyUpper.lean)
- [Verification source](../ProofAtlasAttack/Verification/SyracuseEnergyUpper.lean)

From `ProofAtlasAttack`, reproduce the full check with
`LEAN_NUM_THREADS=4 python3 scripts/verify.py`.

This stage's full check passed on 2026-09-08 with 123 audited endpoints,
including all eight from this module. Their transitive axiom footprints contain
only `propext`, `Classical.choice`, and `Quot.sound`. All 1,485 upstream
source hashes remained unchanged, and all 40 extension hashes matched
that stage's report. The current [report](../ProofAtlasAttack/verification/local-report.json)
also includes the subsequent residue-class refinement.
The [audit output](../ProofAtlasAttack/verification/syracuse-energy-upper-axioms.log)
prints the actual energy definition and the literal new theorem signatures.
