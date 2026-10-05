# Finite rational shadow certificates

Date: 2026-09-28. Status: a proved finite certificate device; not a proof of
Collatz, and historical novelty is unverified.

## The theorem

Consider two length-L integer trajectories satisfying

    c_i x_(i+1) = 3 x_i + 1,
    d_i y_(i+1) = 3 y_i + 1,

with even natural coefficients c_i and d_i. Actual odd-to-odd Collatz
trajectories are instances, with coefficients powers of two. The theorem
is more general and does not assume the terminal states are odd.

A rational sample sequence s_0,...,s_L certifies a coefficient c_i if

    s_(i+1) >= 1,
    |c_i s_(i+1) - 3 s_i + 1| < 1.

If the SAME samples certify both trajectories, then 2^L divides both
directed natural differences of their starting values. Consequently, if
|x_0-y_0| < 2^L, the starts are equal.

This is `certificate_unique` in `Collatz/Strategy/ShadowDecoder.lean`.
It concerns residual error, not an arbitrary absolute error in every sample.

## Proof and precision

Distinct even coefficients differ by at least two. Since the next sample
is at least one, their residuals differ by at least two; two residuals
strictly between -1 and 1 cannot do that. Thus c_i=d_i at every step.

Subtracting the two trajectory equations removes the affine constant.
Each common even coefficient contributes a factor of two to the initial
difference; multiplication by three cannot remove this divisibility.
Induction gives the 2^L bound. A nonzero multiple of 2^L cannot have smaller
absolute value.

The strict local tolerance one is sharp: samples (4/3,1) give residuals
-1 and +1 for coefficients 2 and 4. This is sharpness of the LOCAL decoder,
not a claim that the global length bound is optimal for odd trajectories.

`approximation_fits` checks a sufficient sampling budget: when rational
exact values (u,v) obey c v=3u-1, errors at most delta in each sample are
acceptable if (c+3)delta<1 and the next sample remains at least one.

## Constructive encoder and its limitation

For any finite coefficient word with c_i>=2, set e_L=1 and recursively set
e_i=(c_i e_(i+1)+1)/3. All e_i>=1 and all residuals vanish. The functions
`encode`, `encode_ge_one`, `encode_exact`, and `encode_fits` formalize this.

Thus arbitrary finite words admit exact certificates. No infinite orbit,
bounded infinite shadow, or compatible family with a fixed initial shadow
is asserted. Existence of these finite certificates cannot by itself give
universal descent. The encoder is finite and does not use the uncomputed
future of an infinite integer orbit.

For 7,11,17,13,5,1, rounded samples

    9.86, 14.29, 20.93, 15.45, 5.67, 1

have residuals 0,-0.01,0.01,0.01,-0.01 for coefficients 2,2,4,8,16.
The audit checks these as exact rationals, not floating-point calculations.

## Novelty check and relation to existing work

The arithmetic coding ingredient is classical: Rozier, *The 3x+1 Problem:
A Lower Bound Hypothesis*, Theorem 2.1, attributes finite parity-vector
coding modulo powers of two to Terras and Everett:
https://www.ipgp.fr/~rozier/pub/LBHv4.pdf
That theorem is about shortened-map parity vectors; the present statement
uses even coefficients and rational residual certificates. This distinction
does not establish research novelty for an elementary consequence.

Inspected also the public primary research notes
https://github.com/docbgm2002/collatz-things/blob/main/docs/no-go/shadow_certificate.md
Their shadow certificate concerns negative-cycle shadowing and limitations
of certain local potentials, rather than the residual decoder here. Those
claims were not imported into this proof or independently audited.

Searches included Collatz with noisy shadow, robust decoding, residual
decoder, inverse series error coding, and rational shadow unique. No exact
match to the present formulation was identified in inspected material.
Search non-detection is not proof of priority. The elementary rounding
argument and the classical divisibility argument are not claimed as novel.
The contribution here is an additional finite, noise-tolerant certificate
interface in this workspace, with a constructive encoder and explicit scope.

Earlier workspace `ProofAtlasAttack/.../ShadowRigidity.lean` already recovers
coefficients from close exact shadow pairs. This file adds rational residual
certificates, finite start uniqueness, local sharpness, and a finite encoder;
it does not claim to introduce the shadow coordinate itself.

## Verification

Lean 4.33.0-rc1, core library only. Target:

    lake build Collatz.Strategy.ShadowDecoder
    lake env lean scripts/audit_shadow_decoder.lean

Build evidence: `Research/ShadowDecoderBuild.txt`.
Axiom and concrete-example audit: `Research/ShadowDecoderAudit.txt`.
The ten public theorem endpoints use only the standard axioms propext,
Classical.choice, and Quot.sound (or subsets). No added axioms, sorry,
unsafe declarations, or native_decide. This audit covers this module and
its imported proof dependencies, not all historical project results.

The separate Mathlib package's dependency cache is absent in the current
workspace. No earlier Mathlib audit is represented as rerun in this work.
