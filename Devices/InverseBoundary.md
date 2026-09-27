# The inverse boundary in two completions

**Status: the real and 2-adic boundary identities and limits are checked
in Lean. The full audit passes with 255 named endpoints. Collatz remains
unproved. No historical novelty is claimed.**

The preceding [reciprocal-packing result](OrbitReciprocals.md) controls
the nonlinear correction on a hypothetical injective Syracuse orbit.
This note investigates whether the exact inverse formula can then give
a contradiction by comparing real and 2-adic limits. The proposed
comparison fails: its real boundary term is strictly positive and
cannot be replaced by its 2-adic limit, zero.

## The exact finite identity

For a positive odd start n, let a_k=S^k(n), let
`V_k=sum_{i<k} v_2(3a_i+1)`, and define rational quantities

    w_k = 2^V_k / 3^k,
    R_k = w_k a_k,
    B_k = sum_{i<k} w_i/3.

The exact one-step equation `2^v a_(k+1)=3a_k+1` gives

    R_(k+1) = R_k + w_k/3,
    R_k = n + B_k.

These identities are formalized in both completions. The file
[PadicInverseBoundary.lean](../ProofAtlasAttack/CollatzTargetDensity/PadicInverseBoundary.lean)
also defines `rationalRemainder : Nat -> Nat -> Rat` and proves that its
embeddings are exactly the real and 2-adic remainder definitions. Thus
the two limit statements concern the same rational sequence.

## Its real limit

[InverseBoundary.lean](../ProofAtlasAttack/CollatzTargetDensity/InverseBoundary.lean)
proves, for every positive start and every finite k,

    R_k = n exp(E_k),
    E_k = sum_{i<k} log(1+1/(3a_i)).

Under the hypothesis that the entire orbit sequence is injective, the
previously proved correction summability gives

    R_k -> L(n) = n exp(sum_{i>=0} log(1+1/(3a_i))) > 0.

There is also an absolute C>0 such that R_k<=Cn for every such orbit
and every k. The positive inverse terms are summable in the real topology,
and their sum is

    sum_{i>=0} w_i/3 = L(n)-n.

The remainder cannot tend to zero over the reals even without the
injectivity hypothesis: the finite identity always gives R_k>=n>0.
The endpoint `remainder_not_tendsto_zero` records this directly.

## Its 2-adic limit

For every odd start, each valuation is at least one, so V_k>=k.
Three is a 2-adic unit and a_k is an integer. Therefore

    |R_k|_2 <= 2^(-V_k) <= 2^(-k),
    R_k -> 0 in Q_2,
    B_k -> -n in Q_2.

These conclusions require neither injectivity nor convergence of the
Collatz orbit. The joint endpoint
`same_rational_remainders_two_limits` proves that an injective positive
odd orbit would satisfy both the positive real limit and the zero
2-adic limit.

Replacing the real limit of R_k by zero would change the valid real
identity `sum w_i/3=L(n)-n` into `sum w_i/3=-n`. That replacement is
unjustified. This is the gap in the attempted argument examined here.

## An unconditional check of the limit distinction

[TwoTopologyExample.lean](../ProofAtlasAttack/CollatzTargetDensity/TwoTopologyExample.lean)
defines the explicit rational sequence

    q_k = 2^k floor(3^k/2^k) / 3^k.

It proves

    1-(2/3)^k <= q_k <= 1       over the reals,
    |q_k|_2 <= 2^(-k).

Consequently q_k tends to 1 over the reals and to 0 over Q_2. This is
an explicit counterexample to an unconditional transfer of zero limits
between these completions. It is not asserted to be a Collatz orbit,
and it does not rule out an argument using additional arithmetic
properties of Collatz valuation sequences.

The remaining task is to find such a property that excludes an actual
positive integer orbit satisfying the derived conditions. The distinct
limits themselves provide no contradiction. Unknown cycles also remain
unexcluded.

## Sources and verification

The investigation was informed by the framework in Siegel's
[January 2026 Hydra-map paper](https://arxiv.org/html/2601.17030v1), which
explicitly distinguishes convergence in different completions and
presents a correspondence between certain integer values and orbit
behavior. That correspondence is not a proof of universal Collatz
convergence. No theorem from that paper is an assumption in these Lean
files, and this note does not claim to refute that correspondence.

Run in ProofAtlasAttack:

    LEAN_NUM_THREADS=4 python3 scripts/verify.py

The full build completes 5,105 jobs. The
[report](../ProofAtlasAttack/Verification/local-report.json) contains 255
named theorem footprints, including 25 from these three modules. The
[new evidence](../ProofAtlasAttack/Verification/inverse-boundary-axioms.log)
uses only `propext`, `Classical.choice`, and `Quot.sound`. All 1,485 pinned
upstream source hashes are unchanged. All 57 extension source hashes
were independently recomputed against the report with zero mismatches.
