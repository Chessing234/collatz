# Reciprocal packing and divergent-orbit discrepancy

**Status: this chain is checked in Lean and included in the successful
230-endpoint audit. It proves necessary conditions on an injective
Syracuse orbit. It does not prove that such an orbit is impossible, and
Collatz remains unproved. No historical novelty is claimed.**

A subsequent [inverse-boundary check](InverseBoundary.md) derives the real
limit of the exact inverse remainder and distinguishes it from its zero
2-adic limit. The current package audit includes that work and has 255
named endpoints.

Let S(a)=(3a+1)/2^v, where v is the exact exponent of two dividing 3a+1,
and let a_i=S^i(n), with n positive and odd. Suppose all a_i are distinct.
The new theorems establish an absolute constant C>0 such that

    sum_{i>=0} 1/a_i <= C.

They also establish

    k log 3 - (sum_{i<k} v_2(3a_i+1)) log 2 -> +infinity.

The second conclusion is additive divergence. It does not assert a
positive linear rate or a fixed gap in the limiting valuation average.
The formal hypotheses require injectivity of the entire sequence i->a_i.
They do not merely require that the initial value never returns: an
orbit that later enters a cycle is excluded from these hypotheses.

## From backward density to a finite packing bound

[SyracusePacking.lean](../ProofAtlasAttack/CollatzTargetDensity/SyracusePacking.lean)
first derives the analogue of the
[harmonic predecessor theorem](HarmonicPredecessors.md) for odd Syracuse
predecessors of nonperiodic roots. There are absolute d>0 and A>=1 such
that their logarithmic counting ratio is at least d/b at every
X>=(A*b)^2, for a positive odd root b prime to three that never returns
to itself.

For a finite family of pairwise disjoint predecessor sets, the sum of
these ratios is at most one, at every positive cutoff. Choose a common
cutoff larger than all their activation bounds. It follows that

    sum_{b in the family} 1/b <= 1/d.

The proof uses finite sums of actual indicator functions. It does not
interchange an infinite family with a density limit or assume that a
density limit exists.

## Disjoint branches along a forward orbit

[OrbitReciprocals.lean](../ProofAtlasAttack/CollatzTargetDensity/OrbitReciprocals.lean)
defines an explicit side branch

    side(a) = 16a+5  if a mod 3 = 2,
              4a+1  otherwise.

For a>0 this is odd, prime to three, different from a, and at most 21a.
It has the same next Syracuse value as a. Along an injective orbit,
write b_i=side(a_i). None of these b_i occurs anywhere on the orbit:
an equality b_i=a_j would give a_(i+1)=a_(j+1), hence i=j, contradicting
side(a_i)!=a_i.

After its first step, the orbit of b_i follows the original orbit.
Consequently b_i is nonperiodic and cannot reach another b_j with i!=j.
If two b_i had a common predecessor, determinism would force one to
reach the other. Their predecessor sets are therefore pairwise disjoint.

The packing bound now applies to every finite selection of the b_i.
Since b_i<=21a_i,

    sum_{i in F} 1/a_i <= 21 sum_{i in F} 1/b_i <= 21/d.

Nonnegativity and a bound for every finite F prove convergence of the
series and the absolute bound on its sum. The key endpoints are
`uniform_orbit_reciprocal_bound`, `orbit_reciprocals_summable`, and
`orbit_reciprocals_uniform_tsum`.

## Retaining the nonlinear correction

[OrbitDiscrepancy.lean](../ProofAtlasAttack/CollatzTargetDensity/OrbitDiscrepancy.lean)
uses the exact identity

    log a_k = log n + D_k + E_k,
    D_k = k log 3 - (sum_{i<k} v_2(3a_i+1)) log 2,
    E_k = sum_{i<k} log(1+1/(3a_i)).

Each correction lies between zero and 1/(3a_i). Thus E_k is bounded by
an absolute constant; the series of corrections is also summable.
An injective sequence of natural numbers tends to infinity, so log a_k
tends to infinity. Subtracting the bounded correction proves D_k tends
to positive infinity. The endpoint is `discrepancy_tendsto_atTop`.

This identifies a precise constraint on a hypothetical divergent orbit.
There is no proved upper bound contradicting it. Statistical statements
about typical valuations do not establish such an upper bound for every
individual orbit. Unknown cycles remain a separate possibility.

## Prior work and verification

Related prior work includes Garcia and Tal,
[A note on the generalized 3n+1 problem (1999)](https://doi.org/10.4064/aa-90-3-245-250).
A [July 2026 discussion](https://mathoverflow.net/questions/513539/is-it-known-that-a-divergent-collatz-trajectory-must-have-summable-reciprocals)
explicitly discusses reciprocal summability and additive discrepancy as
consequences of their orbit estimates. The original article's full text
could not be retrieved in this session, so that proposed derivation has
not been independently audited here. The Lean proof above instead uses
the repository's checked predecessor-density machinery and elementary
finite packing; no assertion from that discussion is an assumption.

Run in ProofAtlasAttack:

    LEAN_NUM_THREADS=4 python3 scripts/verify.py

The full build completes 5,099 jobs. The
[report](../ProofAtlasAttack/Verification/local-report.json) verifies 230
named endpoints, including 20 from these three files. The
[new axiom evidence](../ProofAtlasAttack/Verification/orbit-reciprocals-axioms.log)
contains only `propext`, `Classical.choice`, and `Quot.sound`. All 1,485
upstream source hashes are unchanged. All 54 extension source hashes
were independently recomputed against the report with zero mismatches.
