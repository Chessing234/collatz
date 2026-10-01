# A proved 4/5 power-density theorem for Collatz

The core-only Lean development now proves that a natural-density-one set of
starting values n has an actual accelerated Collatz iterate m with

    m^5 < n^4.

The endpoint is `Collatz.Papers.Korec1994.four_fifths_density_one`. An additional
integer-power comparison proves density one for every positive rational
exponent p/q≥4/5. This is a formal reconstruction of a specialization of
[Korec's classical theorem, Theorem 1](https://www.dml.cz/handle/10338.dmlcz/133225),
not a new mathematical result. Korec's published range is c>log₄(3). The small
interval between log₄(3) and 4/5 is outside this specialization. The subsequent
[general certificate proof](KorecCertified.md) now proves the full recorded
`rationalExponentStatement`, while retaining this independent specialization.

Density one allows exceptional starting values. This theorem does not prove
universal convergence, exclude nontrivial cycles, or justify interchanging
the density quantifier with a quantifier over all reciprocal exponents.

## Proof components

The [parity moment identity](ParityMoments.md) supplies the tail estimate

    W^s E(s) ≤ A^s,
    W = 63^63·62^62,    A = 125^125,

where E(s) counts residues modulo 2^(125s) having at least 63s odd steps.
The checked strict gap A<2^125·W, together with an integer Bernoulli estimate,
shows q·E(s)<2^(125s) at all s≥q·A. These explicit thresholds are extremely
coarse; their purpose is to prove eventual bounds without real analysis.

The orbit estimate includes the affine correction. If n≤L·2^k and a is its
odd-step count, the exact affine identity gives

    T^k(n) ≤ (L+1)·3^a.

For k=125s, a≤63s, and n≥2^(125s), the separate gap 3^315<2^500 implies
T^k(n)^5<n^4 once s≥(L+1)^5·3^315. Thus every failure in the scale interval
has a high odd-step count.

For a requested count precision q>0, the proof sets

    D = 2q,
    L = D·2^125,
    S = max(4q·125^125, (L+1)^5·3^315),
    N₀ = D·2^(125S).

For each N≥N₀, a floor-logarithm argument chooses s≥S such that

    D·2^(125s) ≤ N < L·2^(125s).

Writing M=2^(125s), the failure count F(N) is bounded by

    F(N) ≤ M + (floor(N/M)+1) E(s).

The first term covers the discarded prefix. The second counts the periodic
parity tail, including a final incomplete period. Since 2qM≤N and 4qE(s)≤M,
elementary integer arithmetic gives qF(N)≤N. Complementary counting then gives
the repository's exact natural-density-one predicate.

The horizon depends on N, but the proof controls that dependence explicitly.
It does not exchange a fixed-horizon limit with an unbounded-horizon limit.

## Verification and limits

The seven new modules build under the pinned Lean compiler. All 21 endpoints,
including the final density theorem, pass an axiom audit using only `propext`,
`Classical.choice`, and `Quot.sound`. There are no assumptions of universal
convergence or of the recorded Korec statement in the proof.

An independent probe checks 1,760 geometric inequalities, 560 scale choices,
4,096 prefix-plus-period estimates, and 280 actual orbit upper bounds with
inputs up to 8,007 bits. Of the latter samples, 86 satisfy the direct scale-gap
certificate, and all 86 satisfy the asserted power target. A separate scan
finds a power-target iterate for every 2≤n<10000, requiring at most 111 steps.
Finite tests do not establish density; the Lean proof provides that conclusion.
The full main-library integrity check also passed with this theorem imported
and included in its selected axiom audit.

```sh
lake build Collatz.Papers.KorecFourFifths
lake env lean scripts/audit_korec_four_fifths.lean
python3 scripts/probe_korec_four_fifths.py
```

[Final theorem](../Collatz/Papers/KorecFourFifths.lean),
[orbit estimate](../Collatz/Strategy/PowerOrbitScale.lean),
[scale selection](../Collatz/Structure/PowerScaleSelection.lean),
[count transfer](../Collatz/Structure/PowerTailCounting.lean),
[audit](KorecFourFifthsAxioms.txt), [probe](KorecFourFifthsProbe.json).
