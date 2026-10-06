# Bounded descent cannot use a height comparable to size

For the accelerated Collatz map T, let h be a natural-valued height. Suppose
there are fixed natural constants A and C such that, outside a finite range,

    n + 1 ≤ A h(n),       h(n) ≤ C (n + 1).

The new checked theorem says there is no fixed finite B for which every
sufficiently large n has some 1≤k≤B with h(T^k(n))≤h(n). Strict descent is
therefore excluded as well. The height may oscillate arbitrarily: no
monotonicity, residue periodicity, or computability is assumed.

This extends the scope of the earlier residue-monotone obstruction in one
direction. Heights comparable to size need not be residue-monotone, while
residue-monotone heights need not be comparable to size. Neither theorem
excludes all possible descent heights.

## Argument

First normalize to n+1≤h(n)≤C(n+1). For any prescribed run length K and q>0,
the start n=q·2^K−1 has the exact formula

    T^i(n) + 1 = q·3^i·2^(K−i)       (0≤i≤K).

An elementary integer version of Bernoulli's inequality gives
(i+2)2^i≤2·3^i, hence C·2^i<3^i whenever i≥2C+1.

Assume a bounded nonincrease schedule exists. Choose a run longer than
B(2C+1), starting above the exceptional range. Concatenate 2C+1 schedule
choices. Their total time t lies between 2C+1 and B(2C+1). The chosen height
never increases, but the orbit formula gives

    C(n+1) < T^t(n)+1 ≤ h(T^t(n)) ≤ h(n) ≤ C(n+1),

which is impossible. Every intermediate state remains above the exceptional
range because the all-odd run increases. Multiplying h by A handles the two
independent comparison factors in the displayed theorem.

## Scope and checks

This is an obstruction for a specified class of universal-descent proposals,
not a proof of convergence or divergence. It permits schedules whose required
horizons grow with the input, and heights outside these comparison bounds.
No historical novelty is asserted for the argument.

The core-only Lean module builds. Seven theorem endpoints pass an axiom audit
using only standard logical axioms. Independent integer tests check 2,268
odd-run formula cases and 216 adaptive schedules, including residue and
binary-digit oscillations. Tests find an input with no allowed nonincrease
choice in each case; the theorem, rather than these finite tests, establishes
the universal quantifiers over heights, cutoffs, and horizons.

```sh
lake build Collatz.Strategy.ComparableHeightObstruction
lake env lean scripts/audit_comparable_height.lean
python3 scripts/probe_comparable_height.py
```

[Lean source](../Collatz/Strategy/ComparableHeightObstruction.lean),
[axiom audit](ComparableHeightAxioms.txt), [test results](ComparableHeightProbe.json).

The [logarithmic-height extension](LogarithmicHeightObstruction.md) applies
this result after exponentiation, excluding bounded additive corrections to
floor(log₂(n+1)) as a source of uniformly bounded descent.

The [finite witness refinement](BoundedHeightWitness.md) bounds the size of a
failing input and supplies a Boolean search with checked semantics.
