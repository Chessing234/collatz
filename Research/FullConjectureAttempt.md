# Full Collatz proof attempt: unresolved

The requested unconditional proof has not been obtained. The periodic two-defect classification is a checked finite structural theorem. It does not establish convergence of every positive orbit. Its historical novelty also remains unconfirmed beyond the bounded literature comparison in `PeriodicTwoDefectAllClassification.md`.

## Exact missing assertion

For the accelerated map

\[
T(n)=\begin{cases}n/2&n\text{ even},\\(3n+1)/2&n\text{ odd},\end{cases}
\]

one sufficient, and equivalent, missing assertion is

\[
\forall n>1\;\exists k\in\mathbb N:\quad T^k(n)<n.
\]

The core project defines this assertion as `Collatz.Strategy.FiniteStoppingTime` in `Collatz/Strategy/Pillars.lean`. Its implication to the canonical `CollatzConjecture` is already proved there by descent on a hypothetical least counterexample. The converse is also proved. `Collatz/Strategy/Reductions.lean` packages the equivalence as `collatz_iff_finiteStoppingTime`. No proof of the unconditional stopping-time assertion was produced in this attempt.

## Why the modular theorem does not close the gap

Let `B(n)` mean that the orbit of `n` reaches 1. Orbit invariance of `B` is already established. The new classification applies to periodic labels; orbit invariance does not supply periodicity.

In fact, `Collatz/Strategy/PeriodicRigidity.lean` already proves

```
CollatzConjecture ↔ EventuallyPeriodic Reach.ReachesOne
```

where `EventuallyPeriodic f` means that there exist `m > 0` and `N` such that `f(n+m) = f(n)` for every `n ≥ N`. Assuming this hypothesis for the actual convergence basin would assume an equivalent form of the desired conclusion. The classification has not supplied a way to prove that hypothesis. Counts of boundary edges in finite modular graphs do not imply that each integer orbit traverses one of those edges.

## The existing analytic route has a separate missing estimate

The source of `ProofAtlasAttack/CollatzTargetDensity/ProofChain.lean` was examined, together with `EnergyTargets.lean`. This is a separate development using Mathlib; it was not rebuilt or independently re-audited in this follow-up.

That chain derives a positive lower density bound for integers whose trajectories never go below a hypothetical least counterexample `m`. The contradiction requires an upper bound, at arbitrarily large cutoffs, strictly smaller than the supplied lower bound. The file explicitly names this unproved premise `EnergyTailGap K d`. It also proves that, for suitable constants from its lower bound, this gap is equivalent to the full conjecture. The lower bound by itself is not a contradiction, and no proof of the missing upper bound was found here.

## Verification boundary

After the full-conjecture request, both commands completed successfully:

```
lake build Collatz.Strategy.PeriodicTwoDefectAll
lake env lean scripts/audit_periodic_two_defect_all.lean
```

All 20 audited endpoints use only subsets of `propext`, `Classical.choice`, and `Quot.sound`. No unconditional theorem asserting the conjecture was added. The earlier full-repository integrity run was interrupted and is not reported as passed.

These findings identify gaps in the arguments inspected here. They do not establish that another approach cannot succeed. The user's full-proof objective remains unachieved.

## Direct attempt at universal descent using successive rise-and-halving blocks

On the subsequent request to prove universal descent itself, a concrete attempted shortcut was tested: perhaps a fixed number of complete rising runs followed by their halving runs must bring every starting value below itself. This shortcut fails, including when all intermediate values are considered.

For the accelerated map, whenever `u > 0` the exact block is

```
8u - 5  ->  12u - 7  ->  18u - 10  ->  9u - 5.
```

Its input parities are odd, odd, even. For any natural `r`, set `N = 8^(r+1)-5`. The first `r` blocks have the exact boundary values

```
T^(3j)(N) = 9^j * 8^(r+1-j) - 5,      0 <= j <= r.
```

Every such boundary is odd, so every block completes its halving run. Every intermediate iterate through step `3r` is at least `N`; for `r > 0`, the final value `8*9^r-5` is strictly greater than `N`. Thus even arbitrarily many complete rising-and-halving blocks can precede a first descent. The witness depends on `r`: this does not construct an infinite never-descending orbit.

For example, `59 -> 89 -> 134 -> 67` grows across one complete block, but `T^7(59)=38<59`. That example explicitly separates failure of the shortcut from failure of eventual descent.

The standalone file `Research/UniversalDescentBlockAttempt.lean` proves the block formula, the bound on every intermediate iterate, the odd boundaries, and strict endpoint growth. It also checks the concrete 59 example. Its six printed axiom footprints use only `propext` and `Quot.sound`; the file compiles with `lake env lean Research/UniversalDescentBlockAttempt.lean`. No package-wide rebuild was performed for this standalone file. These elementary affine-prefix consequences are not claimed novel. No unconditional universal-descent proof resulted from this attempt.
