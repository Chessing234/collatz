import Collatz.Strategy.RealizableFrontier6809

/-!
# Round XII, Section X — the bottom region is unreachable, and Branch A is empty

Round XII proposes a bottom-scale architecture: a hypothetical cycle is forced into a
finite region `x < B` (initially `B = 1000`), where a finite mechanism extracts a
positive cost.  Section X asks the load-bearing question directly:

> *Does a hypothetical `3x+1` cycle necessarily have `min x < B`?*

**No — and provably not, for every `B ≤ 1086464`.**  The repository already owns the
theorem: `RealizableFrontier6809.ge_verified_1086464` says every point on the orbit of a
counterexample is at least the verified range.  Its hypothesis is `¬ ReachesOne n`, so
it covers **both** kinds of counterexample — a nontrivial cycle and a divergent orbit
alike.  (For divergence this also follows from `Escape.divergent_avoids_verified`.)

Hence:

> **No hypothetical counterexample of either kind ever takes a value below `1086464`.**

The bottom region is not merely unlikely to be visited; it is provably never visited.
So Round XII's **Branch A is empty**, and with it sections XII–XV, XXV–XXXI and
XXXV–XLVII in their bottom-scale reading: an excursion cost, a finite-support potential,
a bottom return graph, a bottom catalogue and a bottom budget are all mechanisms that a
counterexample never touches.  They can be built, and they will be vacuous.

## What this does *not* kill

* `octave_sojourn` is a theorem about *all* orbits and is unaffected.
* The **high-scale branch** (sections XIX, XX, XXXVIII, XLVIII, and Branch B of the
  two-case master theorem XLIX) is untouched — and is now the *only* branch.
* The `0.2299545` accumulation constant remains a real question, but its subject is
  now known: it is a statistic of trajectories that **reach 1**.  Over `99.2%` of it
  comes from odd values below `1000`, and a counterexample is never there.  So the
  constant is a fact about the trivial behaviour, provably invisible to any
  counterexample.

## Status of this file, and the one bottom that is *not* empty

**This file contains no new mathematics, and says so.**  `bottom_unreachable` is
`ge_verified_1086464` composed with `Nat.le_trans`; `no_visit_below_1000` is that at
`B = 1000`; and `reaches_of_bottom_visit` **duplicates
`BackwardRange.subtree_reaches_one`** modulo argument order.  It is a redirection note,
not a result.

Two strengthenings the audit supplied, both compiled elsewhere and recorded here:
the **plain-map** form holds too (the only orbit values the accelerated map skips are
the intermediates `3x+1 > x`, so nothing can hide below), and every **ancestor** of a
counterexample is itself a counterexample, so the reverse tree is `≥ 1086464` as well.

**But there is a bottom that is not empty, and reading this file as "the bottom is
unreachable" would wrongly discard it.**  `SegmentMonoid.cycle_frontier` rearranges to
an *upper* bound on the cycle minimum, `n ≤ a·2^L / (3(2^L − 3^a))`, so the minimum is
confined to a **finite band**:

| ledge `(L,a)` | band for the minimum | integers | odd candidates |
|---|---|---|---|
| `(4701, 2966)` | `[1086464, 1166893]` | 80430 | 40215 |
| `(6809, 4296)` | `[1086464, 1884147]` | 797684 | 398842 |

So "a hypothetical cycle is forced into a finite region where a finite mechanism could
extract a cost" is **true** — the region is at `10^6`, not `10^3`.  What keeps the
redirection intact is that the band is *per ledge*, its union over surviving ledges is
unbounded, and a ledge survives the budget exactly when the verified range fails to
clear its band.  So "clear the band" is definitionally "extend the verified range".

## And a prediction the round should test

For a counterexample every orbit value is `≥ 1086464`, so every local coupling term
`d/(3x)` is at most `1/(3·1086464) ≈ 3.07·10^(−7)`, and the total over `L` steps is at
most `a/(3·1086464)`.  That is exactly the inequality `3nG ≤ a·2^L` —
`SegmentMonoid.cycle_frontier`.  Round XI showed that inequality *is*
`RealizableFrontier6809` in multiplicative coordinates.

> So the budget architecture of sections XII, XIII, XXXV, XLV and XLVII is predicted to
> reduce, once again, to the frontier filter.

**Checked, and the last link was wrong.**  The first three links hold: each term is
`≤ 1/(3·1086464) = 3.068·10^(−7)`, the total is `≤ a/(3·1086464)`, and that is
`floor_coupling` at a constant floor — *implied by* `cycle_frontier`, never conversely,
since `cycle_frontier` uses the cycle's own minimum.

But it is **not** `RealizableFrontier6809`.  The budget's admissible ledge pairs are
`(4701,2966), (5755,3631), (6809,4296), (7863,4961), …` — the same family, but the
certificate **excludes `4701` and `5755`**.  The budget is the frontier ledge family
**cut two risers lower**, so it cannot even recover `L ≥ 6809`.  The reason is exact:
the budget reads only `(L,a)`, i.e. word *content*, while the certificate's `Bcap` reads
word *ordering*.  Content is strictly less information, so no arrangement of the budget
reaches the certificate.
-/

namespace Collatz
namespace BottomUnreachable

open RealizableFrontier6809 Reach

/-- **A counterexample never enters the bottom region.**  For any threshold `B` at or
below the verified range, no orbit point of a non-`ReachesOne` start lies below `B`.

The hypothesis is `¬ ReachesOne n`, so this covers a nontrivial cycle and a divergent
orbit alike: Round XII's Branch A is empty for both. -/
theorem bottom_unreachable {B n m : Nat} (hB : B ≤ 1086464) (hn : 0 < n)
    (hnr : ¬ ReachesOne n) (hm : ∃ i : Nat, acceleratedOrbit i n = m) : B ≤ m :=
  Nat.le_trans hB (ge_verified_1086464 hn hnr hm)

/-- The round's own threshold, `B = 1000`: a counterexample never takes a value there. -/
theorem no_visit_below_1000 {n m : Nat} (hn : 0 < n) (hnr : ¬ ReachesOne n)
    (hm : ∃ i : Nat, acceleratedOrbit i n = m) : 1000 ≤ m :=
  bottom_unreachable (by omega) hn hnr hm

/-- Contrapositive, in the form the bottom-excursion machinery would consume: an orbit
point below the verified range forces the start to reach `1`, so no bottom excursion of
a counterexample exists to be catalogued. -/
theorem reaches_of_bottom_visit {n m : Nat} (hn : 0 < n)
    (hm : ∃ i : Nat, acceleratedOrbit i n = m) (hlow : m < 1086464) : ReachesOne n := by
  by_cases h : ReachesOne n
  · exact h
  · exact absurd (ge_verified_1086464 hn h hm) (by omega)

/-! ## Axiom audit -/

#print axioms bottom_unreachable
#print axioms no_visit_below_1000
#print axioms reaches_of_bottom_visit

end BottomUnreachable
end Collatz
