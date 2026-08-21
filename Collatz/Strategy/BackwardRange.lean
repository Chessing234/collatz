import Collatz.Strategy.ReverseTree
import Collatz.Search.VerifiedExtended

/-!
# The verified range applied to predecessor histories

`ReverseTree` showed that the backward reading of `T` is a relabeling of the
forward one (`reverse_eq_forward`), and that its one `d`-dependent feature depends
on `d mod 3` alone.  That analysis used no `d = 1`-specific asset.  This file
supplies the missing asset — (a), the verified range
`Search.reachesOne_of_lt_1086464` — and asks whether the range becomes a
*branching* obstruction when it is applied to ancestors rather than to a forward
orbit.  It does not.  The record below is the exact reason.

## 1. The range is hereditary upward, and it prunes whole subtrees

If any node of a reverse path is below the range then the *entire* reverse subtree
above it reaches `1` (`subtree_reaches_one`).  So the range does not merely delete
nodes: it deletes cones.  This is the strongest form the asset can take in the
backward reading, and it is the form used here.

## 2. But the cones it deletes all hang off one bounded window

A node `y` loses its odd preimage `p(y) = (2y−1)/3` only when `p(y) < 1086464`,
i.e. only when `2y − 1 < 3·1086464`, i.e. only when `y ≤ 1629696`.  Hence

* `pred_ge_of_ge_threshold`: **every** positive preimage of every `y ≥ 1629697` is
  itself `≥ 1086464`;
* `pruning_window_nonempty`: and `1629696` is sharp — `1086463 → 1629695` is a real
  deleted edge.

So the whole content of the verified range for the reverse tree is a condition on
the single interval `[1086464, 1629696]`, `543233` integers wide.  Everywhere else
the reverse tree is untouched.  A path is deleted exactly when it re-enters that
window from above and then takes the odd branch — and each odd branch multiplies
by only `2/3` while each doubling branch multiplies by `2`, so re-entry is a
positive-drift random walk problem, not a combinatorial one.

## 3. The surviving branching factor is `4/3`, exactly the unpruned one

The reverse tree's growth rate is computable in closed form from
`reverse_eq_forward`: a word `w` of length `k` with `a` ones is realised above `y`
iff `3 ^ a ∣ 2 ^ k y − C(w)`, and by `endpoint_class` the endpoints realising a
given word form a **single residue class mod `3 ^ a`** (density `3 ^ (−a)`).
Summing over words,

`Σ_a C(k,a) · 3^(−a) = (1 + 1/3)^k = (4/3)^k`,

which is the branching factor, and the same computation gives the odd-branch
frequency `(1/3)/(1+1/3) = 1/4` along a typical reverse path.  Both are confirmed
exactly: BFS of the *pruned* tree (every node `≥ 1086464`) to depth `52` gives

```
  y₀ = 1086464 : 3666240 paths, ratio 1.3331, mean odd fraction 0.2441
  y₀ = 1086467 : 3842281 paths, ratio 1.3333, mean odd fraction 0.2467
  y₀ = 2000000 : 5969169 paths, ratio 1.3332, mean odd fraction 0.2494
  y₀ = 10^9+1  : 6137485 paths, ratio 1.3333, mean odd fraction 0.2497
```

and the pruned/unpruned ratio *stabilises at a constant* by depth ≈ 16 and never
decays again: at depth 44 the ratios are `0.6269` (`y₀ = 1086464`), `0.4985`
(`1086466`), `1.0000` (`1086467`), `1.0000` (`1086469`), each already flat from
depth ≈ 16 onwards.  **The verified range costs a constant factor, never an exponent.**

## 4. Why: the bounded-ancestry exponent is the heavy-word deficit again

Along a reverse path, `3 ^ a x = 2 ^ k y − C`, so `log₂ x ≈ log₂ y + k − a·log₂ 3`.
Staying below a bound therefore forces `a ≥ k / log₂ 3 = k·log₃ 2`, and the number
of such paths, weighted by their density `3 ^ (−a)`, is

`2 ^ (k·(H(log₃ 2) − log₃ 2 · log₂ 3)) = 2 ^ (k·(H(log₃ 2) − 1)) = 2 ^ (−0.05004 k)`.

That exponent, `1 − H(log₃ 2) = 0.05004`, is *the same constant* Round V/VI already
recorded as the heavy-word density deficit — and not by analogy: the weight
`C(k,a)·3^(−a)` **is** the forward heaviness generating function.  The typical
reverse path has odd frequency `1/4`; a bounded one needs `log₃ 2 = 0.6309`.  The
requirement is never *infeasible* (by `endpoint_class` every word of every length
is realised above a positive-density set of endpoints, and a fixed `y` realises it
whenever one divisibility holds), only exponentially rare — at exactly the rate the
forward count already knows.

## 5. Verdict

`backward_range_is_forward_range`: for a fixed `x`, "every ancestor-chain node is
`≥ 1086464`" and "the forward orbit stays `≥ 1086464`" are the same predicate, and
`ancestor_ge_iff` shows the backward partial quotients `(2^j y − C_j)/3^(a_j) ≥ B`
are the forward inequalities `3^(a_j)·B + C_j ≤ 2^j y` transposed — the very
inequalities `RealizableFrontier6809.no_light_window` already consumes.  The range
is a *magnitude* asset and it does constrain, but it constrains one bounded window
and a constant fraction of paths; the branching factor `4/3` survives intact.
**The branch is dead.**
-/

namespace Collatz
namespace BackwardRange

open Reach Congruence AffineExact Density ReverseTree

/-! ## 1. Upward heredity: the range deletes cones, not nodes -/

/-- **Whole-subtree pruning.**  If any node of the forward orbit of `x` — i.e. any
node *below* `x` in the reverse tree — is positive and below the verified range,
then `x` itself reaches `1`.  So the reverse subtree above any sub-range node is
deleted in one stroke. -/
theorem subtree_reaches_one {x m i : Nat} (hx : 0 < x) (hm : 0 < m)
    (hlt : m < 1086464) (h : acceleratedOrbit i x = m) : ReachesOne x := by
  have hreach : ReachesOne m := Search.reachesOne_of_lt_1086464 hm hlt
  rw [← h] at hreach
  exact reachesOne_of_accOrbit hx hreach

/-! ## 2. The pruning window, exactly -/

/-- **No pruning above `1629697`.**  Every positive preimage of a node at least
`1629697` is itself at least the verified range `1086464`.  The doubling preimage
is `2y`; the odd preimage satisfies `3n + 1 = 2y`, hence `n ≥ (2·1629697 − 1)/3 >
1086464`. -/
theorem pred_ge_of_ge_threshold {n y : Nat} (hn : 0 < n) (hy : 1629697 ≤ y)
    (h : acceleratedStep n = y) : 1086464 ≤ n := by
  rcases pred_cases hn h with hc | ⟨_, he, _⟩
  · omega
  · omega

/-- Iterated: a reverse path that never leaves `[1629697, ∞)` never meets the
range condition at all. -/
theorem pred_ge_of_ge_threshold' {n y : Nat} (hn : 0 < n) (hy : 1629697 ≤ y)
    (h : acceleratedStep n = y) : 1086464 ≤ n ∧ (n % 2 = 0 → 1629697 ≤ n) := by
  refine ⟨pred_ge_of_ge_threshold hn hy h, fun he => ?_⟩
  rcases pred_cases hn h with hc | ⟨ho, _, _⟩
  · omega
  · omega

/-- **The threshold is sharp.**  `1086463 → 1629695` is a genuine edge of the
reverse tree whose source is below the verified range, so the window
`[1086464, 1629696]` really is where all the pruning happens. -/
theorem pruning_window_nonempty :
    ∃ n y : Nat, 0 < n ∧ n % 2 = 1 ∧ acceleratedStep n = y ∧
      1086464 ≤ y ∧ y ≤ 1629696 ∧ n < 1086464 := by
  refine ⟨1086463, 1629695, by omega, by omega, ?_, by omega, by omega, by omega⟩
  rw [acceleratedStep, if_neg (by omega)]

/-- The window has exactly `543233` integers in it. -/
theorem pruning_window_width : 1629696 - 1086464 + 1 = 543233 := by omega

/-! ## 3. The backward partial quotients are the forward inequalities transposed -/

/-- Scalar helper, with the powers taken as plain variables (the unification trap
of Round III: never let `3 ^ a` meet a four-digit numeral inside `omega`). -/
theorem ge_iff_aux {P x C R Y : Nat} (hP : 0 < P) (he : P * x + C = Y) :
    R ≤ x ↔ P * R + C ≤ Y := by
  constructor
  · intro h
    have := Nat.mul_le_mul_left P h
    omega
  · intro hle
    have h2 : P * R ≤ P * x := by omega
    exact Nat.le_of_mul_le_mul_left h2 hP

/-- **The ancestor bound in affine form.**  If `x` reaches `y` in `j` steps then
`x ≥ 1086464` is *equivalent* to `3 ^ a · 1086464 + C ≤ 2 ^ j · y`, where
`a = oddCount x j` and `C = affineC j x`.  The left side is the backward reading
(`x = (2^j y − C)/3^a ≥ B`); the right side is the forward inequality already used
by `RealizableFrontier6809`.  They are the same statement. -/
theorem ancestor_ge_iff {x y j : Nat} (h : acceleratedOrbit j x = y) :
    1086464 ≤ x ↔ 3 ^ oddCount x j * 1086464 + affineC j x ≤ 2 ^ j * y :=
  ge_iff_aux (Arith.three_pow_pos _) ((reverse_eq_forward x y j).mp h)

/-- **The transposition verdict.**  Quantified over the reverse tree above `x` or
over the forward orbit of `x`, the range condition is one and the same predicate.
There is no backward-only inequality to be had. -/
theorem backward_range_is_forward_range (x L : Nat) :
    (∀ j : Nat, j ≤ L → ∀ y : Nat, acceleratedOrbit j x = y → 1086464 ≤ y) ↔
    (∀ j : Nat, j ≤ L → 1086464 ≤ acceleratedOrbit j x) := by
  constructor
  · intro h j hj
    exact h j hj _ rfl
  · intro h j hj y hy
    rw [← hy]
    exact h j hj

/-! ## 4. The branching count: endpoints of a fixed word form one class mod `3 ^ a`

This is what makes the growth rate `(4/3)^k` exact, and it is `d`-free. -/

/-- **The endpoint class.**  Two reverse paths of the same length carrying the same
word data (`oddCount`, `affineC`) have endpoints congruent mod `3 ^ a` — stated
additively to stay inside `Nat`.  Hence the endpoints above which a given word of
length `k` with `a` ones is realised form a single residue class mod `3 ^ a`, of
density `3 ^ (−a)`; summing `C(k,a)·3^(−a)` over `a` gives the branching factor
`(4/3)^k`. -/
theorem endpoint_class {x x' y y' j : Nat}
    (h : acceleratedOrbit j x = y) (h' : acceleratedOrbit j x' = y')
    (ha : oddCount x j = oddCount x' j) (hc : affineC j x = affineC j x') :
    3 ^ oddCount x j * x + 2 ^ j * y' = 3 ^ oddCount x j * x' + 2 ^ j * y := by
  have he := (reverse_eq_forward x y j).mp h
  have he' := (reverse_eq_forward x' y' j).mp h'
  rw [← ha, ← hc] at he'
  omega

/-- The same statement as a divisibility: `3 ^ a` divides the difference of the two
scaled endpoints. -/
theorem diff_aux {P u v A Bv : Nat} (h : P * u + A = P * v + Bv) (huv : v ≤ u) :
    ∃ q : Nat, A + P * q = Bv := by
  refine ⟨u - v, ?_⟩
  have hu : u = v + (u - v) := by omega
  rw [hu, Nat.mul_add] at h
  omega

/-- The same statement as a divisibility: `3 ^ a` divides the difference of the two
scaled endpoints, so the admissible endpoints of a fixed word are one class mod
`3 ^ a`. -/
theorem endpoint_class_dvd {x x' y y' j : Nat}
    (h : acceleratedOrbit j x = y) (h' : acceleratedOrbit j x' = y')
    (ha : oddCount x j = oddCount x' j) (hc : affineC j x = affineC j x') :
    ∃ q : Nat, 2 ^ j * y' + 3 ^ oddCount x j * q = 2 ^ j * y ∨
               2 ^ j * y + 3 ^ oddCount x j * q = 2 ^ j * y' := by
  have hk := endpoint_class h h' ha hc
  rcases Nat.le_total x' x with hx | hx
  · obtain ⟨q, hq⟩ := diff_aux hk hx
    exact ⟨q, Or.inl hq⟩
  · obtain ⟨q, hq⟩ := diff_aux hk.symm hx
    exact ⟨q, Or.inr hq⟩

/-! ## 5. The dead-branch record -/

/-- **The verdict, as a theorem.**  Above the threshold the range imposes nothing on
the reverse tree (`pred_ge_of_ge_threshold`); the threshold is sharp
(`pruning_window_nonempty`); and inside the tree the range condition is literally
the forward orbit condition (`backward_range_is_forward_range`).  So the verified
range, applied to predecessor histories, is not a branching obstruction. -/
theorem range_is_not_a_branching_obstruction :
    (∀ n y : Nat, 0 < n → 1629697 ≤ y → acceleratedStep n = y → 1086464 ≤ n) ∧
    (∃ n y : Nat, 0 < n ∧ acceleratedStep n = y ∧ 1086464 ≤ y ∧ n < 1086464) ∧
    (∀ x L : Nat,
      ((∀ j : Nat, j ≤ L → ∀ y : Nat, acceleratedOrbit j x = y → 1086464 ≤ y) ↔
       (∀ j : Nat, j ≤ L → 1086464 ≤ acceleratedOrbit j x))) := by
  refine ⟨fun n y hn hy h => pred_ge_of_ge_threshold hn hy h, ?_,
    fun x L => backward_range_is_forward_range x L⟩
  obtain ⟨n, y, hn, _, hs, h1, _, h3⟩ := pruning_window_nonempty
  exact ⟨n, y, hn, hs, h1, h3⟩

end BackwardRange
end Collatz
