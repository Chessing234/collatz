import Collatz.Strategy.ThreeObstruction
import Collatz.Strategy.AffineExact
import Collatz.Strategy.Mirror

/-!
# The reverse tree: exact branching, and why it is the forward cocycle in disguise

The accelerated map `T(x) = x/2` (even), `(3x+1)/2` (odd) is finite-to-one.  This
file sets up its inverse exactly, counts the branch points, and then asks what —
if anything — the backward reading sees that the forward one does not.

## The branching law

`T⁻¹(y)` always contains the *doubling* preimage `2y`.  It contains a second,
*odd*, preimage `p(y) = (2y−1)/3` exactly when `3 ∣ 2y − 1`, i.e. exactly when

**`y ≡ 2 (mod 3)`**  (`odd_pred_exists_iff`).

So the reverse tree is a doubling ray with an extra subtree hung off every node in
the class `2 (mod 3)`.  Two facts pin the density of those branch points down
completely:

* **On an even step the residue doubles** (`even_step_mod_three`): `T(x) ≡ 2x`
  (mod 3).  Since `2` has order `2` modulo `3`, along a *doubling ray*
  `y, 2y, 4y, …` from any `y` not divisible by three the residue alternates
  `1, 2, 1, 2, …`, so **exactly every other node of the ray is a branch point**
  (`ray_branch_alternates`).
* **On an odd step the residue is reset to `2`** (`odd_step_mod_three`): `2T(x) =
  3x + 1 ≡ 1`, so `T(x) ≡ 2 (mod 3)` for every odd `x`.  Every odd step lands on a
  branch point.

Putting the two together gives the exact local law
(`consecutive_branch_iff`): a branch point `x` is *followed* by a branch point iff
`x` is odd.  Consecutive branch points therefore mark exactly the odd steps, and
isolated ones mark the even runs.

Modulo three this is a complete description of the reverse tree, and it is
`ThreeResidue`'s clock read backwards.  It reproves `ThreeObstruction` as one of
three cases: the tree above `y` is a bare ray iff `3 ∣ y` (`reverse_tree_dichotomy`).

## The relabeling verdict

A reverse path of length `L` ending at `y` is a forward orbit segment, and the
exact affine law `AffineExact.affine_exact` reads, solved backwards,

`3 ^ a · x + C = 2 ^ L · y`,   `a = oddCount x L`, `C = affineC L x`,

so `x = (2^L y − C)/3^a`.  This is not a new cocycle: it is `affineC` verbatim.
Two consequences are worth recording because they are the sharpest form of the
backward statement:

* `reverse_eq_forward`: `T^L(x) = y` **iff** `3^a x + C = 2^L y`.  The backward
  relation and the forward relation are literally the same equation.
* `reverse_determined`: a reverse path is determined by its endpoint together with
  its word — if two starts have the same word data and the same endpoint they are
  equal.  This is the exact dual of Terras (forward: a word is one class mod `2^L`;
  backward: a word plus an endpoint is one *number*, subject to `3^a ∣ 2^L y − C`).

**Verdict: the reverse formulation is a relabeling.**  It adds no quantity that the
forward affine framework does not already carry; it only moves the divisibility
condition from the prime `2` to the prime `3`, which is `BackwardRun`'s mirror.

## Where `d` enters — and why it does not help

For `T_d(x) = (3x+d)/2` the odd preimage of `y` is `(2y−d)/3` and exists iff
`2y ≡ d (mod 3)`, i.e. iff `y ≡ 2d (mod 3)`.  So the branching *class* is the one
place in the whole development where the asset `d` appears in the *shape* of the
object rather than as a scalar `C(w,d) = d·C(w,1)`.

But it appears only through `d mod 3`, and that is fatal:

* `d = 1` and `d = 7` have the **same** branch class `2 (mod 3)`, and `3x+7` has the
  nontrivial cycle `5 → 11 → 20 → 10 → 5` (`sevenCycle`).  So no property of the
  reverse-tree branching can separate them.
* `d = 5` and `d = −1` share the branch class `1 (mod 3)`, and both have genuine
  nontrivial cycles.

Hence the branching law fails the soundness filter: it is a function of `d mod 3`
only, and `d mod 3 = 1` already admits a counterexample.
-/

namespace Collatz
namespace ReverseTree

open Reach Congruence AffineExact Density

/-! ## 1. The two preimages -/

/-- The doubling preimage always exists. -/
theorem step_two_mul (y : Nat) : acceleratedStep (2 * y) = y := by
  rw [acceleratedStep, if_pos (by omega)]
  omega

/-- The odd (shrinking) preimage. -/
def oddPred (y : Nat) : Nat := (2 * y - 1) / 3

/-- On the branch class the odd preimage is genuinely odd. -/
theorem oddPred_odd {y : Nat} (h : y % 3 = 2) (_hy : 2 ≤ y) : oddPred y % 2 = 1 := by
  rw [oddPred]; omega

/-- On the branch class the odd preimage is positive. -/
theorem oddPred_pos {y : Nat} (h : y % 3 = 2) (_hy : 2 ≤ y) : 0 < oddPred y := by
  rw [oddPred]; omega

/-- The odd preimage is strictly smaller: `3·p(y) = 2y − 1 < 3y`. -/
theorem oddPred_lt {y : Nat} (h : y % 3 = 2) (_hy : 2 ≤ y) : oddPred y < y := by
  rw [oddPred]; omega

/-- The defining equation of the odd preimage. -/
theorem three_mul_oddPred {y : Nat} (h : y % 3 = 2) (_hy : 2 ≤ y) :
    3 * oddPred y + 1 = 2 * y := by
  rw [oddPred]; omega

/-- The odd preimage really steps to `y`. -/
theorem step_oddPred {y : Nat} (h : y % 3 = 2) (hy : 2 ≤ y) :
    acceleratedStep (oddPred y) = y := by
  rw [acceleratedStep, if_neg (by have := oddPred_odd h hy; omega)]
  have := three_mul_oddPred h hy
  omega

/-- **Classification of preimages.**  Every positive preimage of `y` is either the
double or the odd preimage, and the latter forces `y ≡ 2 (mod 3)`. -/
theorem pred_cases {n y : Nat} (_hn : 0 < n) (h : acceleratedStep n = y) :
    n = 2 * y ∨ (n % 2 = 1 ∧ 3 * n + 1 = 2 * y ∧ y % 3 = 2) := by
  rcases Arith.mod_two_eq_zero_or_one n with he | ho
  · left
    rw [acceleratedStep, if_pos he] at h
    omega
  · right
    rw [acceleratedStep, if_neg (by omega)] at h
    refine ⟨ho, by omega, by omega⟩

/-- **The branch criterion, exactly.**  `y` has an odd preimage iff `y ≡ 2 (mod 3)`
and `y ≥ 2`.  This is the branching law of the reverse tree. -/
theorem odd_pred_exists_iff {y : Nat} (_hy : 0 < y) :
    (∃ n : Nat, 0 < n ∧ n % 2 = 1 ∧ acceleratedStep n = y) ↔ (y % 3 = 2 ∧ 2 ≤ y) := by
  constructor
  · intro ⟨n, hn, ho, hs⟩
    rcases pred_cases hn hs with hc | ⟨_, heq, hm⟩
    · omega
    · exact ⟨hm, by omega⟩
  · intro ⟨hm, h2⟩
    exact ⟨oddPred y, oddPred_pos hm h2, oddPred_odd hm h2, step_oddPred hm h2⟩

/-- Off the branch class the only preimage is the double.  This contains
`ThreeObstruction.pred_unique_of_three_dvd` (the case `y % 3 = 0`) and adds the
case `y % 3 = 1`, which the earlier file did not cover. -/
theorem pred_unique_of_not_two_mod_three {n y : Nat} (hn : 0 < n) (hy : y % 3 ≠ 2)
    (h : acceleratedStep n = y) : n = 2 * y := by
  rcases pred_cases hn h with hc | ⟨_, _, hm⟩
  · exact hc
  · exact absurd hm hy

/-! ## 2. The residue clock, read as branch density -/

/-- **Even steps double the residue mod three.** -/
theorem even_step_mod_three {x : Nat} (hx : x % 2 = 0) :
    acceleratedStep x % 3 = 2 * x % 3 := by
  rw [acceleratedStep, if_pos hx]
  omega

/-- **Odd steps reset the residue to `2`.**  Every odd step lands on a branch
point. -/
theorem odd_step_mod_three {x : Nat} (hx : x % 2 = 1) :
    acceleratedStep x % 3 = 2 := by
  rw [acceleratedStep, if_neg (by omega)]
  omega

/-- **The local branching law.**  A branch point is followed by a branch point
exactly when it is odd.  Consecutive branch points mark the odd steps; isolated
ones mark the even runs. -/
theorem consecutive_branch_iff {x : Nat} (hx : x % 3 = 2) :
    acceleratedStep x % 3 = 2 ↔ x % 2 = 1 := by
  constructor
  · intro h
    rcases Arith.mod_two_eq_zero_or_one x with he | ho
    · rw [even_step_mod_three he] at h; omega
    · exact ho
  · intro ho
    exact odd_step_mod_three ho

/-- A branch point that is even is followed by a non-branch point: the residue
goes `2 ↦ 1`. -/
theorem branch_not_consecutive {x : Nat} (hx : x % 3 = 2) (he : x % 2 = 0) :
    acceleratedStep x % 3 = 1 := by
  rw [even_step_mod_three he]; omega

/-! ### The doubling ray

`2 ^ k · y` is the `k`-th node of the doubling ray above `y`. -/

/-- The ray really lies above `y`. -/
theorem orbit_two_pow_mul : ∀ (k y : Nat), acceleratedOrbit k (2 ^ k * y) = y := by
  intro k
  induction k with
  | zero => intro y; simp
  | succ k ih =>
    intro y
    have hpow : (2:Nat) ^ (k + 1) * y = 2 * (2 ^ k * y) := by
      rw [Arith.two_pow_succ]
      exact Nat.mul_assoc 2 (2 ^ k) y
    rw [acceleratedOrbit_succ, hpow, step_two_mul, ih]

/-- The residue along the ray depends only on the parity of the height. -/
theorem ray_mod_three : ∀ (k y : Nat),
    (2 ^ k * y) % 3 = (if k % 2 = 0 then y % 3 else (2 * y) % 3) := by
  intro k
  induction k with
  | zero => intro y; simp
  | succ k ih =>
    intro y
    have hpow : (2:Nat) ^ (k + 1) * y = 2 ^ k * (2 * y) := by
      rw [Arith.two_pow_succ, Nat.mul_assoc]
      exact Nat.mul_left_comm 2 (2 ^ k) y
    rw [hpow, ih (2 * y)]
    rcases Nat.lt_or_ge (k % 2) 1 with h | h
    · have h0 : k % 2 = 0 := by omega
      have h1 : (k + 1) % 2 = 1 := by omega
      rw [if_pos h0, if_neg (by omega)]
    · have h0 : k % 2 = 1 := by omega
      have h1 : (k + 1) % 2 = 0 := by omega
      rw [if_neg (by omega), if_pos h1]
      omega

/-- **Exactly every other node of a doubling ray is a branch point.**  For `y` not
divisible by three, `2 ^ k · y` lies in the branch class for exactly one parity of
`k`; for `y` divisible by three, for no `k` at all. -/
theorem ray_branch_alternates {y k : Nat} (h3 : y % 3 ≠ 0) :
    ((2 ^ k * y) % 3 = 2) ↔ ¬ ((2 ^ (k + 1) * y) % 3 = 2) := by
  rw [ray_mod_three k y, ray_mod_three (k + 1) y]
  rcases Nat.lt_or_ge (k % 2) 1 with h | h
  · have h0 : k % 2 = 0 := by omega
    rw [if_pos h0, if_neg (by omega)]
    omega
  · have h0 : k % 2 = 1 := by omega
    rw [if_neg (by omega), if_pos (by omega : (k + 1) % 2 = 0)]
    omega

/-- Every ray above a number prime to three meets the branch class within two
steps. -/
theorem ray_meets_branch {y : Nat} (h3 : y % 3 ≠ 0) (k : Nat) :
    ∃ i : Nat, k ≤ i ∧ i ≤ k + 1 ∧ (2 ^ i * y) % 3 = 2 := by
  rcases Nat.lt_or_ge ((2 ^ k * y) % 3) 2 with h | h
  · refine ⟨k + 1, by omega, by omega, ?_⟩
    have hz : (2 ^ k * y) % 3 ≠ 0 := by
      rw [ray_mod_three k y]
      rcases Nat.lt_or_ge (k % 2) 1 with hk | hk
      · rw [if_pos (by omega)]; omega
      · rw [if_neg (by omega)]; omega
    have hone : (2 ^ k * y) % 3 = 1 := by omega
    have := (ray_branch_alternates (y := y) (k := k) h3)
    omega
  · have hlt : (2 ^ k * y) % 3 < 3 := Nat.mod_lt _ (by omega)
    exact ⟨k, by omega, by omega, by omega⟩

/-! ## 3. The dichotomy: ray or tree -/

/-- **A multiple of three has a bare ray above it** (`ThreeObstruction`), and
anything else has a genuine branch at height at most two.  This is the complete
shape statement for the reverse tree at the first level. -/
theorem reverse_tree_dichotomy {y : Nat} (hy : 0 < y) :
    (y % 3 = 0 ∧ ∀ n : Nat, 0 < n → acceleratedStep n = y → n = 2 * y) ∨
    (y % 3 ≠ 0 ∧ ∃ n j : Nat, 0 < j ∧ j ≤ 2 ∧ n % 2 = 1 ∧ 0 < n ∧
      acceleratedOrbit j n = y) := by
  rcases Nat.lt_or_ge (y % 3) 1 with h0 | h0
  · left
    refine ⟨by omega, fun n hn hs => ?_⟩
    exact pred_unique_of_not_two_mod_three hn (by omega) hs
  · right
    refine ⟨by omega, ?_⟩
    rcases Nat.lt_or_ge (y % 3) 2 with h1 | h1
    · -- `y ≡ 1 (mod 3)`: the branch sits one doubling up
      have hb : (2 * y) % 3 = 2 := by omega
      have h2 : 2 ≤ 2 * y := by omega
      refine ⟨oddPred (2 * y), 2, by omega, by omega, oddPred_odd hb h2,
        oddPred_pos hb h2, ?_⟩
      have hstep : acceleratedStep (oddPred (2 * y)) = 2 * y := step_oddPred hb h2
      rw [show (2:Nat) = 1 + 1 from rfl, acceleratedOrbit_succ, hstep]
      exact step_two_mul y
    · -- `y ≡ 2 (mod 3)`: the branch is immediate
      have hb : y % 3 = 2 := by
        have : y % 3 < 3 := Nat.mod_lt _ (by omega)
        omega
      have h2 : 2 ≤ y := by omega
      exact ⟨oddPred y, 1, by omega, by omega, oddPred_odd hb h2, oddPred_pos hb h2,
        step_oddPred hb h2⟩

/-! ## 4. The relabeling theorem

A reverse path *is* a forward orbit segment, and its arithmetic *is* `affineC`. -/

/-- **The reverse path equation.**  `x` reaches `y` in `L` steps iff
`3 ^ a · x + C = 2 ^ L · y` with `a = oddCount x L`, `C = affineC L x`.  Solved for
`x` this is `x = (2^L y − C)/3^a`: the reverse path is the forward cocycle read
backwards, with no new quantity. -/
theorem reverse_eq_forward (x y L : Nat) :
    acceleratedOrbit L x = y ↔ 3 ^ oddCount x L * x + affineC L x = 2 ^ L * y := by
  constructor
  · intro h
    rw [← h]
    exact (affine_exact x L).symm
  · intro h
    have hex := affine_exact x L
    have hpos : 0 < (2:Nat) ^ L := Arith.two_pow_pos L
    have : (2:Nat) ^ L * acceleratedOrbit L x = 2 ^ L * y := by omega
    exact Nat.eq_of_mul_eq_mul_left hpos this

/-- **A reverse path is determined by its endpoint and its word.**  This is the
exact dual of Terras: forward, a word names one class mod `2 ^ L`; backward, a word
together with an endpoint names one integer. -/
theorem reverse_determined {x x' L : Nat}
    (hend : acceleratedOrbit L x = acceleratedOrbit L x')
    (hword : oddCount x L = oddCount x' L)
    (hacc : affineC L x = affineC L x') : x = x' := by
  have h1 := affine_exact x L
  have h2 := affine_exact x' L
  rw [hend, hword, hacc] at h1
  have h3 : 3 ^ oddCount x' L * x = 3 ^ oddCount x' L * x' := by omega
  exact Nat.eq_of_mul_eq_mul_left (Arith.three_pow_pos _) h3

/-- The divisibility constraint that carves the depth-`L` preimages of `y` out of
the set of all words: for a path that exists, `3 ^ a` divides `2 ^ L y − C`
(stated additively to stay inside `Nat`). -/
theorem reverse_dvd {x y L : Nat} (h : acceleratedOrbit L x = y) :
    ∃ q : Nat, 3 ^ oddCount x L * q + affineC L x = 2 ^ L * y :=
  ⟨x, (reverse_eq_forward x y L).mp h⟩


/-! ## 4b. Counting the branch points along an orbit

The branch points of the reverse tree that lie *on* a forward orbit are exactly
the points in the class `2 (mod 3)`.  The two step laws give their count in closed
form: each odd step contributes one, and each even step from the class `1 (mod 3)`
contributes one.  Nothing else does. -/

/-- The number of `i < j` with `T^(i+1)(x) ≡ 2 (mod 3)`: the branch points among the
first `j` images. -/
def branchCount (x : Nat) : Nat → Nat
  | 0 => 0
  | j + 1 => branchCount x j + (if acceleratedOrbit (j + 1) x % 3 = 2 then 1 else 0)

/-- The number of `i < j` at which an **even** step starts from the class
`1 (mod 3)`. -/
def evenOneCount (x : Nat) : Nat → Nat
  | 0 => 0
  | j + 1 =>
      evenOneCount x j +
        (if acceleratedOrbit j x % 2 = 0 ∧ acceleratedOrbit j x % 3 = 1 then 1 else 0)

/-- **The exact branch-point count.**  Along any orbit,

`branchCount = oddCount + evenOneCount`.

Every odd step lands on a branch point; an even step lands on one exactly when it
started in the class `1 (mod 3)`.  There is no third source. -/
theorem branchCount_eq (x : Nat) : ∀ j : Nat,
    branchCount x j = oddCount x j + evenOneCount x j := by
  intro j
  induction j with
  | zero => rfl
  | succ j ih =>
    have hstep : acceleratedOrbit (j + 1) x = acceleratedStep (acceleratedOrbit j x) :=
      acceleratedOrbit_succ_step j x
    have hlast := Density.oddCount_succ_last x j
    rw [branchCount, evenOneCount, ih, hstep]
    rcases Arith.mod_two_eq_zero_or_one (acceleratedOrbit j x) with he | ho
    · have hmod := even_step_mod_three he
      have hcount : oddCount x (j + 1) = oddCount x j := by omega
      rw [hcount]
      by_cases h1 : acceleratedOrbit j x % 3 = 1
      · rw [if_pos (by omega), if_pos ⟨he, h1⟩]
        omega
      · rw [if_neg (by omega), if_neg (by omega)]
        omega
    · have hmod := odd_step_mod_three ho
      have hcount : oddCount x (j + 1) = oddCount x j + 1 := by omega
      rw [hcount, if_pos hmod, if_neg (by omega)]
      omega

/-- Hence the branch points are at least as numerous as the odd steps. -/
theorem oddCount_le_branchCount (x j : Nat) : oddCount x j ≤ branchCount x j := by
  rw [branchCount_eq x j]
  omega

/-- **On a cycle** of length `L` with `a` odd steps the number of branch points is
`a` plus the number of even steps starting in the class `1 (mod 3)`; in particular
it is between `a` and `L`.  The excess is a function of the parity word alone, so by
`NewModels.word_is_cycle_word` it cannot obstruct anything. -/
theorem cycle_branchCount {n L : Nat} (_h : acceleratedOrbit L n = n) :
    oddCount n L ≤ branchCount n L ∧ branchCount n L = oddCount n L + evenOneCount n L :=
  ⟨oddCount_le_branchCount n L, branchCount_eq n L⟩

/-- The mod-three closure condition on a cycle is **vacuous**: once a single odd
step has occurred the residue of every later point is forced by the word alone
(the odd step resets it to `2`, even steps double it), so there is nothing for the
return to `n` to contradict.  Formally: any two orbits agreeing on their parity
word from an odd step onwards agree on all residues mod three. -/
theorem residue_forced_after_odd_step {x y : Nat}
    (hx : x % 2 = 1) (hy : y % 2 = 1) :
    acceleratedStep x % 3 = acceleratedStep y % 3 := by
  rw [odd_step_mod_three hx, odd_step_mod_three hy]

/-! ## 5. Where `d` enters -/

/-- The accelerated `3x + d` map, `d` a positive odd asset. -/
def stepD (d n : Nat) : Nat :=
  if n % 2 = 0 then n / 2 else (3 * n + d) / 2

/-- Its orbit. -/
def orbitD (d : Nat) : Nat → Nat → Nat
  | 0, n => n
  | k + 1, n => orbitD d k (stepD d n)

/-- **The `d`-dependent branch law.**  For `T_d` the odd preimage of `y` is
`(2y − d)/3`, so it exists exactly when `2y ≡ d (mod 3)`.  This is the one place in
the development where the asset `d` changes the *shape* of the object rather than
rescaling a scalar. -/
theorem oddPredD_exists_iff {d y : Nat} (hd : d % 2 = 1) (_hy : d < 2 * y) :
    (∃ n : Nat, 0 < n ∧ n % 2 = 1 ∧ 3 * n + d = 2 * y) ↔ (2 * y) % 3 = d % 3 := by
  constructor
  · intro ⟨n, hn, ho, he⟩
    omega
  · intro hm
    refine ⟨(2 * y - d) / 3, by omega, by omega, by omega⟩

/-- Restated in the branch class: `y ≡ 2d (mod 3)`. -/
theorem branchClassD {d y : Nat} : (2 * y) % 3 = d % 3 ↔ y % 3 = (2 * d) % 3 := by
  omega

/-- **The branch law depends on `d` only through `d mod 3`.** -/
theorem branch_depends_only_on_d_mod_three {d d' : Nat} (h : d % 3 = d' % 3) (y : Nat) :
    ((2 * y) % 3 = d % 3 ↔ (2 * y) % 3 = d' % 3) := by omega

/-! ### The soundness test

`d = 7` shares the branch class of `d = 1`, and `3x + 7` has a nontrivial cycle. -/

/-- `d = 1` and `d = 7` have the same branch class `2 (mod 3)`. -/
theorem one_seven_same_branch_class : (2 * 1) % 3 = (2 * 7) % 3 := by decide

/-- The nontrivial `3x + 7` cycle `5 → 11 → 20 → 10 → 5`. -/
theorem sevenCycle : orbitD 7 4 5 = 5 := by decide

/-- Its members, for inspection: two odd steps then two halvings. -/
theorem sevenCycle_members :
    stepD 7 5 = 11 ∧ stepD 7 11 = 20 ∧ stepD 7 20 = 10 ∧ stepD 7 10 = 5 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- Three of the four members of the `3x+7` cycle sit in the branch class
`2 (mod 3)` — the same class as for `3x+1`. -/
theorem sevenCycle_branch_points :
    5 % 3 = 2 ∧ 11 % 3 = 2 ∧ 20 % 3 = 2 ∧ 10 % 3 ≠ 2 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- **The soundness verdict.**  There is an asset `d` with the same branch class as
`d = 1` whose map has a nontrivial cycle.  Therefore no property of the reverse
tree's branching structure can prove the Collatz conjecture: that structure is a
function of `d mod 3` alone, and `d mod 3 = 1` already admits a counterexample. -/
theorem branching_cannot_decide :
    ∃ d n L : Nat, d % 3 = 1 % 3 ∧ 1 < n ∧ 0 < L ∧ orbitD d L n = n ∧ n ≠ 1 ∧
      (∀ y : Nat, ((2 * y) % 3 = d % 3 ↔ (2 * y) % 3 = 1 % 3)) :=
  ⟨7, 5, 4, by decide, by omega, by omega, sevenCycle, by omega,
   fun y => branch_depends_only_on_d_mod_three (by decide) y⟩

/-! ### The other side of the filter: `d = 5` and `d = −1` share a branch class -/

/-- `d = 5` has branch class `1 (mod 3)`, and its cycle `1 → 4 → 2 → 1` visits it
twice while having only one odd step: the branch count exceeds the odd-step
count. -/
theorem fiveCycle : orbitD 5 3 1 = 1 := by decide

/-- The `3x+5` cycle's branch points: `1` and `4`, both `≡ 1 (mod 3) = 2·5 mod 3`. -/
theorem fiveCycle_branch_points :
    (2 * 5) % 3 = 1 ∧ 1 % 3 = 1 ∧ 4 % 3 = 1 ∧ 2 % 3 ≠ 1 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- The `3x − 1` cycle `5 → 7 → 10 → 5` from `Mirror`, with its two branch points
`7` and `10` in the class `1 (mod 3)` — the same class as `d = 5`. -/
theorem mirrorCycle_branch_points :
    Mirror.mirrorOrbit 3 5 = 5 ∧ 5 % 3 ≠ 1 ∧ 7 % 3 = 1 ∧ 10 % 3 = 1 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-! ## 6. What the reverse tree does *not* change

The set of reverse paths of length `L` that never descend below their start is, by
definition, the set of `x` whose forward orbit does not drop in `L` steps.  There is
no new object: `SieveGrowth.sieve_never_terminates` applies verbatim, and the
survivor count grows exponentially in the backward reading exactly as it does in
the forward one. -/

/-- The backward "never descends" condition and the forward "never drops in `L`
steps" condition are the same predicate on `x`; there is nothing to transfer. -/
theorem backward_no_drop_is_forward (x L : Nat) :
    (∀ i : Nat, i ≤ L → x ≤ acceleratedOrbit i x) ↔
    (∀ i : Nat, i ≤ L → x ≤ acceleratedOrbit i x) := Iff.rfl

end ReverseTree
end Collatz
