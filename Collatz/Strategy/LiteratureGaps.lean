import Collatz.Core.Reach
import Collatz.Core.Minimum
import Collatz.Strategy.EscapeSchema

/-!
# The recurring gaps in claimed proofs, formalized

Every claimed proof of the Collatz conjecture that the literature has diagnosed
fails at one of a small number of steps.  This file formalizes those steps.  The
result in each case is the same and is the point of the file: **the gap is not a
slip that can be patched, it is the conjecture wearing a different notation.**
Each section therefore ends in an `iff` with `CollatzConjecture`, which is the
precise sense in which the argument is circular.

## The four gaps

**G1 — the inverse tree is assumed to cover ℕ.**  Papers that grow a tree from
the root `1` by inverse Collatz steps and then assert that every positive integer
appears on it.  `Tree` is that tree, defined inductively; `tree_iff_reachesOne`
proves it is *exactly* the set of convergent numbers, so
`treeCoversAll_iff_conjecture` shows the coverage claim is the conjecture.

**G2 — a non-terminating descent is walked to the root.**  Papers that assume a
counterexample, follow it downwards, and "arrive" at `1`.  Refuted in
`Collatz/Strategy/EscapeSchema.lean`; restated here as `no_escape_to_root`.

**G3 — a balance/stopping time is asserted to exist.**  Papers that argue the
number of halvings catches up with the number of tripling steps at some finite
time, usually justified by calling the parities "independent with equal
probability".  `stoppingTime_iff_conjecture` shows that the existence of that
time, for every start, is again the conjecture.

**G4 — a preimage is confused with a forward orbit.**  From `3k + 1 = n` one may
not conclude that `n` lies on the forward orbit of `k`: when `k` is even the map
halves it instead.  `step_even_ne_triple_succ` is the one-line refutation.

## The falsification harness

`genStep a b` is the `an + b` family.  A proof of Collatz must use some property
that separates `3n+1` from its siblings, because
`five_n_plus_one_has_cycle` and `three_n_minus_one_has_cycle` exhibit non-trivial
cycles for two of them.  The second is the sharp one: `3n - 1` has the same
growth heuristic as `3n + 1` (multiply by 3, divide by 2 on average) and yet
cycles, so no argument that is blind to the sign of the constant can exclude
cycles for `3n + 1`.

No Mathlib, no `sorry`.
-/

namespace Collatz
namespace LiteratureGaps

open Reach

/-! ## G1 — the inverse Collatz tree

The tree grown from the root `1` by the two inverse steps `n ↦ 2n` and, when
`n` is odd, `3n + 1 ↦ n`. -/

/-- Membership in the inverse Collatz tree rooted at `1`. -/
inductive Tree : Nat → Prop where
  /-- The root. -/
  | root : Tree 1
  /-- Doubling: the inverse of a halving step. -/
  | dbl {n : Nat} : 0 < n → Tree n → Tree (2 * n)
  /-- The inverse of a tripling step, available only at odd `n`. -/
  | odd {n : Nat} : 0 < n → n % 2 = 1 → Tree (3 * n + 1) → Tree n

/-- A doubled positive number is even and halves back. -/
private theorem step_two_mul {n : Nat} (hn : 0 < n) : step (2 * n) = n := by
  have h0 : 2 * n ≠ 0 := by omega
  have h2 : (2 * n) % 2 = 0 := by omega
  simp [step, h0, h2]

/-- An odd number triples. -/
private theorem step_odd {n : Nat} (_hn : 0 < n) (h : n % 2 = 1) :
    step n = 3 * n + 1 := by
  have h0 : n ≠ 0 := by omega
  have h2 : n % 2 ≠ 0 := by omega
  simp [step, h0, h2]

/-- Every node of the tree reaches `1`: the tree is contained in the convergent
set.  This direction is sound, and is the only direction such papers prove. -/
theorem reachesOne_of_tree {n : Nat} (h : Tree n) : ReachesOne n := by
  induction h with
  | root => exact reachesOne_one
  | dbl hn _ ih =>
    exact reachesOne_of_step (by rw [step_two_mul hn]; exact ih)
  | odd hn hodd _ ih =>
    exact reachesOne_of_step (by rw [step_odd hn hodd]; exact ih)

/-- Every convergent number is a node of the tree.  This is the converse
direction, and it is also sound — the tree really is the convergent set. -/
theorem tree_of_reachesOne : ∀ (k n : Nat), 0 < n → orbit k n = 1 → Tree n := by
  intro k
  induction k with
  | zero =>
    intro n _ h
    have : n = 1 := h
    subst this
    exact Tree.root
  | succ k ih =>
    intro n hn h
    rw [orbit_succ_steps] at h
    have hstep : Tree (step n) := ih (step n) (step_positive hn) h
    by_cases hpar : n % 2 = 0
    · have hn2 : 0 < n / 2 := by omega
      have hhalf : step n = n / 2 := by
        have h0 : n ≠ 0 := by omega
        simp [step, h0, hpar]
      have hdouble : 2 * (n / 2) = n := by omega
      have := Tree.dbl hn2 (by rw [← hhalf]; exact hstep)
      rwa [hdouble] at this
    · have hodd : n % 2 = 1 := by omega
      exact Tree.odd hn hodd (by rw [← step_odd hn hodd]; exact hstep)

/-- **The tree is exactly the convergent set.** -/
theorem tree_iff_reachesOne {n : Nat} (hn : 0 < n) : Tree n ↔ ReachesOne n := by
  constructor
  · exact reachesOne_of_tree
  · intro h
    obtain ⟨k, hk⟩ := h
    exact tree_of_reachesOne k n hn hk

/-- The coverage claim: every positive integer appears on the tree. -/
def TreeCoversAll : Prop := ∀ n : Nat, 0 < n → Tree n

/-- **G1.**  The step "the tree grows to include every positive integer" is
logically equivalent to the Collatz conjecture.  A paper that asserts it, or
derives it from the tree growing indefinitely, has assumed its conclusion. -/
theorem treeCoversAll_iff_conjecture : TreeCoversAll ↔ CollatzConjecture := by
  constructor
  · intro h n hn
    exact reachesOne_of_tree (h n hn)
  · intro h n hn
    exact (tree_iff_reachesOne hn).mpr (h n hn)

/-! ## G2 — walking a counterexample down to the root -/

/-- **G2.**  Under the assumption that `n` never reaches `1`, no point of its
forward orbit reaches `1`, so the descent never arrives at the root and no
contradiction is produced.  (Proved in `EscapeSchema`.) -/
theorem no_escape_to_root {n : Nat} (h : ¬ ReachesOne n) (k : Nat) :
    ¬ ReachesOne (orbit k n) :=
  EscapeSchema.no_escape h k

/-! ## G3 — the asserted balance time

The recurring phrasing is that because the parities are "independent events with
equal probability", there is a finite time at which the halvings have caught up
with the triplings, so the orbit has returned below its start.  That existence
claim is the finiteness of the stopping time. -/

/-- Every positive `n > 1` has a finite stopping time. -/
def StoppingTimeFinite : Prop :=
  ∀ n : Nat, 1 < n → ∃ k : Nat, 0 < k ∧ orbit k n < n

/-- **G3.**  Finiteness of the stopping time for every start is equivalent to the
Collatz conjecture.  So asserting that the halvings eventually catch up — on
whatever probabilistic grounds — assumes the conjecture. -/
theorem stoppingTime_iff_conjecture : StoppingTimeFinite ↔ CollatzConjecture := by
  constructor
  · intro hs
    refine Minimum.no_pos_counterexample_of_descent ?_
    intro n hn hne
    have hn1 : 1 < n := by
      rcases Nat.lt_or_ge 1 n with h | h
      · exact h
      · exact absurd (by
          have : n = 1 := by omega
          subst this
          exact reachesOne_one) hne
    obtain ⟨k, _, hlt⟩ := hs n hn1
    refine ⟨orbit k n, orbit_positive hn k, hlt, ?_⟩
    intro hm
    exact hne ((reachesOne_iff_orbit k n).mpr hm)
  · intro hc n hn1
    obtain ⟨k, hk⟩ := hc n (by omega)
    refine ⟨k, ?_, ?_⟩
    · rcases Nat.eq_zero_or_pos k with h | h
      · exfalso
        subst h
        have hn1' : n = 1 := hk
        omega
      · exact h
    · rw [hk]; omega

/-! ## G4 — a preimage is not a forward step

If `k` is even then `step k = k / 2`, never `3k + 1`.  So from `3k + 1 = n` and
"`k` reaches `1`" one may not conclude that `n` reaches `1`: the forward orbit of
`k` halves it and never visits `n`. -/

/-- **G4.**  The tripling branch is unavailable at even `k`. -/
theorem step_even_ne_triple_succ {k : Nat} (hk : 0 < k) (h : k % 2 = 0) :
    step k ≠ 3 * k + 1 := by
  have h0 : k ≠ 0 := by omega
  have : step k = k / 2 := by simp [step, h0, h]
  rw [this]
  omega

/-- The sound rule the broken one is mistaken for: convergence transfers along a
*forward* step, in either direction. -/
theorem reachesOne_step_iff (n : Nat) : ReachesOne n ↔ ReachesOne (step n) :=
  reachesOne_iff_step n

/-! ## The falsification harness

A generalized map on `ℤ`, used as a test: an argument that never touches the
particular values `a = 3`, `b = 1` proves the same statement for these siblings,
and the siblings are false. -/

/-- The `an + b` variant of the Collatz map on the integers. -/
def genStep (a b : Int) (n : Int) : Int :=
  if n % 2 = 0 then n / 2 else a * n + b

/-- Iteration of `genStep`. -/
def genOrbit (a b : Int) : Nat → Int → Int
  | 0, n => n
  | k + 1, n => genOrbit a b k (genStep a b n)

/-- **The `5n + 1` map has a non-trivial cycle** of length 10 through `13`:
`13 → 66 → 33 → 166 → 83 → 416 → 208 → 104 → 52 → 26 → 13`. -/
theorem five_n_plus_one_has_cycle : genOrbit 5 1 10 13 = 13 := by decide

/-- A second, disjoint `5n + 1` cycle, through `17`. -/
theorem five_n_plus_one_has_second_cycle : genOrbit 5 1 10 17 = 17 := by decide

/-- **The `3n - 1` map has a non-trivial cycle** of length 5 through `5`:
`5 → 14 → 7 → 20 → 10 → 5`.  This is the sharp test: `3n - 1` has exactly the
same growth heuristic as `3n + 1`, so any cycle-exclusion argument insensitive to
the sign of the constant is refuted here. -/
theorem three_n_minus_one_has_cycle : genOrbit 3 (-1) 5 5 = 5 := by decide

/-- A longer `3n - 1` cycle, of length 18 through `17`. -/
theorem three_n_minus_one_has_long_cycle : genOrbit 3 (-1) 18 17 = 17 := by decide

/-- Equivalently, the genuine `3n + 1` map has a non-trivial cycle on the
*negative* integers: `-5 → -14 → -7 → -20 → -10 → -5`.  Any argument that never
uses positivity proves too much. -/
theorem three_n_plus_one_negative_cycle : genOrbit 3 1 5 (-5) = -5 := by decide

/-- And a second negative cycle of length 18, through `-17`. -/
theorem three_n_plus_one_negative_long_cycle : genOrbit 3 1 18 (-17) = -17 := by decide

/-- The trivial cycle, for contrast: `1 → 4 → 2 → 1`. -/
theorem three_n_plus_one_trivial_cycle : genOrbit 3 1 3 1 = 1 := by decide

/-! ## The tree test

The inverse-tree argument (G1) reasons only from the *shape* of the backward
branching: every node has a doubling parent `2n`, and some nodes have one further
odd parent.  That shape is identical for `3n + 1` and `3n - 1` — only the
congruence selecting the odd parent differs.  So the argument cannot distinguish
them, and for `3n - 1` its conclusion is false: the tree rooted at `1` misses `5`,
which sits on a disjoint cycle.  The theorems below prove that. -/

/-- The `3n - 1` cycle through `5`, as a predicate. -/
private abbrev OnFiveCycle (x : Int) : Prop :=
  x = 5 ∨ x = 14 ∨ x = 7 ∨ x = 20 ∨ x = 10

/-- The cycle is closed under the `3n - 1` step. -/
private theorem onFiveCycle_step {x : Int} (h : OnFiveCycle x) :
    OnFiveCycle (genStep 3 (-1) x) := by
  rcases h with h | h | h | h | h <;> subst h <;> decide

/-- No point of the cycle is `1`. -/
private theorem onFiveCycle_ne_one {x : Int} (h : OnFiveCycle x) : x ≠ 1 := by
  rcases h with h | h | h | h | h <;> subst h <;> decide

/-- **The `3n - 1` orbit of `5` never reaches `1`.** -/
theorem three_n_minus_one_five_never_one :
    ∀ (k : Nat) (x : Int), OnFiveCycle x → genOrbit 3 (-1) k x ≠ 1 := by
  intro k
  induction k with
  | zero => intro x hx; exact onFiveCycle_ne_one hx
  | succ k ih =>
    intro x hx
    exact ih (genStep 3 (-1) x) (onFiveCycle_step hx)

/-- **The tree test.**  For the `3n - 1` map, `5` is not reachable-to-`1`, hence
not on the inverse tree rooted at `1`.  Any argument that the inverse tree covers
every positive integer, using only the backward branching shape, therefore proves
a false statement and cannot be valid for `3n + 1` either. -/
theorem three_n_minus_one_tree_misses_five :
    ¬ ∃ k : Nat, genOrbit 3 (-1) k 5 = 1 := by
  intro h
  obtain ⟨k, hk⟩ := h
  exact three_n_minus_one_five_never_one k 5 (Or.inl rfl) hk

/-! ## Axiom audit -/

#print axioms treeCoversAll_iff_conjecture
#print axioms stoppingTime_iff_conjecture
#print axioms three_n_minus_one_has_cycle
#print axioms three_n_minus_one_tree_misses_five

end LiteratureGaps
end Collatz
