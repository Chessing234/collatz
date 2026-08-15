import Collatz.Core.Reach

/-!
# Kernel-checked bounded verification

Every serious attack on Collatz starts by clearing an initial segment: if a
counterexample exists, it is larger than everything already checked.  This file
provides that clearance *inside Lean*, so the bound is a theorem rather than a
citation of somebody's C program.

The device is a fuelled Boolean checker, `reachesOneWithin`, together with a
soundness lemma `reachesOne_of_within` transporting a successful Boolean run
into the propositional `ReachesOne`.  A second checker, `allReachOneUpTo`,
sweeps an interval, and `reachesOne_of_le` transports it.

Because the checkers are Boolean and total, statements about concrete bounds
are closed by `decide`, i.e. by kernel computation with no appeal to `native`
evaluation and no axioms.

The exported bound is `reachesOne_of_le_1024`: every `n` with `0 < n ≤ 1024`
reaches `1`.  Consequently any counterexample exceeds `1024`
(`counterexample_gt_1024`), which is the base case used by the descent
arguments in `Collatz.Structure.Minimal`.
-/

namespace Collatz
namespace Search

open Reach

/-! ## The fuelled checker -/

/-- `reachesOneWithin fuel n` is `true` when `n` reaches `1` within `fuel`
standard Collatz steps. -/
def reachesOneWithin : Nat → Nat → Bool
  | 0, n => n == 1
  | fuel + 1, n => if n == 1 then true else reachesOneWithin fuel (step n)

/-- With no fuel, only `1` passes. -/
@[simp] theorem reachesOneWithin_zero (n : Nat) :
    reachesOneWithin 0 n = (n == 1) := rfl

/-- Unfolding the checker at a successor fuel. -/
theorem reachesOneWithin_succ (fuel n : Nat) :
    reachesOneWithin (fuel + 1) n =
      (if n == 1 then true else reachesOneWithin fuel (step n)) := rfl

/-- The checker accepts `1` at every fuel level. -/
@[simp] theorem reachesOneWithin_one (fuel : Nat) : reachesOneWithin fuel 1 = true := by
  cases fuel with
  | zero => rfl
  | succ f => rw [reachesOneWithin_succ]; rfl

/-- Soundness: a successful Boolean run yields a genuine reachability proof. -/
theorem reachesOne_of_within {fuel n : Nat} (h : reachesOneWithin fuel n = true) :
    ReachesOne n := by
  induction fuel generalizing n with
  | zero =>
    have : n = 1 := by
      simpa using h
    subst this
    exact reachesOne_one
  | succ fuel ih =>
    rw [reachesOneWithin_succ] at h
    by_cases hn : n == 1
    · have : n = 1 := by simpa using hn
      subst this
      exact reachesOne_one
    · rw [if_neg hn] at h
      exact reachesOne_of_step (ih h)

/-- The checker is monotone in the fuel. -/
theorem reachesOneWithin_mono {fuel fuel' n : Nat} (hle : fuel ≤ fuel')
    (h : reachesOneWithin fuel n = true) : reachesOneWithin fuel' n = true := by
  induction fuel generalizing fuel' n with
  | zero =>
    have hn : n = 1 := by simpa using h
    subst hn
    exact reachesOneWithin_one fuel'
  | succ fuel ih =>
    cases fuel' with
    | zero => omega
    | succ fuel' =>
      rw [reachesOneWithin_succ] at h ⊢
      by_cases hn : n == 1
      · rw [if_pos hn]
      · rw [if_neg hn] at h ⊢
        exact ih (by omega) h

/-! ## Sweeping an interval -/

/-- `allReachOneUpTo N fuel` is `true` when every `n` with `1 ≤ n ≤ N` reaches
`1` within `fuel` steps. -/
def allReachOneUpTo : Nat → Nat → Bool
  | 0, _ => true
  | m + 1, fuel => reachesOneWithin fuel (m + 1) && allReachOneUpTo m fuel

/-- The empty sweep succeeds. -/
@[simp] theorem allReachOneUpTo_zero (fuel : Nat) : allReachOneUpTo 0 fuel = true := rfl

/-- Unfolding the sweep at a successor. -/
theorem allReachOneUpTo_succ (m fuel : Nat) :
    allReachOneUpTo (m + 1) fuel =
      (reachesOneWithin fuel (m + 1) && allReachOneUpTo m fuel) := rfl

/-- A successful sweep contains a successful individual run. -/
theorem within_of_allReachOneUpTo {N fuel n : Nat} (h : allReachOneUpTo N fuel = true)
    (hn : 0 < n) (hle : n ≤ N) : reachesOneWithin fuel n = true := by
  induction N with
  | zero => omega
  | succ m ih =>
    rw [allReachOneUpTo_succ, Bool.and_eq_true] at h
    by_cases hnm : n = m + 1
    · subst hnm; exact h.1
    · exact ih h.2 (by omega)

/-- Soundness of the sweep. -/
theorem reachesOne_of_le {N fuel n : Nat} (h : allReachOneUpTo N fuel = true)
    (hn : 0 < n) (hle : n ≤ N) : ReachesOne n :=
  reachesOne_of_within (within_of_allReachOneUpTo h hn hle)

/-! ## Concrete verified bounds

Each bound is a single kernel computation.  They are stated separately so that
downstream files can cite the weakest bound that suffices, keeping elaboration
cheap. -/

set_option maxRecDepth 100000 in
/-- Every positive `n ≤ 32` reaches `1`, verified by kernel computation. -/
theorem check_32 : allReachOneUpTo 32 200 = true := by decide

set_option maxRecDepth 100000 in
/-- Every positive `n ≤ 128` reaches `1`, verified by kernel computation. -/
theorem check_128 : allReachOneUpTo 128 200 = true := by decide

set_option maxRecDepth 400000 in
/-- Every positive `n ≤ 1024` reaches `1`, verified by kernel computation. -/
theorem check_1024 : allReachOneUpTo 1024 300 = true := by decide

/-- Every positive `n ≤ 32` reaches `1`. -/
theorem reachesOne_of_le_32 {n : Nat} (hn : 0 < n) (hle : n ≤ 32) : ReachesOne n :=
  reachesOne_of_le check_32 hn hle

/-- Every positive `n ≤ 128` reaches `1`. -/
theorem reachesOne_of_le_128 {n : Nat} (hn : 0 < n) (hle : n ≤ 128) : ReachesOne n :=
  reachesOne_of_le check_128 hn hle

/-- Every positive `n ≤ 1024` reaches `1`. -/
theorem reachesOne_of_le_1024 {n : Nat} (hn : 0 < n) (hle : n ≤ 1024) : ReachesOne n :=
  reachesOne_of_le check_1024 hn hle

/-! ## Consequences for hypothetical counterexamples -/

/-- A counterexample to Collatz exceeds `32`. -/
theorem counterexample_gt_32 {n : Nat} (hn : 0 < n) (h : ¬ ReachesOne n) : 32 < n := by
  by_cases hle : n ≤ 32
  · exact absurd (reachesOne_of_le_32 hn hle) h
  · omega

/-- A counterexample to Collatz exceeds `128`. -/
theorem counterexample_gt_128 {n : Nat} (hn : 0 < n) (h : ¬ ReachesOne n) : 128 < n := by
  by_cases hle : n ≤ 128
  · exact absurd (reachesOne_of_le_128 hn hle) h
  · omega

/-- A counterexample to Collatz exceeds `1024`. -/
theorem counterexample_gt_1024 {n : Nat} (hn : 0 < n) (h : ¬ ReachesOne n) : 1024 < n := by
  by_cases hle : n ≤ 1024
  · exact absurd (reachesOne_of_le_1024 hn hle) h
  · omega

/-- A counterexample is in particular larger than one. -/
theorem counterexample_gt_one {n : Nat} (hn : 0 < n) (h : ¬ ReachesOne n) : 1 < n := by
  have := counterexample_gt_32 hn h; omega

end Search
end Collatz
