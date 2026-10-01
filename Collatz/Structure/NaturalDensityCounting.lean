import Collatz.Structure.NaturalDensity

/-! Compatibility and complement identities for the natural-density count. -/
namespace Collatz.NaturalDensity
open PeriodicCounting

/-- Classical predicate counting agrees with a supplied Boolean decision procedure. -/
theorem predicateCount_bool (P : Nat → Bool) (N : Nat) :
    predicateCount (fun n => P n=true) N = countBelow P N := by
  classical
  unfold predicateCount
  apply congrArg (fun f => countBelow f N)
  funext n
  cases hn : P n <;> simp [hn]

/-- A predicate and its complement partition every finite initial interval. -/
theorem predicateCount_complement (P : Nat → Prop) (N : Nat) :
    predicateCount P N + predicateCount (fun n => ¬ P n) N = N := by
  classical
  unfold predicateCount
  dsimp only
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [count_succ, count_succ]
    by_cases h : P N <;> simp only [h, decide_true, decide_false, not_true_eq_false,
      not_false_eq_true, Bool.false_eq_true, ite_false, ite_true] <;> omega

end Collatz.NaturalDensity
