import Collatz.Structure.NaturalDensityCounting

/-! Relating half-open counts on [0,N) to the existing positive count on [1,N]. -/
namespace Collatz.NaturalDensity
open PeriodicCounting

/-- Predicate counting is independent of the chosen decision procedure. -/
theorem predicateCount_eq_decidable (P : Nat → Prop) [∀ n, Decidable (P n)] (N : Nat) :
    predicateCount P N = countBelow (fun n => decide (P n)) N := by
  classical
  unfold predicateCount
  apply congrArg (fun f => countBelow f N)
  funext n
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]

/-- The positive count is exactly a shifted half-open count. -/
theorem countUpTo_eq_shift (P : Nat → Prop) [∀ n, Decidable (P n)] (N : Nat) :
    countUpTo P N = countBelow (fun n => decide (P (n+1))) N := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [countUpTo, count_succ, ih]
    simp only [decide_eq_true_eq]

/-- If zero is excluded, the positive count contains the half-open count. -/
theorem predicateCount_le_countUpTo (P : Nat → Prop) [∀ n, Decidable (P n)]
    (hz : ¬ P 0) (N : Nat) : predicateCount P N ≤ countUpTo P N := by
  rw [predicateCount_eq_decidable, countUpTo_eq_shift]
  have hshift := count_add_shift (fun n => decide (P n)) 1 N
  have hzero : countBelow (fun n => decide (P n)) 1=0 := by
    rw [show (1:Nat)=0+1 from rfl, count_succ, count_zero]
    simp only [hz, decide_false, Bool.false_eq_true, ite_false, Nat.add_zero]
  rw [hzero, Nat.zero_add] at hshift
  have hmono := count_mono (fun n => decide (P n)) (show N≤1+N by omega)
  rw [hshift] at hmono
  simpa only [Nat.add_comm] using hmono

end Collatz.NaturalDensity
