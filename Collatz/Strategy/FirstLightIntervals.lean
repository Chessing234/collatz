import Collatz.Strategy.FirstLightScanComplete

/-! Finite interval certificates allow large exceptional ranges to be checked
in independent kernel reductions, without one enormous Boolean evaluation. -/
namespace Collatz.FirstLightScan
open FirstLightDescent

/-- Check a half-open interval, ignoring the excluded starts 0 and 1. -/
def checkInterval (H start len : Nat) : Bool :=
  (List.range' start len).all fun n => n≤1 || check H n

/-- A checked interval supplies the exact first-crossing witness for each member. -/
theorem checkInterval_sound (H start len : Nat)
    (h : checkInterval H start len = true) (n : Nat)
    (hlo : start≤n) (hhi : n<start+len) (hn : 1<n) :
    ∃ k : Fin (H+1), FirstLight n k.val ∧ acceleratedOrbit k.val n < n := by
  have hmem : n ∈ List.range' start len :=
    List.mem_range'.mpr ⟨n-start, by omega, by omega⟩
  have hall := List.all_eq_true.mp h n hmem
  have hc : check H n = true := by
    simpa only [Bool.or_eq_true, decide_eq_true_eq, show ¬ n≤1 by omega, false_or] using hall
  exact check_sound H n hc

/-- Completeness: certificates lose no valid bounded first-crossing descents. -/
theorem checkInterval_complete (H start len : Nat)
    (h : ∀ n, start≤n → n<start+len → 1<n →
      ∃ k : Fin (H+1), FirstLight n k.val ∧ acceleratedOrbit k.val n < n) :
    checkInterval H start len = true := by
  apply List.all_eq_true.mpr
  intro n hn
  obtain ⟨i, hi, he⟩ := List.mem_range'.mp hn
  simp only [Nat.one_mul] at he
  rw [Bool.or_eq_true]
  by_cases hsmall : n≤1
  · exact Or.inl (decide_eq_true_eq.mpr hsmall)
  · exact Or.inr ((check_iff H n).mpr (h n (by omega) (by omega) (by omega)))

/-- Adjacent checked intervals combine without reevaluating their trajectories. -/
theorem checkInterval_append (H start left right : Nat)
    (hl : checkInterval H start left = true)
    (hr : checkInterval H (start+left) right = true) :
    checkInterval H start (left+right) = true := by
  apply checkInterval_complete
  intro n hlo hhi hn
  by_cases hm : n<start+left
  · exact checkInterval_sound H start left hl n hlo hm hn
  · exact checkInterval_sound H (start+left) right hr n (by omega) (by omega) hn

/-- Increasing the horizon preserves a successful interval certificate. -/
theorem checkInterval_mono_horizon (H K start len : Nat) (hHK : H≤K)
    (h : checkInterval H start len = true) : checkInterval K start len = true := by
  apply checkInterval_complete
  intro n hlo hhi hn
  obtain ⟨k, hf, hd⟩ := checkInterval_sound H start len h n hlo hhi hn
  exact ⟨⟨k.val, by have := k.isLt; omega⟩, hf, hd⟩

end Collatz.FirstLightScan
