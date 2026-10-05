import Collatz.Strategy.FirstDescentScale

/-!
# Exact classification of the first two descent times

First descent at time one is exactly the positive even class. First descent
at time two is exactly the class one modulo four above the trivial input one.
Time three is impossible. These statements classify all initial values,
rather than infer a classification from a finite table.
-/

namespace Collatz.FirstDescentResidue

/-- Any input with a stopping time is greater than one. -/
theorem input_gt_one_of_stoppingTime {n k : Nat} (hk : stoppingTime n k) : 1 < n := by
  have hd := hk.2.1
  have hn : 0 < n := by omega
  have hp := acceleratedOrbit_positive hn k
  omega

/-- Two-step endpoint on the odd class that immediately takes an even step. -/
theorem two_step_mod_four_one {n : Nat} (hn : n % 4 = 1) :
    acceleratedOrbit 2 n = (3 * n + 1) / 4 := by
  have ho : n % 2 ≠ 0 := by omega
  have hs : acceleratedStep n = (3 * n + 1) / 2 := by
    simp only [acceleratedStep, if_neg ho]
  have he : ((3 * n + 1) / 2) % 2 = 0 := by omega
  change acceleratedStep (acceleratedStep n) = _
  rw [hs]
  simp only [acceleratedStep, if_pos he]
  omega

/-- The opposite odd class takes two increasing odd steps. -/
theorem two_step_mod_four_three {n : Nat} (hn : n % 4 = 3) :
    n < acceleratedOrbit 2 n := by
  have ho : n % 2 ≠ 0 := by omega
  have hs : acceleratedStep n = (3 * n + 1) / 2 := by
    simp only [acceleratedStep, if_neg ho]
  have ho2 : ((3 * n + 1) / 2) % 2 ≠ 0 := by omega
  change n < acceleratedStep (acceleratedStep n)
  rw [hs]
  simp only [acceleratedStep, if_neg ho2]
  omega

/-- Every nontrivial member of the class one modulo four first descends at time two. -/
theorem stoppingTime_two_of_mod_four_one {n : Nat} (hn : 1 < n) (hr : n % 4 = 1) :
    stoppingTime n 2 := by
  refine ⟨by decide, ?_, ?_⟩
  · rw [two_step_mod_four_one hr]
    omega
  · intro j hj hj2
    have he : j = 1 := by omega
    subst j
    have ho := odd_step_increases (show n % 2 = 1 by omega)
    change ¬ acceleratedStep n < n
    omega

/-- A two-step first descent can only start in the class one modulo four. -/
theorem mod_four_one_of_stoppingTime_two {n : Nat} (hk : stoppingTime n 2) : n % 4 = 1 := by
  have hn := input_gt_one_of_stoppingTime hk
  have ho : n % 2 = 1 := by
    by_cases he : n % 2 = 0
    · have hu := stoppingTime_unique hk (stoppingTime_of_even (by omega) he)
      omega
    · omega
  by_cases hr : n % 4 = 1
  · exact hr
  · have hr3 : n % 4 = 3 := by omega
    have hg := two_step_mod_four_three hr3
    have hd := hk.2.1
    omega

/-- Complete classification of two-step first descent. -/
theorem stoppingTime_two_iff (n : Nat) :
    stoppingTime n 2 ↔ 1 < n ∧ n % 4 = 1 := by
  constructor
  · intro hk
    exact ⟨input_gt_one_of_stoppingTime hk, mod_four_one_of_stoppingTime_two hk⟩
  · rintro ⟨hn, hr⟩
    exact stoppingTime_two_of_mod_four_one hn hr

/-- Three iterations of the class three modulo four still stay above the input. -/
theorem three_step_mod_four_three {n : Nat} (hn : n % 4 = 3) :
    n ≤ acceleratedOrbit 3 n := by
  have ho : n % 2 ≠ 0 := by omega
  have hs : acceleratedStep n = (3 * n + 1) / 2 := by
    simp only [acceleratedStep, if_neg ho]
  have ho2 : ((3 * n + 1) / 2) % 2 ≠ 0 := by omega
  have ht : acceleratedOrbit 2 n = (3 * ((3 * n + 1) / 2) + 1) / 2 := by
    change acceleratedStep (acceleratedStep n) = _
    rw [hs]
    simp only [acceleratedStep, if_neg ho2]
  rw [acceleratedOrbit_succ_step, ht]
  by_cases he : ((3 * ((3 * n + 1) / 2) + 1) / 2) % 2 = 0
  · simp only [acceleratedStep, if_pos he]
    omega
  · simp only [acceleratedStep, if_neg he]
    omega

/-- No natural input first descends at exactly time three. -/
theorem no_stoppingTime_three (n : Nat) : ¬ stoppingTime n 3 := by
  intro hk
  have hn := input_gt_one_of_stoppingTime hk
  by_cases he : n % 2 = 0
  · have hu := stoppingTime_unique hk (stoppingTime_of_even (by omega) he)
    omega
  · have ho : n % 2 = 1 := by omega
    by_cases hr : n % 4 = 1
    · have hu := stoppingTime_unique hk (stoppingTime_two_of_mod_four_one hn hr)
      omega
    · have hr3 : n % 4 = 3 := by omega
      have hg := three_step_mod_four_three hr3
      have hd := hk.2.1
      omega

end Collatz.FirstDescentResidue
