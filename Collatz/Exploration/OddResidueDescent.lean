import Collatz.Strategy.Pillars

/-! Universal accelerated descent reduces to one odd residue class modulo four.
This elementary reduction isolates the hard case; it does not solve it. -/
namespace Collatz.Exploration.OddResidueDescent
open Collatz
open Collatz.Strategy

/-- Every input congruent to one modulo four descends in at most two steps. -/
theorem descent_two_of_one_mod_four {n : Nat} (hn : 1 < n) (hmod : n % 4 = 1) :
    ∃ k : Nat, k ≤ 2 ∧ acceleratedOrbit k n < n := by
  obtain ⟨m, rfl⟩ : ∃ m : Nat, n = 4*m+1 := by omega
  refine ⟨2, by omega, ?_⟩
  have h1 : acceleratedStep (4*m+1) = 6*m+2 := by
    simp [acceleratedStep]
    omega
  have h2 : acceleratedStep (6*m+2) = 3*m+1 := by
    simp [acceleratedStep]
    omega
  calc
    acceleratedOrbit 2 (4*m+1) = acceleratedStep (acceleratedStep (4*m+1)) := rfl
    _ = 3*m+1 := by rw [h1, h2]
    _ < 4*m+1 := by omega

/-- The only odd residue class still needing a descent argument. -/
def DescentOnThreeModFour : Prop :=
  ∀ n : Nat, 1 < n → n % 4 = 3 → ∃ k : Nat, acceleratedOrbit k n < n

/-- A descent theorem on the three-mod-four class supplies universal descent. -/
theorem finiteStoppingTime_of_three_mod_four (h : DescentOnThreeModFour) :
    FiniteStoppingTime := by
  intro n hn
  rcases Arith.mod_two_eq_zero_or_one n with heven | hodd
  · refine ⟨1, ?_⟩
    have hs : acceleratedOrbit 1 n = n/2 := by
      unfold acceleratedOrbit acceleratedStep
      simp [heven]
    rw [hs]
    omega
  · have hmododd : n % 4 = 1 ∨ n % 4 = 3 := by omega
    rcases hmododd with hmod | hmod
    · obtain ⟨k, hk, hd⟩ := descent_two_of_one_mod_four hn hmod
      exact ⟨k, hd⟩
    · exact h n hn hmod

/-- Hence the same single congruence-class hypothesis implies Collatz. -/
theorem collatz_of_three_mod_four (h : DescentOnThreeModFour) : CollatzConjecture :=
  collatz_of_finiteStoppingTime (finiteStoppingTime_of_three_mod_four h)

/-- The bound of two steps cannot replace the hypothesis on the hard class. -/
theorem seven_does_not_descend_in_two : ¬ acceleratedOrbit 2 7 < 7 := by decide

end Collatz.Exploration.OddResidueDescent
