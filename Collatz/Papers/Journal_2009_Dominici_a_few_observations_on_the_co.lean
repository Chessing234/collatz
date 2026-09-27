import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Diego Dominici, "A few observations on the Collatz problem", 2009.

Title: A few observations on the Collatz problem

Abstract (from harvested metadata, truncated):
We establish an equivalent condition to the validity of the Collatz conjecture, using elementary methods. We derive some conclusions and show several examples of our results. We also offer some further problems and conjectures.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: (no stable URL in metadata)
-/

namespace Collatz.Papers.Journal_2009_Dominici_a_few_observations_on_the_co

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Diego Dominici, \"A few observations on the Collatz problem\", International Journal of Applied Mathematics & Statistics/International journal of applied mathematics and statistics [2009]."

/-- Recorded main claim shell (structural); the paper's theorem is not proved here.
This placeholder is the standard Collatz conjecture proposition. -/
def mainStatement : Prop := Collatz.CollatzConjecture

/-- Checked bridge facts only. -/
theorem step_one_eq : Collatz.step 1 = 4 := Collatz.step_one

theorem step_two_eq : Collatz.step 2 = 1 := Collatz.step_two

/-- Checked: every power of two reaches `1` (Mathlib-copied parity/division facts). -/
theorem powers_of_two_reach_one (k : Nat) :
    ∃ t : Nat, Collatz.orbit t (2 ^ k) = 1 :=
  Collatz.Papers.MathlibCopied.orbit_pow_two_reaches_one k

end Collatz.Papers.Journal_2009_Dominici_a_few_observations_on_the_co
