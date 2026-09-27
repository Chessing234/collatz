import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Josefina López and Peter Stoll, "The 3x + 1 Conjugacy Map over a Sturmian Word", 2009.

Title: The 3x + 1 Conjugacy Map over a Sturmian Word

Abstract (from harvested metadata, truncated):
(No abstract in harvested metadata; statement recorded from title/venue only.)

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.1515/integ.2009.014
-/

namespace Collatz.Papers.Journal_10_1515_integ_2009_014

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Josefina López and Peter Stoll, \"The 3x + 1 Conjugacy Map over a Sturmian Word\", Integers, DOI:10.1515/integ.2009.014 [2009]."

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

end Collatz.Papers.Journal_10_1515_integ_2009_014
