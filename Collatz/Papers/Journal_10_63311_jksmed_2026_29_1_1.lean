import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Mark Applebaum, "Learning to do mathematics as inquiry: A pre-service teacher’s journey with the Collatz conjecture variant", 2026.

Title: Learning to do mathematics as inquiry: A pre-service teacher’s journey with the Collatz conjecture variant

Abstract (from harvested metadata, truncated):
(No abstract in harvested metadata; statement recorded from title/venue only.)

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.63311/jksmed.2026.29.1.1
-/

namespace Collatz.Papers.Journal_10_63311_jksmed_2026_29_1_1

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Mark Applebaum, \"Learning to do mathematics as inquiry: A pre-service teacher’s journey with the Collatz conjecture variant\", Mathematics Education Research and Practice, DOI:10.63311/jksmed.2026.29.1.1 [2026]."

/-- Recorded generalization-style claim shell; the paper's theorem is not proved here.
This placeholder is the standard Collatz conjecture proposition. -/
def mainStatement : Prop := Collatz.CollatzConjecture

/-- Checked bridge facts only. -/
theorem step_one_eq : Collatz.step 1 = 4 := Collatz.step_one

theorem step_two_eq : Collatz.step 2 = 1 := Collatz.step_two

/-- Checked: every power of two reaches `1` (Mathlib-copied parity/division facts). -/
theorem powers_of_two_reach_one (k : Nat) :
    ∃ t : Nat, Collatz.orbit t (2 ^ k) = 1 :=
  Collatz.Papers.MathlibCopied.orbit_pow_two_reaches_one k

end Collatz.Papers.Journal_10_63311_jksmed_2026_29_1_1
