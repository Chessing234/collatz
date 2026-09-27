import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Oliver Clay, "The Long Search for Collatz Counterexamples", 2023.

Title: The Long Search for Collatz Counterexamples

Abstract (from harvested metadata, truncated):
Despite decades of effort, the Collatz conjecture remains neither proved, nor refuted by a counterexample, nor formally shown to be undecidable. This note introduces the Collatz problem and probes its logical depth with a test question: can the search space for counterexamples be iteratively reduced, and when would it help?

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5642/jhummath.yqho7207
-/

namespace Collatz.Papers.Journal_10_5642_jhummath_yqho7207

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Oliver Clay, \"The Long Search for Collatz Counterexamples\", Journal of Humanistic Mathematics, DOI:10.5642/jhummath.yqho7207 [2023]."

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

end Collatz.Papers.Journal_10_5642_jhummath_yqho7207
