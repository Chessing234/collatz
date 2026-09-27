import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Liu Shuai et al., "Attraction in Positive Direction of Real Axis of Two Generalized 3x + 1 Functions", 2012.

Title: Attraction in Positive Direction of Real Axis of Two Generalized 3x + 1 Functions

Abstract (from harvested metadata, truncated):
(No abstract in harvested metadata; statement recorded from title/venue only.)

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.1007/978-94-007-2169-2_81
-/

namespace Collatz.Papers.Journal_10_1007_978_94_007_2169_2_81

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Liu Shuai et al., \"Attraction in Positive Direction of Real Axis of Two Generalized 3x + 1 Functions\", Lecture Notes in Electrical Engineering, DOI:10.1007/978-94-007-2169-2_81 [2012]."

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

end Collatz.Papers.Journal_10_1007_978_94_007_2169_2_81
