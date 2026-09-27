import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Unknown, "A Mathematical Representation of the Collatz Conjecture and its Applications", 2025.

Title: A Mathematical Representation of the Collatz Conjecture and its Applications

Abstract (from harvested metadata, truncated):
(No abstract in harvested metadata; statement recorded from title/venue only.)

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.30546/macosep2025.1239
-/

namespace Collatz.Papers.Journal_10_30546_macosep2025_1239

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Unknown, \"A Mathematical Representation of the Collatz Conjecture and its Applications\", MaCoSEP2025., DOI:10.30546/macosep2025.1239 [2025]."

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

end Collatz.Papers.Journal_10_30546_macosep2025_1239
