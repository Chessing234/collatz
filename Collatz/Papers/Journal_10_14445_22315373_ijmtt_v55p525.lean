import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Ashok, Joshi B, "Number Set Theory and Collatz Conjecture", 2018.

Title: Number Set Theory and Collatz Conjecture

Abstract (from harvested metadata, truncated):
(No abstract in harvested metadata; statement recorded from title/venue only.)

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.14445/22315373/ijmtt-v55p525
-/

namespace Collatz.Papers.Journal_10_14445_22315373_ijmtt_v55p525

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Ashok, Joshi B, \"Number Set Theory and Collatz Conjecture\", International Journal of Mathematics Trends and Technology, DOI:10.14445/22315373/ijmtt-v55p525 [2018]."

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

end Collatz.Papers.Journal_10_14445_22315373_ijmtt_v55p525
