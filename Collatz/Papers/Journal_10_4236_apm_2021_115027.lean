import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Zuojun Hu, "The Analysis of Convergence for the 3X + 1 Problem and Crandall Conjecture for the aX + 1 Problem", 2021.

Title: The Analysis of Convergence for the 3X + 1 Problem and Crandall Conjecture for the aX + 1 Problem

Abstract (from harvested metadata, truncated):
(No abstract in harvested metadata; statement recorded from title/venue only.)

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.4236/apm.2021.115027
-/

namespace Collatz.Papers.Journal_10_4236_apm_2021_115027

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Zuojun Hu, \"The Analysis of Convergence for the 3X + 1 Problem and Crandall Conjecture for the aX + 1 Problem\", Advances in Pure Mathematics, DOI:10.4236/apm.2021.115027 [2021]."

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

end Collatz.Papers.Journal_10_4236_apm_2021_115027
