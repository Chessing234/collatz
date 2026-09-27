import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Hayat Rezgui, "Some remarkable notes related to the Collatz conjecture", 2025.

Title: Some remarkable notes related to the Collatz conjecture

Abstract (from harvested metadata, truncated):
The aim of this short paper is to mention (and demonstrate) some very important results related to the Collatz conjecture. We will show the truth of this conjecture, in special cases, using reasoning by recurrence. We conclude that there is only one case where no one have not yet reached any conclusion (proving or disproving the Collatz conjecture). So, just one step is missing (to complete these results), and if anyone manages to pass it, the Collatz conjecture will be solved (either by proving it right or proving it wrong) once and for all.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.31559/glm2025.15.2.3
-/

namespace Collatz.Papers.Journal_10_31559_glm2025_15_2_3

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Hayat Rezgui, \"Some remarkable notes related to the Collatz conjecture\", General Letters in Mathematics, DOI:10.31559/glm2025.15.2.3 [2025]."

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

end Collatz.Papers.Journal_10_31559_glm2025_15_2_3
