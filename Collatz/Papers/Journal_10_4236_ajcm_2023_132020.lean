import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for David C. Kay, "A Solution to the 3x + 1 Problem", 2023.

Title: A Solution to the 3x + 1 Problem

Abstract (from harvested metadata, truncated):
The author makes the claim to have a solution for the famous 3x + 1 problem. The key to its solution is a special proof that the term (3 + ε)r is a non-integer, as well as the use of properties of extremal points of a Collatz sequence.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.4236/ajcm.2023.132020
-/

namespace Collatz.Papers.Journal_10_4236_ajcm_2023_132020

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "David C. Kay, \"A Solution to the 3x + 1 Problem\", American Journal of Computational Mathematics, DOI:10.4236/ajcm.2023.132020 [2023]."

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

end Collatz.Papers.Journal_10_4236_ajcm_2023_132020
