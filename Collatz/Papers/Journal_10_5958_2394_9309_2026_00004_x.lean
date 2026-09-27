import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Sonam Sharma and Megha Rani, "On the Proof of Collatz Conjecture", 2026.

Title: On the Proof of Collatz Conjecture

Abstract (from harvested metadata, truncated):
In this paper, an attempt has been made to prove the Collatz conjecture by a simple method known as mathematical induction method.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5958/2394-9309.2026.00004.x
-/

namespace Collatz.Papers.Journal_10_5958_2394_9309_2026_00004_x

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Sonam Sharma and Megha Rani, \"On the Proof of Collatz Conjecture\", Arya Bhatta Journal of Mathematics and Informatics, DOI:10.5958/2394-9309.2026.00004.x [2026]."

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

end Collatz.Papers.Journal_10_5958_2394_9309_2026_00004_x
