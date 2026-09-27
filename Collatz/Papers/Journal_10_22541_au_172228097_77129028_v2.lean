import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Abascal, Guillermo Wells, "Bottom-up Approach to the Collatz Conjecture", 2024.

Title: Bottom-up Approach to the Collatz Conjecture

Abstract (from harvested metadata, truncated):
The Collatz conjecture states that, by following two specific arithmetic operations, every positive integer can be transformed into 1. The rules are that each even number must be divided by 2, while odd numbers are multiplied by 3 and then 1 is added to them. Despite its simplicity, the conjecture has not been proven. For this, an inverted version of the Collatz conjecture, in which it is possible to start from n1=1 to later produce any number, was used to standardize the behavior that the sequence follows. Consequently, formulas were made to describe the observed sequences, and a proof of the tendency of every integer to reach the expected outcome, was developed.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.22541/au.172228097.77129028/v2
-/

namespace Collatz.Papers.Journal_10_22541_au_172228097_77129028_v2

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Abascal, Guillermo Wells, \"Bottom-up Approach to the Collatz Conjecture\", DOI:10.22541/au.172228097.77129028/v2 [2024]."

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

end Collatz.Papers.Journal_10_22541_au_172228097_77129028_v2
