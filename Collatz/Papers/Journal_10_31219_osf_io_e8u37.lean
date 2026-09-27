import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Kavak, Mesut, "Proof for Collatz Conjecture", 2023.

Title: Proof for Collatz Conjecture

Abstract (from harvested metadata, truncated):
"When a positive integer is chosen, if the number is even, it is divided by 2; otherwise, it is multiplied by 3 and after that 1 is added to the result. Due to the condition that the result is odd or even, the same operation is repeated with the required option of the problem, every positive integer other than 0 and 1 can the integer be reduced to 1?"

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.31219/osf.io/e8u37
-/

namespace Collatz.Papers.Journal_10_31219_osf_io_e8u37

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Kavak, Mesut, \"Proof for Collatz Conjecture\", DOI:10.31219/osf.io/e8u37 [2023]."

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

end Collatz.Papers.Journal_10_31219_osf_io_e8u37
