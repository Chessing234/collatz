import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Michael C. I. Nwogugu, "On The Collatz Conjecture.", 2022.

Title: On The Collatz Conjecture.

Abstract (from harvested metadata, truncated):
We propose two conjectures which imply the Collatz conjecture.We give a numerical evidence for the second conjecture.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.2139/ssrn.4170807
-/

namespace Collatz.Papers.Journal_10_2139_ssrn_4170807

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Michael C. I. Nwogugu, \"On The Collatz Conjecture.\", SSRN Electronic Journal, DOI:10.2139/ssrn.4170807 [2022]."

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

end Collatz.Papers.Journal_10_2139_ssrn_4170807
