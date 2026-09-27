import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Petro Kosobutskyy and Volodymyr Karkulovskyy, "RECURRENCE AND STRUCTURING OF SEQUENCES OF TRANSFORMATIONS 3N + 1 AS ARGUMENTS FOR CONFIRMATION OF THE СOLLATZ HYPOTHESIS", 2023.

Title: RECURRENCE AND STRUCTURING OF SEQUENCES OF TRANSFORMATIONS 3N + 1 AS ARGUMENTS FOR CONFIRMATION OF THE СOLLATZ HYPOTHESIS

Abstract (from harvested metadata, truncated):
It is shown that infinites of the subsequence of odd numbers is not a counterargument of the violation of the Collatz hypothesis, but a universal characteristic of transformations of natural numbers by the 3n + 1 algorithm. A recurrent relationship is established between the parameters of the sequence of Collatz transformations of an arbitrary pair of natural numbers n and 2n.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.23939/cds2023.01.028
-/

namespace Collatz.Papers.Journal_10_23939_cds2023_01_028

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Petro Kosobutskyy and Volodymyr Karkulovskyy, \"RECURRENCE AND STRUCTURING OF SEQUENCES OF TRANSFORMATIONS 3N + 1 AS ARGUMENTS FOR CONFIRMATION OF THE СOLLATZ HYPOTHESIS\", Computer Design Systems Theory and Practice, DOI:10.23939/cds2023.01.028 [2023]."

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

end Collatz.Papers.Journal_10_23939_cds2023_01_028
