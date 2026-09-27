import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Jacqueline Wötzel, "The Order of Numbers and the Collatz Problem", 2023.

Title: The Order of Numbers and the Collatz Problem

Abstract (from harvested metadata, truncated):
The algorithm of Collatz is also known the 3n+1 problem. It will be started with any uneven natural number (n). This number is to triple and add one. Then divide by two as often as possible, if the number is even. If the number is odd, use again the 3n+1 step. The conjecture of the Collatz problem is that these operations always reach 1, no matter which positive integer is chosen to start the algorithm. A view to an order of numbers gives an explanation for the dominance of degressive steps to reach 1. The idea to identify the order of numbers is developed from an interview of Dr. Peter Plichta where he spoke on his book “Das Primzahlenkreuz”.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5121/ijcsa.2023.13201
-/

namespace Collatz.Papers.Journal_10_5121_ijcsa_2023_13201

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Jacqueline Wötzel, \"The Order of Numbers and the Collatz Problem\", International Journal on Computational Science & Applications, DOI:10.5121/ijcsa.2023.13201 [2023]."

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

end Collatz.Papers.Journal_10_5121_ijcsa_2023_13201
