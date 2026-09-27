import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Jinqing Zhang and Xintong Zhang, "Collatz Iterative Trajectories of All Odd Numbers Attain Bounded Values", 2023.

Title: Collatz Iterative Trajectories of All Odd Numbers Attain Bounded Values

Abstract (from harvested metadata, truncated):
The aim of this paper is to study the 3x + 1 problem based on the Collatz iterative formula. It can be seen from the iterative formula that the necessary condition for the Collatz iteration convergence is that its slope being less than 1. An odd number N that satisfies the condition of a slope less than 1 after nth Collatz iterations is defined as an n-step odd number. Through statistical analysis, it is found that after nth Collatz iterations, the iterative value of any n-step odd number N that is greater than 1 is less than N, which proves that the slope less than 1 is a sufficient and necessary condition for Collatz iteration convergence.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.4236/jamp.2023.1110200
-/

namespace Collatz.Papers.Journal_10_4236_jamp_2023_1110200

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Jinqing Zhang and Xintong Zhang, \"Collatz Iterative Trajectories of All Odd Numbers Attain Bounded Values\", Journal of Applied Mathematics and Physics, DOI:10.4236/jamp.2023.1110200 [2023]."

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

end Collatz.Papers.Journal_10_4236_jamp_2023_1110200
