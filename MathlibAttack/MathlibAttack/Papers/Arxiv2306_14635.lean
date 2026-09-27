import MathlibAttack.Papers.Core

/-!
Mathlib-backed Lean notes for Petro Kosobutskyy, "The Collatz problem (a*q+-1,a=1,3,5,...) from the point of view of transformations of Jacobsthal numbers", arXiv:2306.14635 [2023].

Title: The Collatz problem (a*q+-1,a=1,3,5,...) from the point of view of transformations of Jacobsthal numbers

Abstract (truncated):
In the paper, from the point of view of recurrent numbers of the Jacobsthal type, the Collatz problem with the general aq+-1 function of conjecture odd positive integers q from the set of natural numbers is investigated. Formulated branching rules from nodes with generalized Jacobsthal numbers of the so-called Jacobsthal tree. It is shown that Collatz trajectories are formed in the reverse direction of the Jacobsthal tree. It is shown that unlike the classical Collatz problem, in which the Collatz sequence for a finite number of iterations leads to the unit element, for functions with factors 3 and 5, the Collatz sequence for a finite number of iterations does not reach the unit element. An analytical model is proposed that relates the iteration number of doubling (or halving the number in the reverse direction) number between two odd-numbered branch nodes. It is shown that for an arbitr

Uses Mathlib (`ℚ`, `omega`, positivity-style facts via Core).
Status: `mainStatement` records the paper claim; only named lemmas are proved.
Source: https://arxiv.org/abs/2306.14635
-/

namespace MathlibAttack.Papers.Arxiv2306_14635

open MathlibAttack.Papers

def citation : String := "Petro Kosobutskyy, \"The Collatz problem (a*q+-1,a=1,3,5,...) from the point of view of transformations of Jacobsthal numbers\", arXiv:2306.14635 [2023]."

/-- Recorded claim shell (generalization); paper theorem not proved.
Placeholder equals the Collatz conjecture proposition. -/
def mainStatement : Prop := CollatzConjecture

theorem step_one_eq : step 1 = 4 := step_one
theorem step_two_eq : step 2 = 1 := step_two

end MathlibAttack.Papers.Arxiv2306_14635
