import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Petro Kosobutskyy, "The Collatz problem (a*q+-1,a=1,3,5,...) from the point of view of transformations of Jacobsthal numbers", arXiv:2306.14635 [2023].

Title: The Collatz problem (a*q+-1,a=1,3,5,...) from the point of view of transformations of Jacobsthal numbers

Abstract (from OpenAlex metadata, truncated):
In the paper, from the point of view of recurrent numbers of the Jacobsthal type, the Collatz problem with the general aq+-1 function of conjecture odd positive integers q from the set of natural numbers is investigated. Formulated branching rules from nodes with generalized Jacobsthal numbers of the so-called Jacobsthal tree. It is shown that Collatz trajectories are formed in the reverse direction of the Jacobsthal tree. It is shown that unlike the classical Collatz problem, in which the Collatz sequence for a finite number of iterations leads to the unit element, for functions with factors 3 and 5, the Collatz sequence for a finite number of iterations does not reach the unit element. An analytical model is proposed that relates the iteration number of doubling (or halving the number in the reverse direction) number between two odd-numbered branch nodes. It is shown that for an arbitrary number, Collatz and Jacobsthal trajectories develop in the respective directions, and the Jacobs

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2306.14635
-/

namespace Collatz.Papers.Arxiv2306_14635

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Petro Kosobutskyy, \"The Collatz problem (a*q+-1,a=1,3,5,...) from the point of view of transformations of Jacobsthal numbers\", arXiv:2306.14635 [2023]."

/-- Recorded main claim shell (generalization); the paper's theorem is not proved here.
This placeholder is the standard Collatz conjecture proposition. -/
def mainStatement : Prop := Collatz.CollatzConjecture

/-- Checked bridge facts only. -/
theorem step_one_eq : Collatz.step 1 = 4 := Collatz.step_one

theorem step_two_eq : Collatz.step 2 = 1 := Collatz.step_two

/-- Checked: every power of two reaches `1` (Mathlib-copied parity/division facts). -/
theorem powers_of_two_reach_one (k : Nat) :
    ∃ t : Nat, Collatz.orbit t (2 ^ k) = 1 :=
  Collatz.Papers.MathlibCopied.orbit_pow_two_reaches_one k

end Collatz.Papers.Arxiv2306_14635
