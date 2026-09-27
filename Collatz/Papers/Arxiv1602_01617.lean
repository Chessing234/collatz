import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Maya Mohsin Ahmed, "The intricate labyrinth of Collatz sequences", arXiv:1602.01617 [2016].

Title: The intricate labyrinth of Collatz sequences

Abstract (from OpenAlex metadata, truncated):
In a previous article, we reduced the unsolved problem of the convergence of Collatz sequences, to convergence of Collatz sequences of odd numbers, that are divisible by 3. In this article, we further reduce this set to odd numbers that are congruent to 21 mod 24. We also show that either the Collatz sequence of a given odd number or an equivalent Collatz sequence reverses to a multiple of 3. Moreover, we construct a network composed of Collatz sequences of all odd numbers.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/1602.01617
-/

namespace Collatz.Papers.Arxiv1602_01617

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Maya Mohsin Ahmed, \"The intricate labyrinth of Collatz sequences\", arXiv:1602.01617 [2016]."

/-- Recorded claim shell (structural); the paper's theorem is not proved.
Placeholder equals the standard Collatz conjecture proposition. -/
def mainStatement : Prop := Collatz.CollatzConjecture

/-- Checked bridge facts only. -/
theorem step_one_eq : Collatz.step 1 = 4 := Collatz.step_one

theorem step_two_eq : Collatz.step 2 = 1 := Collatz.step_two

/-- Checked: every power of two reaches `1` (Mathlib-copied parity/division facts). -/
theorem powers_of_two_reach_one (k : Nat) :
    ∃ t : Nat, Collatz.orbit t (2 ^ k) = 1 :=
  Collatz.Papers.MathlibCopied.orbit_pow_two_reaches_one k

end Collatz.Papers.Arxiv1602_01617
