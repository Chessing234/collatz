import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Maya Mohsin Ahmed, "A window to the Convergence of a Collatz Sequence", arXiv:1510.01274 [2015].

Title: A window to the Convergence of a Collatz Sequence

Abstract (from OpenAlex metadata, truncated):
In this article, we reduce the unsolved problem of convergence of Collatz sequences to convergence of Collatz sequences of odd numbers that are divisible by 3. We give an elementary proof of the fact that a Collatz sequence does not increase monotonically. We define a unique reverse Collatz sequence and conjecture that this sequence always converges to a multiple of $3$.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/1510.01274
-/

namespace Collatz.Papers.Arxiv1510_01274

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Maya Mohsin Ahmed, \"A window to the Convergence of a Collatz Sequence\", arXiv:1510.01274 [2015]."

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

end Collatz.Papers.Arxiv1510_01274
