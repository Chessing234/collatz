import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Aristides V. Doumas and Vassilis G. Papanicolaou, "A Randomized Version of the Collatz $3x + 1$ Problem", arXiv:1503.03658 [2015].

Title: A Randomized Version of the Collatz $3x + 1$ Problem

Abstract (from OpenAlex metadata, truncated):
We propose a stochastic version of the Collatz $3x + 1$ Problem.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/1503.03658
-/

namespace Collatz.Papers.Arxiv1503_03658

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Aristides V. Doumas and Vassilis G. Papanicolaou, \"A Randomized Version of the Collatz $3x + 1$ Problem\", arXiv:1503.03658 [2015]."

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

end Collatz.Papers.Arxiv1503_03658
