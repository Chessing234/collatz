import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Ewa Graczyńska, "A solution of $3x+1$ problem", arXiv:1710.04503 [2017].

Title: A solution of $3x+1$ problem

Abstract (from OpenAlex metadata, truncated):
We present a solution of $3x+1$ problem. For a history of this problem we refer the reader to Lagarias, Jeffrey C.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/1710.04503
-/

namespace Collatz.Papers.Arxiv1710_04503

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Ewa Graczy\u0144ska, \"A solution of $3x+1$ problem\", arXiv:1710.04503 [2017]."

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

end Collatz.Papers.Arxiv1710_04503
