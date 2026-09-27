import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Eŝa Sakkinen, "Approaching the Collatz Theorem via Frontline Rules", arXiv:4210.24002 [2026].

Title: Approaching the Collatz Theorem via Frontline Rules

Abstract (from OpenAlex metadata, truncated):


Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/4210.24002
-/

namespace Collatz.Papers.Arxiv4210_24002

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "E\u015da Sakkinen, \"Approaching the Collatz Theorem via Frontline Rules\", arXiv:4210.24002 [2026]."

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

end Collatz.Papers.Arxiv4210_24002
