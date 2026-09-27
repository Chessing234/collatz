import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Fabrizio Luccio, "Some considerations on Collatz conjecture", arXiv:2007.02031 [2020].

Title: Some considerations on Collatz conjecture

Abstract (from OpenAlex metadata, truncated):
Some simple facts are proved ruling the Collatz tree and the chains of vertices appearing in it, leading to the reduction of the number of significant elements appearing in the tree. Although the Collatz conjecture remains open, these fact may cast some light on the nature of the problem.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2007.02031
-/

namespace Collatz.Papers.Arxiv2007_02031

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Fabrizio Luccio, \"Some considerations on Collatz conjecture\", arXiv:2007.02031 [2020]."

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

end Collatz.Papers.Arxiv2007_02031
