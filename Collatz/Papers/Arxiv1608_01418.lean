import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Gerardo Costa and A. C. Souza Filho, "Collatz Numbers", arXiv:1608.01418 [2016].

Title: Collatz Numbers

Abstract (from OpenAlex metadata, truncated):
In this article we present set of infinite natural numbers which satisfies the conjecture $3n+1$.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/1608.01418
-/

namespace Collatz.Papers.Arxiv1608_01418

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Gerardo Costa and A. C. Souza Filho, \"Collatz Numbers\", arXiv:1608.01418 [2016]."

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

end Collatz.Papers.Arxiv1608_01418
