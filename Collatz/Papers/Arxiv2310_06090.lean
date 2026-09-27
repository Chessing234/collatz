import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Kerry M. Soileau, "A Necessary Condition on the Collatz Conjecture", arXiv:2310.06090 [2023].

Title: A Necessary Condition on the Collatz Conjecture

Abstract (from OpenAlex metadata, truncated):
The Collatz conjecture implies that an iterated function sequence under a certain linear operator, beginning with a certain complex valued function, must converge to a certain complex function.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2310.06090
-/

namespace Collatz.Papers.Arxiv2310_06090

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Kerry M. Soileau, \"A Necessary Condition on the Collatz Conjecture\", arXiv:2310.06090 [2023]."

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

end Collatz.Papers.Arxiv2310_06090
