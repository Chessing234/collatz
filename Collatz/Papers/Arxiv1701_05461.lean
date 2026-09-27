import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Denver Stahl, "The Convergence Properties of Mersenne Variations of the Collatz Function", arXiv:1701.05461 [2017].

Title: The Convergence Properties of Mersenne Variations of the Collatz Function

Abstract (from OpenAlex metadata, truncated):


Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/1701.05461
-/

namespace Collatz.Papers.Arxiv1701_05461

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Denver Stahl, \"The Convergence Properties of Mersenne Variations of the Collatz Function\", arXiv:1701.05461 [2017]."

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

end Collatz.Papers.Arxiv1701_05461
