import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Mario DeFranco, "A Boolean polynomial operator for the Collatz $3n+1$ problem", arXiv:2608.25791 [2026].

Title: A Boolean polynomial operator for the Collatz $3n+1$ problem

Abstract (from OpenAlex metadata, truncated):
We define a reformulation of the Collatz $3n+1$ map which allows us to express it as an operator on the set of sequences of Boolean polynomials. We express this operator in terms of certain carry sequences that arise from addition in base-2, and then we simplify them and find explicit formulas for them.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2608.25791
-/

namespace Collatz.Papers.Arxiv2608_25791

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Mario DeFranco, \"A Boolean polynomial operator for the Collatz $3n+1$ problem\", arXiv:2608.25791 [2026]."

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

end Collatz.Papers.Arxiv2608_25791
