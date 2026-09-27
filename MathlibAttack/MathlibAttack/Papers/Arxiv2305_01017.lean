import MathlibAttack.Papers.Core

/-!
Mathlib-backed Lean notes for Shouvik Ahmed Antu et al., "An Exploration Into the Collatz Conjecture with Changed Parameters", arXiv:2305.01017 [2023].

Title: An Exploration Into the Collatz Conjecture with Changed Parameters

Abstract (truncated):
Exploring the Collatz Conjecture and changing the expression from 3n + 1 to 5n + 1, we found patterns in different sets of numbers. Some numbers reduce to one (as stated in the Collatz Conjecture), some might escape to infinity, and some get stuck in repeating cycles. To further explore the patterns involved in Collatz-like expressions, we changed the expression to 3n+5 and found connections between 3n+1 and 3n+5.

Uses Mathlib (`ℚ`, `omega`, positivity-style facts via Core).
Status: `mainStatement` records the paper claim; only named lemmas are proved.
Source: https://arxiv.org/abs/2305.01017
-/

namespace MathlibAttack.Papers.Arxiv2305_01017

open MathlibAttack.Papers

def citation : String := "Shouvik Ahmed Antu et al., \"An Exploration Into the Collatz Conjecture with Changed Parameters\", arXiv:2305.01017 [2023]."

/-- Recorded cycle-exclusion shell (paper theorem not proved). -/
def mainStatement : Prop :=
  ∀ n : ℕ, 1 < n → ∀ k : ℕ, 0 < k → orbit k n = n →
    ∃ j : ℕ, j ≤ k ∧ orbit j n = 1

/-- Checked: the trivial 1-cycle returns. -/
theorem orbit_one_cycle : orbit 3 1 = 1 :=
  MathlibAttack.Papers.orbit_one_returns

end MathlibAttack.Papers.Arxiv2305_01017
