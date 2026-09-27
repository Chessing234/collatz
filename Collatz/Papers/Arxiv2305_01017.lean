import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Shouvik Ahmed Antu et al., "An Exploration Into the Collatz Conjecture with Changed Parameters", arXiv:2305.01017 [2023].

Title: An Exploration Into the Collatz Conjecture with Changed Parameters

Abstract (from OpenAlex metadata, truncated):
Exploring the Collatz Conjecture and changing the expression from 3n + 1 to 5n + 1, we found patterns in different sets of numbers. Some numbers reduce to one (as stated in the Collatz Conjecture), some might escape to infinity, and some get stuck in repeating cycles. To further explore the patterns involved in Collatz-like expressions, we changed the expression to 3n+5 and found connections between 3n+1 and 3n+5.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2305.01017
-/

namespace Collatz.Papers.Arxiv2305_01017

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Shouvik Ahmed Antu et al., \"An Exploration Into the Collatz Conjecture with Changed Parameters\", arXiv:2305.01017 [2023]."

/-- Recorded main claim shell (cycle); not proved.
States that any accelerated return to `n > 1` has already visited `1`. -/
def mainStatement : Prop :=
  ∀ n : Nat, n > 1 → ∀ k : Nat, 0 < k → Collatz.orbit k n = n →
    ∃ j : Nat, j ≤ k ∧ Collatz.orbit j n = 1

/-- Checked: the trivial 1-cycle returns to 1. -/
theorem orbit_one_returns : Collatz.orbit 3 1 = 1 :=
  (Collatz.Papers.MathlibCopied.trivial_cycle).1

theorem step_branches_on_cycle :
    Collatz.step 1 = 4 ∧ Collatz.step 4 = 2 ∧ Collatz.step 2 = 1 := by
  have h := Collatz.Papers.MathlibCopied.trivial_cycle
  exact ⟨h.2.1, h.2.2.1, h.2.2.2⟩


end Collatz.Papers.Arxiv2305_01017
