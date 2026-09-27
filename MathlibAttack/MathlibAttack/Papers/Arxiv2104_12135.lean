import MathlibAttack.Papers.Core

/-!
Mathlib-backed Lean notes for Hassan Rezai Soleymanpour, "A Proof of Collatz Conjecture Based on a New Tree Topology", arXiv:2104.12135 [2021].

Title: A Proof of Collatz Conjecture Based on a New Tree Topology

Abstract (truncated):
Consider a finite positive integer. If it is even, divide it by 2, and if it is odd, multiply it by 3 and add 1. This will give you a new integer. Following the procedure for the new integer, you will receive another integer. Repeat the steps, and after a few repetitions, you will finally reach 1. Collatz conjecture states that the final integer in the mentioned process will always be 1, no matter what integer it starts with. Although the procedure of the conjecture is easy to describe, its correctness has not yet been confirmed. This article proves the conjecture by introducing a tree topology of it. Given the proposed tree, we can prove that all integers are uniquely distributed on the tree, and there is no cycle other than 1-2-1. We also see how every trajectory ends in 1.

Uses Mathlib (`ℚ`, `omega`, positivity-style facts via Core).
Status: `mainStatement` records the paper claim; only named lemmas are proved.
Source: https://arxiv.org/abs/2104.12135
-/

namespace MathlibAttack.Papers.Arxiv2104_12135

open MathlibAttack.Papers

def citation : String := "Hassan Rezai Soleymanpour, \"A Proof of Collatz Conjecture Based on a New Tree Topology\", arXiv:2104.12135 [2021]."

/-- Recorded cycle-exclusion shell (paper theorem not proved). -/
def mainStatement : Prop :=
  ∀ n : ℕ, 1 < n → ∀ k : ℕ, 0 < k → orbit k n = n →
    ∃ j : ℕ, j ≤ k ∧ orbit j n = 1

/-- Checked: the trivial 1-cycle returns. -/
theorem orbit_one_cycle : orbit 3 1 = 1 :=
  MathlibAttack.Papers.orbit_one_returns

end MathlibAttack.Papers.Arxiv2104_12135
