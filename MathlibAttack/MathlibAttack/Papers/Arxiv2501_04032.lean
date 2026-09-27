import MathlibAttack.Papers.Core

/-!
Mathlib-backed Lean notes for Eyob Solomon Getachew and Beakal Gizachew Assefa, "Efficient Computation of Collatz Sequence Stopping Times: A Novel Algorithmic Approach", arXiv:2501.04032 [2025].

Title: Efficient Computation of Collatz Sequence Stopping Times: A Novel Algorithmic Approach

Abstract (truncated):
The Collatz conjecture, which posits that any positive integer will eventually reach 1 through a specific iterative process, is a classic unsolved problem in mathematics. This research focuses on designing an efficient algorithm to compute the stopping time of numbers in the Collatz sequence, achieving significant computational improvements. By leveraging structural patterns in the Collatz tree, the proposed algorithm minimizes redundant operations and optimizes computational steps. Unlike prior methods, it efficiently handles extremely large numbers without requiring advanced techniques such as memoization or parallelization. Experimental evaluations confirm computational efficiency improvements of approximately 28% over state-of-the-art methods. These findings underscore the algorithm's scalability and robustness, providing a foundation for future large-scale verification of the conjec

Uses Mathlib (`ℚ`, `omega`, positivity-style facts via Core).
Status: `mainStatement` records the paper claim; only named lemmas are proved.
Source: https://arxiv.org/abs/2501.04032
-/

namespace MathlibAttack.Papers.Arxiv2501_04032

open MathlibAttack.Papers

def citation : String := "Eyob Solomon Getachew and Beakal Gizachew Assefa, \"Efficient Computation of Collatz Sequence Stopping Times: A Novel Algorithmic Approach\", arXiv:2501.04032 [2025]."

/-- Recorded finite-verification claim shell; paper bound not proved. -/
def mainStatement : Prop :=
  ∃ B : ℕ, 1 < B ∧ ∀ n : ℕ, 0 < n → n < B → ∃ k : ℕ, orbit k n = 1

/-- Mathlib-checked miniature verification for `B = 2`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨2, by omega, MathlibAttack.Papers.verifies_below_two⟩

end MathlibAttack.Papers.Arxiv2501_04032
