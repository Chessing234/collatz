import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Eyob Solomon Getachew and Beakal Gizachew Assefa, "Efficient Computation of Collatz Sequence Stopping Times: A Novel Algorithmic Approach", arXiv:2501.04032 [2025].

Title: Efficient Computation of Collatz Sequence Stopping Times: A Novel Algorithmic Approach

Abstract (from OpenAlex metadata, truncated):
The Collatz conjecture, which posits that any positive integer will eventually reach 1 through a specific iterative process, is a classic unsolved problem in mathematics. This research focuses on designing an efficient algorithm to compute the stopping time of numbers in the Collatz sequence, achieving significant computational improvements. By leveraging structural patterns in the Collatz tree, the proposed algorithm minimizes redundant operations and optimizes computational steps. Unlike prior methods, it efficiently handles extremely large numbers without requiring advanced techniques such as memoization or parallelization. Experimental evaluations confirm computational efficiency improvements of approximately 28% over state-of-the-art methods. These findings underscore the algorithm's scalability and robustness, providing a foundation for future large-scale verification of the conjecture and potential applications in computational mathematics.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2501.04032
-/

namespace Collatz.Papers.Arxiv2501_04032

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Eyob Solomon Getachew and Beakal Gizachew Assefa, \"Efficient Computation of Collatz Sequence Stopping Times: A Novel Algorithmic Approach\", arXiv:2501.04032 [2025]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 2` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1


/-- Miniature verification: every positive `n < 2` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩


end Collatz.Papers.Arxiv2501_04032
