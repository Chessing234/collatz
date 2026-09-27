import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Sitan Chen, "Cellular Automata to More Efficiently Compute the Collatz Map", arXiv:1301.3125 [2013].

Title: Cellular Automata to More Efficiently Compute the Collatz Map

Abstract (from OpenAlex metadata, truncated):
The Collatz, or 3x+1, Conjecture claims that for every positive integer n, there exists some k such that T^k(n)=1, where T is the Collatz map. We present three cellular automata (CA) that transform the global problem of mimicking the Collatz map in bases 2, 3, and 4 into a local one of transforming the digits of iterates. The CAs streamline computation first by bypassing calculation of certain parts of trajectories: the binary CA bypasses division by two altogether. In addition, they allow for multiple trajectories to be calculated simultaneously, representing both a significant improvement upon existing sequential methods of computing the Collatz map and a demonstration of the efficacy of using a massively parallel approach with cellular automata to tackle iterative problems like the Collatz Conjecture.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/1301.3125
-/

namespace Collatz.Papers.Arxiv1301_3125

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Sitan Chen, \"Cellular Automata to More Efficiently Compute the Collatz Map\", arXiv:1301.3125 [2013]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Arxiv1301_3125
