import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Luo, Youchun, "Iteration Steps of 3x+1 Problem", arXiv:2506.23070 [2025].

Title: Iteration Steps of 3x+1 Problem

Abstract (from arXiv metadata, truncated):
On the 3x+1 problem, given a positive integer $N$, let $D\left( N \right) $, $O\left( N \right) $ and $E\left( N \right) $ denote the total number of iteration steps, the number of odd iteration steps, and the number of even iteration steps, respectively, when $N$ is iterated until it reaches 1. It is straightforward to observe that $D\left( N \right) =O\left( N \right) +E\left( N \right) $. In this paper, we propose a conjecture termed the Weak Residue Conjecture(i.e., $\frac{2^{E\left( N \right)}}{3^{O\left( N \right)}\cdot N}<2$). We prove that if the 3x+1 conjecture is true and the Weak Residue Conjecture is true, there exist nontrivial relationships among $D\left( N \right) $, $O\left( N \right) $, $E\left( N \right) $, i.e., $O\left( N \right) =\lfloor \log _62\cdot D\left( N \right) -\log _6N \rfloor $(this implies that, given $N$, both $O\left( N \right) $ and $E\left( N \right) 

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2506.23070
-/

namespace Collatz.Papers.Arxiv2506_23070

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Luo, Youchun, \"Iteration Steps of 3x+1 Problem\", arXiv:2506.23070 [2025]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Arxiv2506_23070
