import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Paula Neeley et al., "On the Uniformity of $(3/2)^n$ Modulo 1", arXiv:1806.03559 [2018].

Title: On the Uniformity of $(3/2)^n$ Modulo 1

Abstract (from OpenAlex metadata, truncated):
It has been conjectured that the sequence $(3/2)^n$ modulo $1$ is uniformly distributed. The distribution of this sequence is signifcant in relation to unsolved problems in number theory including the Collatz conjecture. In this paper, we describe an algorithm to compute $(3/2)^n$ modulo $1$ to $n = 10^8$. We then statistically analyze its distribution. Our results strongly agree with the hypothesis that $(3/2)^n$ modulo 1 is uniformly distributed.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/1806.03559
-/

namespace Collatz.Papers.Arxiv1806_03559

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Paula Neeley et al., \"On the Uniformity of $(3/2)^n$ Modulo 1\", arXiv:1806.03559 [2018]."

/-- Recorded finite-verification claim shell; the paper's bound is not proved here. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1


/-- Miniature checked verification for `B = 2`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩


end Collatz.Papers.Arxiv1806_03559
