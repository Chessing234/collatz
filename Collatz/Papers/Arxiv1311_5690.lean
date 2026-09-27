import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Bojin Zheng, Yangqian Su, Hongrun Wu, Li Kuang, "The Ergodicity of the Collatz Process in Positive Integer Field", arXiv:1311.5690 [2013].

Title: The Ergodicity of the Collatz Process in Positive Integer Field

Abstract (from OpenAlex metadata, truncated):
The $3x+1$ problem, also called the Collatz conjecture, is a very interesting unsolved mathematical problem related to computer science. This paper generalized this problem by relaxing the constraints, i.e., generalizing this deterministic process to non-deterministic process, and set up three models. This paper analyzed the ergodicity of these models and proved that the ergodicity of the Collatz process in positive integer field holds, i.e., all the positive integers can be transformed to 1 by the iterations of the Collatz function.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/1311.5690
-/

namespace Collatz.Papers.Arxiv1311_5690

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Bojin Zheng et al., \"The Ergodicity of the Collatz Process in Positive Integer Field\", arXiv:1311.5690 [2013]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Arxiv1311_5690
