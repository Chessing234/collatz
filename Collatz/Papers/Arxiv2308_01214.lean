import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Juan Rojas, "An optimal convergent Collatz algorithm", arXiv:2308.01214 [2023].

Title: An optimal convergent Collatz algorithm

Abstract (from OpenAlex metadata, truncated):
In this research, an optimal algorithm for the Collatz conjecture is presented. Properties such as the convergence of the algorithm and an equation that relates the algorithm to the classical Collatz conjecture are obtained. It is validated that the proposed theory is correct with several examples; as a sector of mathematicians believes that the Collatz conjecture fails in some power of $3$. The algorithm was applied to the first $600$ powers of $3$, where the convergence of the proposed algorithm was verified.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2308.01214
-/

namespace Collatz.Papers.Arxiv2308_01214

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Juan Rojas, \"An optimal convergent Collatz algorithm\", arXiv:2308.01214 [2023]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 2` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1


/-- Miniature verification: every positive `n < 2` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩


end Collatz.Papers.Arxiv2308_01214
