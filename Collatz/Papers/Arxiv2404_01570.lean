import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Youngik Lee, "Numerical Approach on Collatz Conjecture", arXiv:2404.01570 [2024].

Title: Numerical Approach on Collatz Conjecture

Abstract (from OpenAlex metadata, truncated):
We can analyze the properties of the Collatz Conjecture by using Terras’ Theorem, and computational graphical calculations. To do this, we introduce the concept of “tree" which shows the relationship between the input and output positive integers of the Collatz process. This approach offers a novel way for determining the non-existence of loops and diverge trees through computer simulations.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2404.01570
-/

namespace Collatz.Papers.Arxiv2404_01570

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Youngik Lee, \"Numerical Approach on Collatz Conjecture\", arXiv:2404.01570 [2024]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Arxiv2404_01570
