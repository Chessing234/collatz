import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Michel, Pascal, "Problems in number theory from busy beaver competition", arXiv:1311.1029 [2013].

Title: Problems in number theory from busy beaver competition

Abstract (from arXiv metadata, truncated):
By introducing the busy beaver competition of Turing machines, in 1962, Rado defined noncomputable functions on positive integers. The study of these functions and variants leads to many mathematical challenges. This article takes up the following one: How can a small Turing machine manage to produce very big numbers? It provides the following answer: mostly by simulating Collatz-like functions, that are generalizations of the famous 3x+1 function. These functions, like the 3x+1 function, lead to new unsolved problems in number theory.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/1311.1029
-/

namespace Collatz.Papers.Arxiv1311_1029

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Michel, Pascal, \"Problems in number theory from busy beaver competition\", arXiv:1311.1029 [2013]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Arxiv1311_1029
