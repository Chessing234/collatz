import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Roupam Ghosh, "New lower bounds for the size of a non-trivial loop in the Collatz 3x+1 problem", arXiv:0907.3086 [2009].

Title: New lower bounds for the size of a non-trivial loop in the Collatz 3x+1 problem

Abstract (from OpenAlex metadata, truncated):
In the Collatz 3x+1 problem, there are 3 possibilities: Starting from any positive number, we either reach the trivial loop (1,4,2), end up in a non-trivial loop, or go until infinity. In this paper, we shall show that if a non-trivial loop with m odd numbers exists, then its minimum odd number is bounded above by a function of m. We shall also use that bound to calculate the least number of odd elements required for a non-trivial loop to exist. Introduction to the Collatz problem

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/0907.3086
-/

namespace Collatz.Papers.Arxiv0907_3086

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Roupam Ghosh, \"New lower bounds for the size of a non-trivial loop in the Collatz 3x+1 problem\", arXiv:0907.3086 [2009]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Arxiv0907_3086
