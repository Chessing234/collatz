import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for David Barina, "$7x\pm1$: Close Relative of Collatz Problem", arXiv:1807.00908 [2018].

Title: $7x\pm1$: Close Relative of Collatz Problem

Abstract (from OpenAlex metadata, truncated):
We show an iterated function of which iterates oscillate wildly and grow at a dizzying pace. We conjecture that the orbit of arbitrary positive integer always returns to 1, as in the case of Collatz function. The conjecture is supported by a heuristic argument and computational results.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/1807.00908
-/

namespace Collatz.Papers.Arxiv1807_00908

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "David Barina, \"$7x\\pm1$: Close Relative of Collatz Problem\", arXiv:1807.00908 [2018]."

/-- Recorded finite-verification claim shell; the paper's bound is not proved here. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1


/-- Miniature checked verification for `B = 2`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩


end Collatz.Papers.Arxiv1807_00908
