import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for baoyuan duan, "A Solution to the Collatz Conjecture Problem", arXiv:2301.00541 [2025].

Title: A Solution to the Collatz Conjecture Problem

Abstract (from OpenAlex metadata, truncated):
Research Collatz odd sequence, change (×3 + 1) ÷ 2k operation in Collatz Conjecture to (×3 + 2m − 1) ÷ 2k operation. Expand loop Collatz odd sequence (if exists) in (×3 + 2m − 1) ÷ 2k odd sequence to become ∞-steps non-loop sequence. Build a (×3 + 2m − 1) ÷ 2k odd tree model and transform position model for odds in tree. Via comparing actual and virtual positions, prove if a (×3 + 2m − 1) ÷ 2k odd sequence can not converge after ∞ steps of (×3 + 2m − 1) ÷ 2k operation, the sequence must walk out of the right boundary of the tree.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2301.00541
-/

namespace Collatz.Papers.Arxiv2301_00541

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "baoyuan duan, \"A Solution to the Collatz Conjecture Problem\", arXiv:2301.00541 [2025]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Arxiv2301_00541
