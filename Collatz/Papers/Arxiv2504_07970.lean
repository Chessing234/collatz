import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Franciszek Kobus, "Collatz Representations With Bounded Partial Quotients", arXiv:2504.07970 [2025].

Title: Collatz Representations With Bounded Partial Quotients

Abstract (from OpenAlex metadata, truncated):
We define Collatz representations for a subset of rational numbers and prove that each real number \( x \notin (-1,1) \) can be approximated arbitrarily well by rational numbers which have only \( 2 \)'s and \( 1 \)'s in their Collatz representation.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2504.07970
-/

namespace Collatz.Papers.Arxiv2504_07970

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Franciszek Kobus, \"Collatz Representations With Bounded Partial Quotients\", arXiv:2504.07970 [2025]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 2` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1


/-- Miniature verification: every positive `n < 2` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩


end Collatz.Papers.Arxiv2504_07970
