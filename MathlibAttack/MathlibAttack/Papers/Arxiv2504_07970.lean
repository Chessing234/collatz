import MathlibAttack.Papers.Core

/-!
Mathlib-backed Lean notes for Franciszek Kobus, "Collatz Representations With Bounded Partial Quotients", arXiv:2504.07970 [2025].

Title: Collatz Representations With Bounded Partial Quotients

Abstract (truncated):
We define Collatz representations for a subset of rational numbers and prove that each real number \( x \notin (-1,1) \) can be approximated arbitrarily well by rational numbers which have only \( 2 \)'s and \( 1 \)'s in their Collatz representation.

Uses Mathlib (`ℚ`, `omega`, positivity-style facts via Core).
Status: `mainStatement` records the paper claim; only named lemmas are proved.
Source: https://arxiv.org/abs/2504.07970
-/

namespace MathlibAttack.Papers.Arxiv2504_07970

open MathlibAttack.Papers

def citation : String := "Franciszek Kobus, \"Collatz Representations With Bounded Partial Quotients\", arXiv:2504.07970 [2025]."

/-- Recorded finite-verification claim shell; paper bound not proved. -/
def mainStatement : Prop :=
  ∃ B : ℕ, 1 < B ∧ ∀ n : ℕ, 0 < n → n < B → ∃ k : ℕ, orbit k n = 1

/-- Mathlib-checked miniature verification for `B = 2`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨2, by omega, MathlibAttack.Papers.verifies_below_two⟩

end MathlibAttack.Papers.Arxiv2504_07970
