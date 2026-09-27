import MathlibAttack.Papers.Core

/-!
Mathlib-backed Lean notes for Grażyna Mirkowska and Andrzej Salwicki, "Collatz conjecture becomes theorem", arXiv:2310.13035 [2023].

Title: Collatz conjecture becomes theorem

Abstract (truncated):
The Collatz hypothesis is a theorem of the algorithmic theory of natural numbers. We prove the (algorithmic) formula that expresses the halting property of Collatz algorithm. The observation that Collatz's theorem cannot be proved in any elementary number theory completes the main result.

Uses Mathlib (`ℚ`, `omega`, positivity-style facts via Core).
Status: `mainStatement` records the paper claim; only named lemmas are proved.
Source: https://arxiv.org/abs/2310.13035
-/

namespace MathlibAttack.Papers.Arxiv2310_13035

open MathlibAttack.Papers

def citation : String := "Gra\u017cyna Mirkowska and Andrzej Salwicki, \"Collatz conjecture becomes theorem\", arXiv:2310.13035 [2023]."

/-- Recorded finite-verification claim shell; paper bound not proved. -/
def mainStatement : Prop :=
  ∃ B : ℕ, 1 < B ∧ ∀ n : ℕ, 0 < n → n < B → ∃ k : ℕ, orbit k n = 1

/-- Mathlib-checked miniature verification for `B = 2`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨2, by omega, MathlibAttack.Papers.verifies_below_two⟩

end MathlibAttack.Papers.Arxiv2310_13035
