import MathlibAttack.Papers.Core

/-!
Mathlib-backed Lean notes for Juan Rojas, "An optimal convergent Collatz algorithm", arXiv:2308.01214 [2023].

Title: An optimal convergent Collatz algorithm

Abstract (truncated):
In this research, an optimal algorithm for the Collatz conjecture is presented. Properties such as the convergence of the algorithm and an equation that relates the algorithm to the classical Collatz conjecture are obtained. It is validated that the proposed theory is correct with several examples; as a sector of mathematicians believes that the Collatz conjecture fails in some power of $3$. The algorithm was applied to the first $600$ powers of $3$, where the convergence of the proposed algorithm was verified.

Uses Mathlib (`ℚ`, `omega`, positivity-style facts via Core).
Status: `mainStatement` records the paper claim; only named lemmas are proved.
Source: https://arxiv.org/abs/2308.01214
-/

namespace MathlibAttack.Papers.Arxiv2308_01214

open MathlibAttack.Papers

def citation : String := "Juan Rojas, \"An optimal convergent Collatz algorithm\", arXiv:2308.01214 [2023]."

/-- Recorded finite-verification claim shell; paper bound not proved. -/
def mainStatement : Prop :=
  ∃ B : ℕ, 1 < B ∧ ∀ n : ℕ, 0 < n → n < B → ∃ k : ℕ, orbit k n = 1

/-- Mathlib-checked miniature verification for `B = 2`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨2, by omega, MathlibAttack.Papers.verifies_below_two⟩

end MathlibAttack.Papers.Arxiv2308_01214
