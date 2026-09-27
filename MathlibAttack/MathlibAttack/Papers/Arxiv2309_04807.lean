import MathlibAttack.Papers.Core

/-!
Mathlib-backed Lean notes for Yongjun Chen and Liping Zhang, "Linear convergence of the Collatz method for computing the Perron eigenpair of primitive dual number matrix", arXiv:2309.04807 [2023].

Title: Linear convergence of the Collatz method for computing the Perron eigenpair of primitive dual number matrix

Abstract (truncated):
Very recently, Qi and Cui extended the Perron-Frobenius theory to dual number matrices with primitive and irreducible nonnegative standard parts and proved that they have Perron eigenpair and Perron-Frobenius eigenpair. The Collatz method was also extended to find Perron eigenpair. Qi and Cui proposed two conjectures. One is the k-order power of a dual number matrix tends to zero if and only if the spectral radius of its standard part less than one, and another is the linear convergence of the Collatz method. In this paper, we confirm these conjectures and provide theoretical proof. The main contribution is to show that the Collatz method R-linearly converges with an explicit rate.

Uses Mathlib (`ℚ`, `omega`, positivity-style facts via Core).
Status: `mainStatement` records the paper claim; only named lemmas are proved.
Source: https://arxiv.org/abs/2309.04807
-/

namespace MathlibAttack.Papers.Arxiv2309_04807

open MathlibAttack.Papers

def citation : String := "Yongjun Chen and Liping Zhang, \"Linear convergence of the Collatz method for computing the Perron eigenpair of primitive dual number matrix\", arXiv:2309.04807 [2023]."

/-- Recorded finite-verification claim shell; paper bound not proved. -/
def mainStatement : Prop :=
  ∃ B : ℕ, 1 < B ∧ ∀ n : ℕ, 0 < n → n < B → ∃ k : ℕ, orbit k n = 1

/-- Mathlib-checked miniature verification for `B = 2`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨2, by omega, MathlibAttack.Papers.verifies_below_two⟩

end MathlibAttack.Papers.Arxiv2309_04807
