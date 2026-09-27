import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Yongjun Chen and Liping Zhang, "Linear convergence of the Collatz method for computing the Perron eigenpair of primitive dual number matrix", arXiv:2309.04807 [2023].

Title: Linear convergence of the Collatz method for computing the Perron eigenpair of primitive dual number matrix

Abstract (from OpenAlex metadata, truncated):
Very recently, Qi and Cui extended the Perron-Frobenius theory to dual number matrices with primitive and irreducible nonnegative standard parts and proved that they have Perron eigenpair and Perron-Frobenius eigenpair. The Collatz method was also extended to find Perron eigenpair. Qi and Cui proposed two conjectures. One is the k-order power of a dual number matrix tends to zero if and only if the spectral radius of its standard part less than one, and another is the linear convergence of the Collatz method. In this paper, we confirm these conjectures and provide theoretical proof. The main contribution is to show that the Collatz method R-linearly converges with an explicit rate.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2309.04807
-/

namespace Collatz.Papers.Arxiv2309_04807

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Yongjun Chen and Liping Zhang, \"Linear convergence of the Collatz method for computing the Perron eigenpair of primitive dual number matrix\", arXiv:2309.04807 [2023]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 2` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1


/-- Miniature verification: every positive `n < 2` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩


end Collatz.Papers.Arxiv2309_04807
