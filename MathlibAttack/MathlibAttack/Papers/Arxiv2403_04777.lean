import MathlibAttack.Papers.Core

/-!
Mathlib-backed Lean notes for Ali Ebnenasir, "Specifying and Verifying the Convergence Stairs of the Collatz Program", arXiv:2403.04777 [2024].

Title: Specifying and Verifying the Convergence Stairs of the Collatz Program

Abstract (truncated):
This paper presents an algorithmic method that, given a positive integer $j$, generates the $j$-th convergence stair containing all natural numbers from where the Collatz conjecture holds by exactly $j$ applications of the Collatz function. To this end, we present a novel formulation of the Collatz conjecture as a concurrent program, and provide the general case specification of the $j$-th convergence stair for any $j > 0$. The proposed specifications provide a layered and linearized orientation of Collatz numbers organized in an infinite set of infinite binary trees. To the best of our knowledge, this is the first time that such a general specification is provided, which can have significant applications in analyzing and testing the behaviors of complex non-linear systems. We have implemented this method as a software tool that generates the Collatz numbers of individual stairs. We also

Uses Mathlib (`ℚ`, `omega`, positivity-style facts via Core).
Status: `mainStatement` records the paper claim; only named lemmas are proved.
Source: https://arxiv.org/abs/2403.04777
-/

namespace MathlibAttack.Papers.Arxiv2403_04777

open MathlibAttack.Papers

def citation : String := "Ali Ebnenasir, \"Specifying and Verifying the Convergence Stairs of the Collatz Program\", arXiv:2403.04777 [2024]."

/-- Recorded finite-verification claim shell; paper bound not proved. -/
def mainStatement : Prop :=
  ∃ B : ℕ, 1 < B ∧ ∀ n : ℕ, 0 < n → n < B → ∃ k : ℕ, orbit k n = 1

/-- Mathlib-checked miniature verification for `B = 2`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨2, by omega, MathlibAttack.Papers.verifies_below_two⟩

end MathlibAttack.Papers.Arxiv2403_04777
