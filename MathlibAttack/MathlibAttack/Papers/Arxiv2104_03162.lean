import MathlibAttack.Papers.Core

/-!
Mathlib-backed Lean notes for Raouf Rajab, "The fundamental properties characterizing the structural behaviors of Collatz sequences", arXiv:2104.03162 [2021].

Title: The fundamental properties characterizing the structural behaviors of Collatz sequences

Abstract (truncated):
This work represents an in-depth study of the structural behavior of the Collatz sequences. We consider a finite arithmetic progression with a common difference is 2 and the number of terms in the sequence is equal to 2^n . After, we consider a 2^n x(n+1) matrix ((n+1) columns and 2^n rows) such as the first column contains the terms of arithmetic progression and each row of the matrix represent a finite Collatz sequence. Then, each element of the matrix will be replaced by 0 or 1 according to the following rule: the even integer is replaced by 0 and the odd integer is replaced by 1. We obtained a table contains all binary permutation with repetition this property is called the property of structural complementarily. Based on these tables, we can determine any other fundamentals properties characterizing the behavior of Collatz sequences. Thus, we can distinguish two other important prop

Uses Mathlib (`ℚ`, `omega`, positivity-style facts via Core).
Status: `mainStatement` records the paper claim; only named lemmas are proved.
Source: https://arxiv.org/abs/2104.03162
-/

namespace MathlibAttack.Papers.Arxiv2104_03162

open MathlibAttack.Papers

def citation : String := "Raouf Rajab, \"The fundamental properties characterizing the structural behaviors of Collatz sequences\", arXiv:2104.03162 [2021]."

/-- Recorded cycle-exclusion shell (paper theorem not proved). -/
def mainStatement : Prop :=
  ∀ n : ℕ, 1 < n → ∀ k : ℕ, 0 < k → orbit k n = n →
    ∃ j : ℕ, j ≤ k ∧ orbit j n = 1

/-- Checked: the trivial 1-cycle returns. -/
theorem orbit_one_cycle : orbit 3 1 = 1 :=
  MathlibAttack.Papers.orbit_one_returns

end MathlibAttack.Papers.Arxiv2104_03162
