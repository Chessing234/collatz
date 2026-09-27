import MathlibAttack.Papers.Core

/-!
Mathlib-backed Lean notes for Yagub N. Aliyev, "On integer linear combinations of terms of rational cycles for the generalized 3x+1 problem", arXiv:2307.11990 [2023].

Title: On integer linear combinations of terms of rational cycles for the generalized 3x+1 problem

Abstract (truncated):
In the paper, some special linear combinations of the terms of rational cycles of generalized Collatz sequences are studied. It is proved that if the coefficients of the linear combinations satisfy some conditions then these linear combinations are integers. The discussed results are demonstrated on some examples. In some particular cases the obtained results can be used to explain some patterns of digits in $p$-adic representations of the terms of the rational cycles.

Uses Mathlib (`ℚ`, `omega`, positivity-style facts via Core).
Status: `mainStatement` records the paper claim; only named lemmas are proved.
Source: https://arxiv.org/abs/2307.11990
-/

namespace MathlibAttack.Papers.Arxiv2307_11990

open MathlibAttack.Papers

def citation : String := "Yagub N. Aliyev, \"On integer linear combinations of terms of rational cycles for the generalized 3x+1 problem\", arXiv:2307.11990 [2023]."

/-- Recorded cycle-exclusion shell (paper theorem not proved). -/
def mainStatement : Prop :=
  ∀ n : ℕ, 1 < n → ∀ k : ℕ, 0 < k → orbit k n = n →
    ∃ j : ℕ, j ≤ k ∧ orbit j n = 1

/-- Checked: the trivial 1-cycle returns. -/
theorem orbit_one_cycle : orbit 3 1 = 1 :=
  MathlibAttack.Papers.orbit_one_returns

end MathlibAttack.Papers.Arxiv2307_11990
