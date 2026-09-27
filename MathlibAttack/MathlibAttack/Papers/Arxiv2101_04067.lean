import MathlibAttack.Papers.Core

/-!
Mathlib-backed Lean notes for Darrell Cox et al., "Collatz Cycles and $3n+c$ Cycles", arXiv:2101.04067 [2021].

Title: Collatz Cycles and $3n+c$ Cycles

Abstract (truncated):
Halbeisen and Hungerbuhler determined optimal bounds for the length of rational Collatz cycles. Their methods are extended to $3n+c$ cycles. Another sequence having properties similar to those of Riemann zeta function zeros is introduced.

Uses Mathlib (`ℚ`, `omega`, positivity-style facts via Core).
Status: `mainStatement` records the paper claim; only named lemmas are proved.
Source: https://arxiv.org/abs/2101.04067
-/

namespace MathlibAttack.Papers.Arxiv2101_04067

open MathlibAttack.Papers

def citation : String := "Darrell Cox et al., \"Collatz Cycles and $3n+c$ Cycles\", arXiv:2101.04067 [2021]."

/-- Recorded cycle-exclusion shell (paper theorem not proved). -/
def mainStatement : Prop :=
  ∀ n : ℕ, 1 < n → ∀ k : ℕ, 0 < k → orbit k n = n →
    ∃ j : ℕ, j ≤ k ∧ orbit j n = 1

/-- Checked: the trivial 1-cycle returns. -/
theorem orbit_one_cycle : orbit 3 1 = 1 :=
  MathlibAttack.Papers.orbit_one_returns

end MathlibAttack.Papers.Arxiv2101_04067
