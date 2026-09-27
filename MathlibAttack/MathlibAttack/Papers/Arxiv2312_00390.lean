import MathlibAttack.Papers.Core

/-!
Mathlib-backed Lean notes for Angelot Behajaina and Elad Paran, "The Collatz map analogue in polynomial rings and in completions", arXiv:2312.00390 [2023].

Title: The Collatz map analogue in polynomial rings and in completions

Abstract (truncated):
We study an analogue of the Collatz map in the polynomial ring $R[x]$, where $R$ is an arbitrary commutative ring. We prove that if $R$ is of positive characteristic, then every polynomial in $R[x]$ is eventually periodic with respect to this map. This extends previous works of the authors and of Hicks, Mullen, Yucas and Zavislak, who studied the Collatz map on $\mathbb{F}_p[x]$ and $\mathbb{F}_2[x]$, respectively. We also consider the Collatz map on the ring of formal power series $R[[x]]$ when $R$ is finite: we characterize the eventually periodic series in this ring, and give formulas for the number of cycles induced by the Collatz map, of any given length. We provide similar formulas for the original Collatz map defined on the ring $\mathbb{Z}_2$ of $2$-adic integers, extending previous results of Lagarias.

Uses Mathlib (`ℚ`, `omega`, positivity-style facts via Core).
Status: `mainStatement` records the paper claim; only named lemmas are proved.
Source: https://arxiv.org/abs/2312.00390
-/

namespace MathlibAttack.Papers.Arxiv2312_00390

open MathlibAttack.Papers

def citation : String := "Angelot Behajaina and Elad Paran, \"The Collatz map analogue in polynomial rings and in completions\", arXiv:2312.00390 [2023]."

/-- Recorded cycle-exclusion shell (paper theorem not proved). -/
def mainStatement : Prop :=
  ∀ n : ℕ, 1 < n → ∀ k : ℕ, 0 < k → orbit k n = n →
    ∃ j : ℕ, j ≤ k ∧ orbit j n = 1

/-- Checked: the trivial 1-cycle returns. -/
theorem orbit_one_cycle : orbit 3 1 = 1 :=
  MathlibAttack.Papers.orbit_one_returns

end MathlibAttack.Papers.Arxiv2312_00390
