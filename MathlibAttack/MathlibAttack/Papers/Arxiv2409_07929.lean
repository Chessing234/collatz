import MathlibAttack.Papers.Core

/-!
Mathlib-backed Lean notes for Gaurav Goyal, "General Dynamics and Generation Mapping for Collatz-type Sequences", arXiv:2409.07929 [2024].

Title: General Dynamics and Generation Mapping for Collatz-type Sequences

Abstract (truncated):
Let an odd integer \(\mathcal{X}\) be expressed as $\left\{\sum\limits_{M > m}b_M2^M\right\}+2^m-1,$ where $b_M\in\{0,1\}$ and $2^m-1$ is referred to as the Governor. In Collatz-type functions, a high index Governor is eventually reduced to $2^1-1$. For the $3\mathcal{Z}+1$ sequence, the Governor occurring in the Trivial cycle is $2^1-1$, while for the $5\mathcal{Z}+1$ sequence, the Trivial Governors are $2^2-1$ and $2^1-1$. Therefore, in these specific sequences, the Collatz function reduces the Governor $2^m - 1$ to the Trivial Governor $2^{\mathcal{T}} - 1$. Once this Trivial Governor is reached, it can evolve to a higher index Governor through interactions with other terms. This feature allows $\mathcal{X}$ to reappear in a Collatz-type sequence, since $2^m - 1 = 2^{m - 1} + \cdots + 2^{\mathcal{T} + 1} + 2^{\mathcal{T}}+(2^{\mathcal{T}}-1).$ Thus, if $\mathcal{X}$ reappears, at leas

Uses Mathlib (`ℚ`, `omega`, positivity-style facts via Core).
Status: `mainStatement` records the paper claim; only named lemmas are proved.
Source: https://arxiv.org/abs/2409.07929
-/

namespace MathlibAttack.Papers.Arxiv2409_07929

open MathlibAttack.Papers

def citation : String := "Gaurav Goyal, \"General Dynamics and Generation Mapping for Collatz-type Sequences\", arXiv:2409.07929 [2024]."

/-- Recorded cycle-exclusion shell (paper theorem not proved). -/
def mainStatement : Prop :=
  ∀ n : ℕ, 1 < n → ∀ k : ℕ, 0 < k → orbit k n = n →
    ∃ j : ℕ, j ≤ k ∧ orbit j n = 1

/-- Checked: the trivial 1-cycle returns. -/
theorem orbit_one_cycle : orbit 3 1 = 1 :=
  MathlibAttack.Papers.orbit_one_returns

end MathlibAttack.Papers.Arxiv2409_07929
