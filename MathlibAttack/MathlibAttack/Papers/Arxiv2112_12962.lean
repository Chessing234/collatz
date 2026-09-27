import MathlibAttack.Papers.Core

/-!
Mathlib-backed Lean notes for Daohang Sha, "Minimum Steps to reach to a Smaller Number in 3n+1/Collatz Process", arXiv:2112.12962 [2021].

Title: Minimum Steps to reach to a Smaller Number in 3n+1/Collatz Process

Abstract (truncated):
We analyze the stopping-time and cycle structure of the normalized Collatz iteration. Using a recursive description of admissible binary sequences, we show that every integer $m \equiv 3 \pmod{4}$ arises uniquely and derive new bounds for the associated stopping and cycle numbers. These bounds imply that $F_{q}(m)/m \to 1$ as the sequence length increases, while equality is impossible for any finite sequence. Consequently, no finite nontrivial cycle is compatible with the iteration, and the trivial cycle at $1$ is the only admissible periodic orbit.

Uses Mathlib (`ℚ`, `omega`, positivity-style facts via Core).
Status: `mainStatement` records the paper claim; only named lemmas are proved.
Source: https://arxiv.org/abs/2112.12962
-/

namespace MathlibAttack.Papers.Arxiv2112_12962

open MathlibAttack.Papers

def citation : String := "Daohang Sha, \"Minimum Steps to reach to a Smaller Number in 3n+1/Collatz Process\", arXiv:2112.12962 [2021]."

/-- Recorded cycle-exclusion shell (paper theorem not proved). -/
def mainStatement : Prop :=
  ∀ n : ℕ, 1 < n → ∀ k : ℕ, 0 < k → orbit k n = n →
    ∃ j : ℕ, j ≤ k ∧ orbit j n = 1

/-- Checked: the trivial 1-cycle returns. -/
theorem orbit_one_cycle : orbit 3 1 = 1 :=
  MathlibAttack.Papers.orbit_one_returns

end MathlibAttack.Papers.Arxiv2112_12962
