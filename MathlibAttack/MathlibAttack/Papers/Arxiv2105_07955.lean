import MathlibAttack.Papers.Core

/-!
Mathlib-backed Lean notes for Fabian S. Reid, "The Visual Pattern in the Collatz Conjecture and Proof of No Non-Trivial Cycles", arXiv:2105.07955 [2021].

Title: The Visual Pattern in the Collatz Conjecture and Proof of No Non-Trivial Cycles

Abstract (truncated):
We present the long sought visual pattern in the Collatz problem with the aid of a logarithmic spiral. Using this newly discovered pattern, we show that the Collatz problem is linked to primes via Jacobsthal numbers. We then prove that no non-trivial cycles exist on the spiral and by extension in the Collatz problem.

Uses Mathlib (`ℚ`, `omega`, positivity-style facts via Core).
Status: `mainStatement` records the paper claim; only named lemmas are proved.
Source: https://arxiv.org/abs/2105.07955
-/

namespace MathlibAttack.Papers.Arxiv2105_07955

open MathlibAttack.Papers

def citation : String := "Fabian S. Reid, \"The Visual Pattern in the Collatz Conjecture and Proof of No Non-Trivial Cycles\", arXiv:2105.07955 [2021]."

/-- Recorded cycle-exclusion shell (paper theorem not proved). -/
def mainStatement : Prop :=
  ∀ n : ℕ, 1 < n → ∀ k : ℕ, 0 < k → orbit k n = n →
    ∃ j : ℕ, j ≤ k ∧ orbit j n = 1

/-- Checked: the trivial 1-cycle returns. -/
theorem orbit_one_cycle : orbit 3 1 = 1 :=
  MathlibAttack.Papers.orbit_one_returns

end MathlibAttack.Papers.Arxiv2105_07955
