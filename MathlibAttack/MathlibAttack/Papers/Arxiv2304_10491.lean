import MathlibAttack.Papers.Core

/-!
Mathlib-backed Lean notes for Wei Ren, "Reduced Collatz Dynamics is Periodical and the Period Equals 2 to the Power of the Count of x/2", arXiv:2304.10491 [2023].

Title: Reduced Collatz Dynamics is Periodical and the Period Equals 2 to the Power of the Count of x/2

Abstract (truncated):
In this paper, we prove that reduced dynamics on Collatz conjecture is periodical, and its period equals 2 to the power of the count of x/2 computation in the reduced dynamics. More specifically, if there exists reduced dynamics of x (that is, start from an integer x and the computation will go to an integer less than x), then there must also exist reduced dynamics of x+P (that is, if starting from an integer x+P, then computation will go to an integer less than x+P), where P equals 2 to the power of L, and L is the total count of x/2 computations (i.e., computational times) in the reduced dynamics of x (note that, equivalently, L is also the length of the reduced dynamics of x). Therefore, the power (or output) of this period property, which is discovered and proved in this paper, is - the study of the existence of reduced dynamics of x will result in the existence of reduced dynamics o

Uses Mathlib (`ℚ`, `omega`, positivity-style facts via Core).
Status: `mainStatement` records the paper claim; only named lemmas are proved.
Source: https://arxiv.org/abs/2304.10491
-/

namespace MathlibAttack.Papers.Arxiv2304_10491

open MathlibAttack.Papers

def citation : String := "Wei Ren, \"Reduced Collatz Dynamics is Periodical and the Period Equals 2 to the Power of the Count of x/2\", arXiv:2304.10491 [2023]."

/-- Recorded cycle-exclusion shell (paper theorem not proved). -/
def mainStatement : Prop :=
  ∀ n : ℕ, 1 < n → ∀ k : ℕ, 0 < k → orbit k n = n →
    ∃ j : ℕ, j ≤ k ∧ orbit j n = 1

/-- Checked: the trivial 1-cycle returns. -/
theorem orbit_one_cycle : orbit 3 1 = 1 :=
  MathlibAttack.Papers.orbit_one_returns

end MathlibAttack.Papers.Arxiv2304_10491
