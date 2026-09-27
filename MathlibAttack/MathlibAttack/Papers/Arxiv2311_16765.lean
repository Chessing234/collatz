import MathlibAttack.Papers.Core

/-!
Mathlib-backed Lean notes for J. Stöckl, "Observations towards a proof of the Collatz conjecture using $2^{j}k+x$ number series", arXiv:2311.16765 [2023].

Title: Observations towards a proof of the Collatz conjecture using $2^{j}k+x$ number series

Abstract (truncated):
The document tries to put focus on sequences with certain properties and periods leading to the first value smaller than the starting value in the Collatz problem. With the idea that, if all starting numbers lead ultimately to a smaller number, all full sequences lead to 1 with a finite stopping time, the problem could be reduced to more structured shorter sequences. It is shown that this sequences exist and follow consistent rules. Potential features of an infinite cycle, also leading to a smaller number, are also discussed. Further, an argument for only one possible closed cycle is given for the special sequence of alternating odd and even steps as well as arguments that infinite cycles must exist. Using the observation that periodic behavior is exists an additional argument is provided the probability of subsets which will end up at a number smaller the initial value possibly even of 

Uses Mathlib (`ℚ`, `omega`, positivity-style facts via Core).
Status: `mainStatement` records the paper claim; only named lemmas are proved.
Source: https://arxiv.org/abs/2311.16765
-/

namespace MathlibAttack.Papers.Arxiv2311_16765

open MathlibAttack.Papers

def citation : String := "J. St\u00f6ckl, \"Observations towards a proof of the Collatz conjecture using $2^{j}k+x$ number series\", arXiv:2311.16765 [2023]."

/-- Recorded cycle-exclusion shell (paper theorem not proved). -/
def mainStatement : Prop :=
  ∀ n : ℕ, 1 < n → ∀ k : ℕ, 0 < k → orbit k n = n →
    ∃ j : ℕ, j ≤ k ∧ orbit j n = 1

/-- Checked: the trivial 1-cycle returns. -/
theorem orbit_one_cycle : orbit 3 1 = 1 :=
  MathlibAttack.Papers.orbit_one_returns

end MathlibAttack.Papers.Arxiv2311_16765
