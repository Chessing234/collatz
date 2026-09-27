import MathlibAttack.Papers.Core

/-!
Mathlib-backed Lean notes for Jishe Feng, "Using binary string to prove the Collatz conjecture", arXiv:2402.00001 [2023].

Title: Using binary string to prove the Collatz conjecture

Abstract (truncated):
We introduce a full binary directed tree structure to represent the set of natural numbers, further categorizing them into three distinct subsets: pure odd numbers, pure even numbers, and mixed numbers. We adopt a binary string representation for natural numbers and elaborate on the composite methodology encompassing odd- and even-number functions. Our analysis focuses on examining the iteration sequence (or composition) of the Collatz function and its reduced variant, which serves as an analog to the inverse function, to scrutinize the validity of the Collatz conjecture. To substantiate this conjecture, we incorporate binary strings into an algebraic formula that captures the essence of the Collatz sequence. By this means, we transform discrete powers of 2 into continuous counterparts, ultimately culminating in the smallest natural number, 1. Consequently, the sequence generated through

Uses Mathlib (`ℚ`, `omega`, positivity-style facts via Core).
Status: `mainStatement` records the paper claim; only named lemmas are proved.
Source: https://arxiv.org/abs/2402.00001
-/

namespace MathlibAttack.Papers.Arxiv2402_00001

open MathlibAttack.Papers

def citation : String := "Jishe Feng, \"Using binary string to prove the Collatz conjecture\", arXiv:2402.00001 [2023]."

/-- Recorded cycle-exclusion shell (paper theorem not proved). -/
def mainStatement : Prop :=
  ∀ n : ℕ, 1 < n → ∀ k : ℕ, 0 < k → orbit k n = n →
    ∃ j : ℕ, j ≤ k ∧ orbit j n = 1

/-- Checked: the trivial 1-cycle returns. -/
theorem orbit_one_cycle : orbit 3 1 = 1 :=
  MathlibAttack.Papers.orbit_one_returns

end MathlibAttack.Papers.Arxiv2402_00001
