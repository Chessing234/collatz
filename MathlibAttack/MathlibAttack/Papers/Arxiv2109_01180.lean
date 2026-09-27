import MathlibAttack.Papers.Core

/-!
Mathlib-backed Lean notes for Quang-Nhat Le and Edward Smith, "Observations on cycles in a variant of the Collatz Graph", arXiv:2109.01180 [2021].

Title: Observations on cycles in a variant of the Collatz Graph

Abstract (truncated):
It is well known that the Collatz Conjecture can be reinterpreted as the Collatz Graph with root vertex 1, asking whether all positive integers are within the tree generated. It is further known that any cycle in the Collatz Graph can be represented as a tuple, given that inputting them into a function outputs an odd positive integer; yet, it is an open question as to whether there exist any tuples not of the form $(2,2,...,2)$, thus disproving the Collatz Conjecture. In this paper, we explore a variant of the Collatz Graph, which allows the 3x+1 operation to be applied to both even and odd integers. We prove an analogous function for this variant, called the Loosened Collatz Function (LCF), and observe various properties of the LCF in relation to tuples and outputs. We prove a certain underlying unique factorisation monoid structure for tuples to the LCF and provide a geometric interpre

Uses Mathlib (`ℚ`, `omega`, positivity-style facts via Core).
Status: `mainStatement` records the paper claim; only named lemmas are proved.
Source: https://arxiv.org/abs/2109.01180
-/

namespace MathlibAttack.Papers.Arxiv2109_01180

open MathlibAttack.Papers

def citation : String := "Quang-Nhat Le and Edward Smith, \"Observations on cycles in a variant of the Collatz Graph\", arXiv:2109.01180 [2021]."

/-- Recorded cycle-exclusion shell (paper theorem not proved). -/
def mainStatement : Prop :=
  ∀ n : ℕ, 1 < n → ∀ k : ℕ, 0 < k → orbit k n = n →
    ∃ j : ℕ, j ≤ k ∧ orbit j n = 1

/-- Checked: the trivial 1-cycle returns. -/
theorem orbit_one_cycle : orbit 3 1 = 1 :=
  MathlibAttack.Papers.orbit_one_returns

end MathlibAttack.Papers.Arxiv2109_01180
