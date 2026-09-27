import MathlibAttack.Papers.Core

/-!
Mathlib-backed Lean notes for Robert H. Nichols, "A Collatz Conjecture Proof", arXiv:2112.07361 [2021].

Title: A Collatz Conjecture Proof

Abstract (truncated):
We represent the generalized Collatz function with the recursive ruler function r(2n) = r(n) + 1 and r(2n + 1) = 1. We generate even-only and odd-only Collatz subsequences that contain significantly fewer elements term by term, to 2 and 1, respectively, than are present in the original 3n + 1 and the Terras-modified Collatz sequences. We show that a nonlinear, coupled system of difference equations yields a complete acyclic (except for the trivial cycle) Collatz tree in odds not divisible by 3 with root vertex 1. We construct a complete Collatz tree with the axiom of choice and prove the Collatz conjecture.

Uses Mathlib (`ℚ`, `omega`, positivity-style facts via Core).
Status: `mainStatement` records the paper claim; only named lemmas are proved.
Source: https://arxiv.org/abs/2112.07361
-/

namespace MathlibAttack.Papers.Arxiv2112_07361

open MathlibAttack.Papers

def citation : String := "Robert H. Nichols, \"A Collatz Conjecture Proof\", arXiv:2112.07361 [2021]."

/-- Recorded cycle-exclusion shell (paper theorem not proved). -/
def mainStatement : Prop :=
  ∀ n : ℕ, 1 < n → ∀ k : ℕ, 0 < k → orbit k n = n →
    ∃ j : ℕ, j ≤ k ∧ orbit j n = 1

/-- Checked: the trivial 1-cycle returns. -/
theorem orbit_one_cycle : orbit 3 1 = 1 :=
  MathlibAttack.Papers.orbit_one_returns

end MathlibAttack.Papers.Arxiv2112_07361
