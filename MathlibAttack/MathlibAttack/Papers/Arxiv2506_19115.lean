import MathlibAttack.Papers.Core

/-!
Mathlib-backed Lean notes for Sebastian Angermund, "A Two-Operator Calculus for Arithmetic-Progression Paths in the Collatz Graph", arXiv:2506.19115 [2025].

Title: A Two-Operator Calculus for Arithmetic-Progression Paths in the Collatz Graph

Abstract (truncated):
A recast of the standard residue-class analysis of the 3x+1 (Collatz) map in terms of two elementary operators on arithmetic progressions. The resulting calculus (i) splits any progression into its even and odd subsequences in a single step, (ii) gives a closed formula for every set of seeds that realises a prescribed parity word, (iii) yields a one line affine invariant that forbids trajectories consisting of infinitely many odd moves, and (iv) reduces the non-trivial-cycle problem to a pair of linear congruences.

Uses Mathlib (`ℚ`, `omega`, positivity-style facts via Core).
Status: `mainStatement` records the paper claim; only named lemmas are proved.
Source: https://arxiv.org/abs/2506.19115
-/

namespace MathlibAttack.Papers.Arxiv2506_19115

open MathlibAttack.Papers

def citation : String := "Sebastian Angermund, \"A Two-Operator Calculus for Arithmetic-Progression Paths in the Collatz Graph\", arXiv:2506.19115 [2025]."

/-- Recorded cycle-exclusion shell (paper theorem not proved). -/
def mainStatement : Prop :=
  ∀ n : ℕ, 1 < n → ∀ k : ℕ, 0 < k → orbit k n = n →
    ∃ j : ℕ, j ≤ k ∧ orbit j n = 1

/-- Checked: the trivial 1-cycle returns. -/
theorem orbit_one_cycle : orbit 3 1 = 1 :=
  MathlibAttack.Papers.orbit_one_returns

end MathlibAttack.Papers.Arxiv2506_19115
