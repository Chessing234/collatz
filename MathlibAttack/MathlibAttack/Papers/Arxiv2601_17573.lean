import MathlibAttack.Papers.Core

/-!
Mathlib-backed Lean notes for Abderrahman Bouhamidi, "Weakly and Strongly Admissible Triplets for a Collatz-Type Map", arXiv:2601.17573 [2026].

Title: Weakly and Strongly Admissible Triplets for a Collatz-Type Map

Abstract (truncated):
In this paper, we investigate a class of Collatz-like problems associated with weakly and strongly admissible triplets of integers. This framework extends the classical Collatz mapping, providing a systematic method for generating triplets with convergence to cycles, thereby bypassing the difficulties inherent in solving Diophantine equations. We introduce several special families of admissible triplets and establish general structural properties. In addition, we propose conjectures that generalize the classical Collatz conjecture. Bounds on the lengths of potential non-trivial cycles are derived and analyzed, and two algorithms are presented for computing lower bounds on cycle lengths. Finally, experimental tests are given to illustrate our approach.

Uses Mathlib (`ℚ`, `omega`, positivity-style facts via Core).
Status: `mainStatement` records the paper claim; only named lemmas are proved.
Source: https://arxiv.org/abs/2601.17573
-/

namespace MathlibAttack.Papers.Arxiv2601_17573

open MathlibAttack.Papers

def citation : String := "Abderrahman Bouhamidi, \"Weakly and Strongly Admissible Triplets for a Collatz-Type Map\", arXiv:2601.17573 [2026]."

/-- Recorded cycle-exclusion shell (paper theorem not proved). -/
def mainStatement : Prop :=
  ∀ n : ℕ, 1 < n → ∀ k : ℕ, 0 < k → orbit k n = n →
    ∃ j : ℕ, j ≤ k ∧ orbit j n = 1

/-- Checked: the trivial 1-cycle returns. -/
theorem orbit_one_cycle : orbit 3 1 = 1 :=
  MathlibAttack.Papers.orbit_one_returns

end MathlibAttack.Papers.Arxiv2601_17573
