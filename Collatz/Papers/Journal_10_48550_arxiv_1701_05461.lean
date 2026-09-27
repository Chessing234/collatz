import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Stahl, Denver, "Convergence and Divergence of Mersenne Variations of the $3x+1$ Function", 2017.

Title: Convergence and Divergence of Mersenne Variations of the $3x+1$ Function

Abstract (from harvested metadata, truncated):
The Collatz problem is one of many names (the Collatz Problem, the Syracuse Problem, the Hailstone Problem, the 3x+1 problem). Most commonly, however, the problem goes by either the 3x+1 problem or the Collatz problem. In addition to having many names, the Collatz problem has many variations, such as those in the form introduced by Jeffrey Lagarias in 1985. This writing discusses several variations of the Collatz function which involve the Mersenne numbers. Following that, we observe the convergent cycles of these functions which we can then relate back to the original Collatz 3x+1 function. Lastly, we give a proof of the No Divergent Trajectories Theorem and show why the same cannot be show...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.48550/arxiv.1701.05461
-/

namespace Collatz.Papers.Journal_10_48550_arxiv_1701_05461

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Stahl, Denver, \"Convergence and Divergence of Mersenne Variations of the $3x+1$ Function\", arXiv, DOI:10.48550/arxiv.1701.05461 [2017]."

/-- Recorded nontrivial-cycle exclusion shell; the paper's theorem is not proved. -/
def mainStatement : Prop :=
  ∀ n : Nat, 1 < n → ∀ k : Nat, 0 < k → Collatz.orbit k n = n →
    ∃ j : Nat, j ≤ k ∧ Collatz.orbit j n = 1

/-- Checked: the trivial cycle through `1` returns after three steps. -/
theorem orbit_one_returns : Collatz.orbit 3 1 = 1 :=
  (Collatz.Papers.MathlibCopied.trivial_cycle).1

theorem step_branches_on_cycle :
    Collatz.step 1 = 4 ∧ Collatz.step 4 = 2 ∧ Collatz.step 2 = 1 := by
  have h := Collatz.Papers.MathlibCopied.trivial_cycle
  exact ⟨h.2.1, h.2.2.1, h.2.2.2⟩

end Collatz.Papers.Journal_10_48550_arxiv_1701_05461
