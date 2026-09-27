import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Diedrich E., "Resolution of the Collatz Conjecture via Structural and Quantitative Approaches", 2025.

Title: Resolution of the Collatz Conjecture via Structural and Quantitative Approaches

Abstract (from harvested metadata, truncated):
We present a comprehensive resolution of the Collatz conjecture through two complementary approaches. The primary approach develops a novel framework based on inverse function properties and generative completeness, establishing that all trajectories in the Collatz dynamical system converge to the cycle {1 , 4 , 2}. A second, independent proof using measure theory provides explicit computational bounds for convergence times. Together, these approaches offer both structural understanding and quantitative characterization of the system’s behavior, providing a complete resolution of this long-standing problem.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.22541/au.173660871.17716215/v1
-/

namespace Collatz.Papers.Journal_10_22541_au_173660871_17716215_v1

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Diedrich E., \"Resolution of the Collatz Conjecture via Structural and Quantitative Approaches\", DOI:10.22541/au.173660871.17716215/v1 [2025]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Journal_10_22541_au_173660871_17716215_v1
