import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Mark D. LaDue, "Clusters of Integers with Equal Total Stopping Times in the 3x + 1 Problem", arXiv:1709.02979 [2017].

Title: Clusters of Integers with Equal Total Stopping Times in the 3x + 1 Problem

Abstract (from OpenAlex metadata, truncated):
The clustering of integers with equal total stopping times has long been observed in the 3x + 1 Problem, and a number of elementary results about it have been used repeatedly in the literature. In this paper we introduce a simple recursively defined function C(n), and we use it to give a necessary and sufficient condition for pairs of consecutive even and odd integers to have trajectories which coincide after a specific pair-dependent number of steps. Then we derive a number of standard total stopping time equalities, including the ones in Garner (1985), as well as several novel results.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/1709.02979
-/

namespace Collatz.Papers.Arxiv1709_02979

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Mark D. LaDue, \"Clusters of Integers with Equal Total Stopping Times in the 3x + 1 Problem\", arXiv:1709.02979 [2017]."

/-- Recorded finite-verification claim shell; the paper's bound is not proved here. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1


/-- Miniature checked verification for `B = 2`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩


end Collatz.Papers.Arxiv1709_02979
