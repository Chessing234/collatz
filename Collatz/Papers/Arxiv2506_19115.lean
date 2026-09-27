import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Sebastian Angermund, "A Two-Operator Calculus for Arithmetic-Progression Paths in the Collatz Graph", arXiv:2506.19115 [2025].

Title: A Two-Operator Calculus for Arithmetic-Progression Paths in the Collatz Graph

Abstract (from OpenAlex metadata, truncated):
A recast of the standard residue-class analysis of the 3x+1 (Collatz) map in terms of two elementary operators on arithmetic progressions. The resulting calculus (i) splits any progression into its even and odd subsequences in a single step, (ii) gives a closed formula for every set of seeds that realises a prescribed parity word, (iii) yields a one line affine invariant that forbids trajectories consisting of infinitely many odd moves, and (iv) reduces the non-trivial-cycle problem to a pair of linear congruences.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2506.19115
-/

namespace Collatz.Papers.Arxiv2506_19115

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Sebastian Angermund, \"A Two-Operator Calculus for Arithmetic-Progression Paths in the Collatz Graph\", arXiv:2506.19115 [2025]."

/-- Recorded main claim shell (cycle); not proved.
States that any accelerated return to `n > 1` has already visited `1`. -/
def mainStatement : Prop :=
  ∀ n : Nat, n > 1 → ∀ k : Nat, 0 < k → Collatz.orbit k n = n →
    ∃ j : Nat, j ≤ k ∧ Collatz.orbit j n = 1

/-- Checked: the trivial 1-cycle returns to 1. -/
theorem orbit_one_returns : Collatz.orbit 3 1 = 1 :=
  (Collatz.Papers.MathlibCopied.trivial_cycle).1

theorem step_branches_on_cycle :
    Collatz.step 1 = 4 ∧ Collatz.step 4 = 2 ∧ Collatz.step 2 = 1 := by
  have h := Collatz.Papers.MathlibCopied.trivial_cycle
  exact ⟨h.2.1, h.2.2.1, h.2.2.2⟩


end Collatz.Papers.Arxiv2506_19115
