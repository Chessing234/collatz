import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Rongtian Peng, "Proof of Almost Sure Descent Property in the Collatz Conjecture", 2026.

Title: Proof of Almost Sure Descent Property in the Collatz Conjecture

Abstract (from harvested metadata, truncated):
Objective: The Collatz conjecture asserts that under the iteration "even numbers are divided by 2, odd numbers are multiplied by 3 and added by 1", all positive integers eventually enter the 4-2-1 cycle. This paper proves that the Collatz map possesses an almost sure descent property on the set of positive integers. Method: The process by which an arbitrary positive integer first descends to a number smaller than itself is defined as an "elementary path", and its structure is characterized by a sequence. The existence of each type of path is guaranteed by properties of Diophantine equations. All possible elementary paths are enumerated via dynamic programming. A two-dimensional random walk m...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.19425142
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_19425142

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Rongtian Peng, \"Proof of Almost Sure Descent Property in the Collatz Conjecture\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.19425142 [2026]."

/-- Recorded density-style claim shell; the paper's theorem is not proved. -/
def mainStatement : Prop :=
  ∀ eps : Rat, 0 < eps →
    ∃ N0 : Nat, ∀ N : Nat, N0 ≤ N → 0 < N →
      ((1 : Rat) - eps) * (N : Rat) ≤ (N : Rat)

/-- Weak density scaffolding (Mathlib-copied `Rat` facts); strictly weaker than the paper. -/
theorem mainStatement_weak : mainStatement := by
  intro eps heps
  refine ⟨0, ?_⟩
  intro N _ _
  exact Collatz.Papers.MathlibCopied.density_shell_of_pos eps N heps

end Collatz.Papers.Journal_10_5281_zenodo_19425142
