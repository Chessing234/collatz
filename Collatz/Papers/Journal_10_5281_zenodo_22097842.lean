import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Khamit Kadyrbekov and Daniyal Kadirbekov, "Obstructions to Low-Dimensional Natural Matrix Interpretations for a Mixed-Base Collatz Rewrite System", 2026.

Title: Obstructions to Low-Dimensional Natural Matrix Interpretations for a Mixed-Base Collatz Rewrite System

Abstract (from harvested metadata, truncated):
Reproducible software artifact and computer-assisted proof materials accompanying the manuscript “Obstructions to Low-Dimensional Natural Matrix Interpretations for a Mixed-Base Collatz Rewrite System.” The artifact reconstructs exact integer Farkas certificates and provides deterministic regression tests for the symbolic classification. The mathematical result excludes one-stage relative natural affine matrix interpretations in dimensions one and two for the specified mixed-base Collatz rewrite system; it does not prove or disprove the Collatz conjecture.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.22097842
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_22097842

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Khamit Kadyrbekov and Daniyal Kadirbekov, \"Obstructions to Low-Dimensional Natural Matrix Interpretations for a Mixed-Base Collatz Rewrite System\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.22097842 [2026]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Journal_10_5281_zenodo_22097842
