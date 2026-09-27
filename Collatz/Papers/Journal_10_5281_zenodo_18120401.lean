import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Krishnaswamy Bharati Gandhi Mohan, "Reproducibility and figures for "The Hidden Order of the Collatz Problem"", 2026.

Title: Reproducibility and figures for "The Hidden Order of the Collatz Problem"

Abstract (from harvested metadata, truncated):
This record contains figures, reference material, and reproducibility artifacts supporting the paper “The Hidden Order of the Collatz Problem”(doi:10.5281/zenodo.18119833). The authoritative scholarly version of the work is the Zenodo preprint. This software record exists solely to support verification, reuse, and reproducibility.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.18120401
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_18120401

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Krishnaswamy Bharati Gandhi Mohan, \"Reproducibility and figures for \"The Hidden Order of the Collatz Problem\"\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.18120401 [2026]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Journal_10_5281_zenodo_18120401
