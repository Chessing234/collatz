import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Nidhal Mghirbi, "Supplementary material for the paper: "Defect-area bounds near the Christoffel boundary for Collatz cycles"", 2026.

Title: Supplementary material for the paper: "Defect-area bounds near the Christoffel boundary for Collatz cycles"

Abstract (from harvested metadata, truncated):
Supplementary material for the paper: "Defect-area bounds near the Christoffel boundary for Collatz cycles".

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.22060022
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_22060022

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Nidhal Mghirbi, \"Supplementary material for the paper: \"Defect-area bounds near the Christoffel boundary for Collatz cycles\"\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.22060022 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_22060022
