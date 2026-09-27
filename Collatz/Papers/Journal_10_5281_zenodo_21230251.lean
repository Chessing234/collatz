import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Николай Архипов, "«Complete Proof of the Collatz Hypothesis and the Universal Equation d = S × 2ⁿ − 3m»", 2026.

Title: «Complete Proof of the Collatz Hypothesis and the Universal Equation d = S × 2ⁿ − 3m»

Abstract (from harvested metadata, truncated):
This paper presents a complete proof of the Collatz hypothesis (the 3n+1 problem), based on its own quadruplets and the governing equation 3x² − 4x − 4 = 0. A general theory for 3n+d systems is constructed. Global convergence and the uniqueness of the 4→2→1 cycle are strictly proven, and the Arche principle is formulated, linking the proof to the architecture of binary systems. A universal equation d = S × 2ⁿ − 3m is derived, describing all possible cycles for any d and m.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.21230251
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_21230251

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Николай Архипов, \"«Complete Proof of the Collatz Hypothesis and the Universal Equation d = S × 2ⁿ − 3m»\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.21230251 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_21230251
