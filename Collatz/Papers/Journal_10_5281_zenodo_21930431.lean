import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Idris Ali Shaik, "Lean 4 Formalization: Polylogarithmic Descent for Almost All Collatz Orbits in Natural Density", 2026.

Title: Lean 4 Formalization: Polylogarithmic Descent for Almost All Collatz Orbits in Natural Density

Abstract (from harvested metadata, truncated):
This archive contains the Version 4 Lean formalization accompanying “Polylogarithmic Descent for Almost All Collatz Orbits in Natural Density.” It checks the strengthened critical arbitrary-multiplier result, the fixed-exponent common-landing theorem with centered shortcut and raw clocks and the exact upper exceptional-rate endpoint, the matching height-forced lower order for the balanced joint exceptional event, and the quantitative stretched-logarithmic common-landing theorem with relative-height control. The release is frozen at tag lean-v4.0.0 and commit a419e012be2aeb735387385a711c211651ccf527. It uses Lean 4.15.0 and Mathlib revision 9837ca9d65d9de6fad1ef4381750ca688774e608. From the e...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.21930431
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_21930431

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Idris Ali Shaik, \"Lean 4 Formalization: Polylogarithmic Descent for Almost All Collatz Orbits in Natural Density\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.21930431 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_21930431
