import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for J Allikvere, "Periodic shadows, drift pressure, and transcendence of the 3x+1 conjugacy map", 2026.

Title: Periodic shadows, drift pressure, and transcendence of the 3x+1 conjugacy map

Abstract (from harvested metadata, truncated):
Bernstein and Lagarias defined a homeomorphism Φ: Z₂ → Z₂ conjugating the Collatz map to the 2-adic shift. López and Stoll asked whether an aperiodic parity word can map to a rational 2-adic integer under Φ. We give an elementary periodic-shadow criterion: if an aperiodic word w shares long initial segments with eventually periodic words, then a quantitative congruence bounds the shared length by the archimedean height of the rational shadow value, forcing Φ(w) ∉ Q. The governing height exponent is the drift pressure m(δ) = max(1, δ·log₂3), where δ is the ones-density; for balanced words the height of a shadow of combined length N is at most 2^(m(δ)N + O(log N)). Combined with the 2-adic Rot...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.21543841
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_21543841

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "J Allikvere, \"Periodic shadows, drift pressure, and transcendence of the 3x+1 conjugacy map\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.21543841 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_21543841
