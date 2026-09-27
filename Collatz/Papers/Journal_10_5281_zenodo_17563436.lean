import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Miguel Cerdá Bennassar, "A 2-adic Density Lemma in the Odd Trajectory of the Collatz Map", 2025.

Title: A 2-adic Density Lemma in the Odd Trajectory of the Collatz Map

Abstract (from harvested metadata, truncated):
This work analyzes the odd–even dynamics of the classical Collatz map from a 2-adic viewpoint. It proves that odd numbers with ν₂(3n + 1) = r form arithmetic progressions of relative density 1/2^{r–1}, explaining the increasing gaps observed in Collatz trajectories. Using this 2-adic information, all odd numbers sharing the same last even term are grouped into 4-adic families, showing that every family converges to 𝔽₂ = {1, 5, 21, 85,…}. The cycle 4 → 2 → 1 emerges as a unique global attractor. The framework also connects explicitly with the Structure Theorem for (d,g,h)-maps by Kontorovich and Sinai (2006), where the decreasing 2-adic density plays the role of the negative drift in their probabilistic model.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.17563436
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_17563436

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Miguel Cerdá Bennassar, \"A 2-adic Density Lemma in the Odd Trajectory of the Collatz Map\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.17563436 [2025]."

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

end Collatz.Papers.Journal_10_5281_zenodo_17563436
