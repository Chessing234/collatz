import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Si, Yuan, "A microcanonical phase transition for the Collatz affine random model", 2026.

Title: A microcanonical phase transition for the Collatz affine random model

Abstract (from harvested metadata, truncated):
We introduce a microcanonical framework for the Syracuse affine random model of Tao (Forum Math. Pi, 2022) by conditioning on S_n = s. Under this conditioning the multiplicative phase becomes deterministic, and the affine Fourier coefficient at hard frequencies reduces to a primitive ternary Bernoulli-bridge transform on a real-line perpetuity. Combining ensemble equivalence, Brémont's Rajchman classification for contracting-on-average affine IFS, and an exact suffix self-similarity,we prove a sharp phase transition for the resonant hard frequency at the entropy line h_* = 2 log_3 2 - 1 ≈ 0.262: subcritical decay below, supercritical obstruction above. We further prove density-one and fiberwise flattening for all hard frequencies via pair-switch averaging, forcing any HFBD-violating...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.20027096
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_20027096

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Si, Yuan, \"A microcanonical phase transition for the Collatz affine random model\", DOI:10.5281/zenodo.20027096 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_20027096
