import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Adam L McEvoy, "The Fractal Correction Engine Applied to the Collatz Conjecture: Orbit Geometry, Fractal Dimension, and a Statistical Rigor Study with Baselines, Ablations, and Synthetic Controls", 2026.

Title: The Fractal Correction Engine Applied to the Collatz Conjecture: Orbit Geometry, Fractal Dimension, and a Statistical Rigor Study with Baselines, Ablations, and Synthetic Controls

Abstract (from harvested metadata, truncated):
# The Fractal Correction Engine Applied to the Collatz Conjecture: Orbit Geometry, Fractal Dimension, and a Statistical Rigor Study with Baselines, Ablations, and Synthetic Controls **Author:** Adam L McEvoy **Date:** 5 July 2026 **Version:** 2.0 **Keywords:** Collatz conjecture, fractal correction engine, fractal dimension, Higuchi method, pi-normalised curvature, trajectory prediction, bootstrap confidence intervals, hypothesis testing, synthetic controls, ablation study, number theory, dynamical systems **Classification:** 11B83 (Special sequences), 37M05 (Simulation of dynamical systems), 28A80 (Fractals), 62F40 (Bootstrap and resampling) --- ## Abstract I present an application of the F...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.19143557
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_19143557

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Adam L McEvoy, \"The Fractal Correction Engine Applied to the Collatz Conjecture: Orbit Geometry, Fractal Dimension, and a Statistical Rigor Study with Baselines, Ablations, and Synthetic Controls\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.19143557 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_19143557
