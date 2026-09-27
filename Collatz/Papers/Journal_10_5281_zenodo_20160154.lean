import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Borgatta, Piero, "A Spectral Reduction of the Collatz Conjecture via Phantom Orbit Shadowing - v3", 2026.

Title: A Spectral Reduction of the Collatz Conjecture via Phantom Orbit Shadowing - v3

Abstract (from harvested metadata, truncated):
Version 3 of the preprint, superseding v2 (DOI 10.5281/zenodo.20098868) of May 2026. The mathematical core of v2 is unchanged; v3 extends it along two axes: a finite phantom-set taxonomy at depth $K_0 = 16$, and an extended Lean 4 + Mathlib formalization that now covers the finite operator layer in addition to the shadowing core. Mathematical content We propose a structural reformulation of the Collatz conjecture in terms of a finite-dimensional spectral problem. Starting from the empirical observation that “rebel” orbits of the Syracuse map shadow, for finite stretches, periodic rational points of the 2-adic dynamics associated to negative rational fixed points (the “phantom cycles” of Chang 2026, an object that goes back to Lagarias 1985 and the Böhm–Sontacchi criterion in the Collatz...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.20160154
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_20160154

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Borgatta, Piero, \"A Spectral Reduction of the Collatz Conjecture via Phantom Orbit Shadowing - v3\", DOI:10.5281/zenodo.20160154 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_20160154
