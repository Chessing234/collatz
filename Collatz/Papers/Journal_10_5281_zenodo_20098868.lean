import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Borgatta, Piero, "A Spectral Reduction of the Collatz Conjecture via Phantom Orbit Shadowing - v2", 2026.

Title: A Spectral Reduction of the Collatz Conjecture via Phantom Orbit Shadowing - v2

Abstract (from harvested metadata, truncated):
Version 2 of the preprint, superseding v1 (DOI 10.5281/zenodo.20021538) of May 2026. The mathematical core is unchanged; v2 incorporates a completed Lean 4 + Mathlib formal verification of the foundational shadowing lemma, an explicit comparison with the concurrent work of Chang (arXiv:2603.11066), an expanded related-work section, and an extended methodology section that makes the cross-AI verification protocol explicit. Mathematical content We propose a structural reformulation of the Collatz conjecture in terms of a finite-dimensional spectral problem. Starting from the empirical observation that “rebel” orbits of the Syracuse map shadow, for finite stretches, periodic rational points of the 2-adic dynamics associated to negative rational fixed points (the “phantom cycles” of Chang...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.20098868
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_20098868

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Borgatta, Piero, \"A Spectral Reduction of the Collatz Conjecture via Phantom Orbit Shadowing - v2\", DOI:10.5281/zenodo.20098868 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_20098868
