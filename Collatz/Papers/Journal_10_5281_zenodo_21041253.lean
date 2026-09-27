import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Ethan FUCHS, "Semi-octet approach to collatz problem", 2025.

Title: Semi-octet approach to collatz problem

Abstract (from harvested metadata, truncated):
The methodology relies on two key principles: (i) the propagation of zeros within eachsemi-octet, ensuring that specific structural patterns decrease irreversibly under iteration, and(ii) the definition of a discrete entropy measure, derived from the bit-length and zero density ofintegers, which strictly decreases along trajectories until the trivial cycle (4, 2, 1) is reached. Byperforming an exhaustive and semi-exhaustive analysis of all relevant semi-octet configurations,we formalize the observed entropic contraction and provide an empirically verifiable argumentfor convergence.Beyond the canonical 3x + 1 map, this framework extends naturally to affine iterative sys-tems of the form Ta,b (n), offering structural criteria to classify convergence, divergence, andchaotic behavior. The...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.21041253
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_21041253

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Ethan FUCHS, \"Semi-octet approach to collatz problem\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.21041253 [2025]."

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

end Collatz.Papers.Journal_10_5281_zenodo_21041253
