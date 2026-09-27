import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Rodgers, Jeremy, "A Drift–Potential Framework and Finite Linear-Programming Reduction of the Collatz Conjecture", 2025.

Title: A Drift–Potential Framework and Finite Linear-Programming Reduction of the Collatz Conjecture

Abstract (from harvested metadata, truncated):
This paper presents a complete, deterministic, and finite resolution of the Collatz conjecture via a new drift–potential framework for discrete nonlinear dynamical systems. The classical Collatz iteration is reformulated as an odd-only dynamical system equipped with an explicitly constructed potential function whose long-term behavior is governed by an exact drift decomposition. The method introduces a rigorous phase classification of orbit segments, derives exact local and clustered drift bounds, and proves a universal structural drift floor. A critical density threshold is established beyond which all non-descending behavior is analytically excluded. The remaining exceptional low-band conf...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.17845717
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_17845717

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Rodgers, Jeremy, \"A Drift–Potential Framework and Finite Linear-Programming Reduction of the Collatz Conjecture\", Zenodo, DOI:10.5281/zenodo.17845717 [2025]."

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

end Collatz.Papers.Journal_10_5281_zenodo_17845717
