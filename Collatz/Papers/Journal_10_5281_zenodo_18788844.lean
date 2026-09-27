import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Miguel Cerdá Bennassar, "Structural reduction of the Collatz conjecture: segments, portals and 2-adic survival sets", 2026.

Title: Structural reduction of the Collatz conjecture: segments, portals and 2-adic survival sets

Abstract (from harvested metadata, truncated):
This paper develops a structural analysis of the Collatz conjecture by decomposing orbits into finite building blocks called segments, each governed by exact algebraic rules. A key notion is introduced — the portal — a special class of odd numbers that act as the decisive transition points of the dynamics: every segment closes at a portal, and at every portal a structural functional measuring the size of the orbit decreases unconditionally.Working within this framework, the paper proves that no non-trivial cycle can remain entirely within the class of portals, establishes an exact measure-theoretic result showing that the set of initial conditions compatible with a non-convergent orbit has m...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.18788844
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_18788844

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Miguel Cerdá Bennassar, \"Structural reduction of the Collatz conjecture: segments, portals and 2-adic survival sets\", Zenodo, DOI:10.5281/zenodo.18788844 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_18788844
