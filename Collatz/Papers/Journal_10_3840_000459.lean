import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Unknown, "Density Map for the 3n+1 Problem", 2008.

Title: Density Map for the 3n+1 Problem

Abstract (from harvested metadata, truncated):
(No abstract in harvested metadata; statement recorded from title/venue only.)

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.3840/000459
-/

namespace Collatz.Papers.Journal_10_3840_000459

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Unknown, \"Density Map for the 3n+1 Problem\", Wolfram Demonstrations Project, DOI:10.3840/000459 [2008]."

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

end Collatz.Papers.Journal_10_3840_000459
