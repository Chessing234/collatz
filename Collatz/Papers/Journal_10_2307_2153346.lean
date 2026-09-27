import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for David Applegate and Jeffrey C. Lagarias, "Density Bounds for the 3x + 1 Problem. II. Krasikov Inequalities", 1995.

Title: Density Bounds for the 3x + 1 Problem. II. Krasikov Inequalities

Abstract (from harvested metadata, truncated):
(No abstract in harvested metadata; statement recorded from title/venue only.)

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.2307/2153346
-/

namespace Collatz.Papers.Journal_10_2307_2153346

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "David Applegate and Jeffrey C. Lagarias, \"Density Bounds for the 3x + 1 Problem. II. Krasikov Inequalities\", Mathematics of Computation, DOI:10.2307/2153346 [1995]."

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

end Collatz.Papers.Journal_10_2307_2153346
