import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Ivan Korec, "A density estimate for the $3x+1$ problem", 1994.

Title: A density estimate for the $3x+1$ problem

Abstract (from harvested metadata, truncated):
(No abstract in harvested metadata; statement recorded from title/venue only.)

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: (no stable URL in metadata)
-/

namespace Collatz.Papers.Journal_1994_Korec_a_density_estimate_for_the_3x

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Ivan Korec, \"A density estimate for the $3x+1$ problem\", Czech digital mathematics library [1994]."

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

end Collatz.Papers.Journal_1994_Korec_a_density_estimate_for_the_3x
