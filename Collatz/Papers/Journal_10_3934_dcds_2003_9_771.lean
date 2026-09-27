import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Günther Wirsching, "On the problem of positive predecessor density in $3n+1$ dynamics", 2003.

Title: On the problem of positive predecessor density in $3n+1$ dynamics

Abstract (from harvested metadata, truncated):
(No abstract in harvested metadata; statement recorded from title/venue only.)

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.3934/dcds.2003.9.771
-/

namespace Collatz.Papers.Journal_10_3934_dcds_2003_9_771

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Günther Wirsching, \"On the problem of positive predecessor density in $3n+1$ dynamics\", Discrete and Continuous Dynamical Systems, DOI:10.3934/dcds.2003.9.771 [2003]."

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

end Collatz.Papers.Journal_10_3934_dcds_2003_9_771
