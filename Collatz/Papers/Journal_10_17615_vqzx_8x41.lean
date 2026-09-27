import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Hande, Anand, "Characterization of Syracuse Maps as Non-singular Power-Bounded Transformations and the Inverse Image", 2023.

Title: Characterization of Syracuse Maps as Non-singular Power-Bounded Transformations and the Inverse Image

Abstract (from harvested metadata, truncated):
In this thesis, we will introduce the well-known Collatz Conjecture, discussing some of the previous work done on this problem. Next, we give a dynamical system characterization of an arbitrary map V : N → N, which applies to both the Collatz Map and the related Syracuse maps. In the third section of this thesis, we discuss some number theoretic properties of the Collatz inverse image, comparing some properties to one particular subclass of the Syracuse maps. In the last section, we analyze previous density results, looking at what this does and does not give in terms of density results on the elements with unbounded Collatz trajectories, denoted by D2. We also motivate the study of density...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.17615/vqzx-8x41
-/

namespace Collatz.Papers.Journal_10_17615_vqzx_8x41

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Hande, Anand, \"Characterization of Syracuse Maps as Non-singular Power-Bounded Transformations and the Inverse Image\", The University of North Carolina at Chapel Hill University Libraries, DOI:10.17615/vqzx-8x41 [2023]."

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

end Collatz.Papers.Journal_10_17615_vqzx_8x41
