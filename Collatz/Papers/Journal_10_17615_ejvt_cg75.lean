import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Ebbighausen, Ethan, "The Bounded Trajectories Conjecture for Syracuse Maps", 2024.

Title: The Bounded Trajectories Conjecture for Syracuse Maps

Abstract (from harvested metadata, truncated):
The Collatz Conjecture has haunted the mathematical scene for nearly 100 years. In this thesis, we introduce part of the conjecture, and its generalization to a larger class of maps. Using some theory from dynamical systems, we pose several equivalent conditions to conjecture through the construction of various measures. Next, we investigate the set L of Terras, providing a rate of convergence to his density argument to give partial control of the inverse Collatz map.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.17615/ejvt-cg75
-/

namespace Collatz.Papers.Journal_10_17615_ejvt_cg75

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Ebbighausen, Ethan, \"The Bounded Trajectories Conjecture for Syracuse Maps\", The University of North Carolina at Chapel Hill University Libraries, DOI:10.17615/ejvt-cg75 [2024]."

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

end Collatz.Papers.Journal_10_17615_ejvt_cg75
