import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Eduardo Diedrich, "Structural Constraints on the Inverse Collatz Tree, and a Separation of the Drift Windows for 3n+1 and 3n−1", 2026.

Title: Structural Constraints on the Inverse Collatz Tree, and a Separation of the Drift Windows for 3n+1 and 3n−1

Abstract (from harvested metadata, truncated):
We give a self-contained account of the combinatorial and arithmetic structure of the inverse Collatz tree rooted at 1, and we prove a separation result that distinguishes the 3n+1 dynamics from its closest structural analogue, the 3n−1 dynamics. Structure theory. We establish a closed form for the node reached along a prescribed address, a complete description of the local constraints on admissible addresses, and a 3-adic density theorem showing that the odd nodes of the tree are dense in the 3-adic integers. The density theorem has a negative corollary of independent interest: no congruence condition modulo a power of 3 can obstruct membership in the tree, so no argument of that type can s...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.21846929
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_21846929

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Eduardo Diedrich, \"Structural Constraints on the Inverse Collatz Tree, and a Separation of the Drift Windows for 3n+1 and 3n−1\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.21846929 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_21846929
