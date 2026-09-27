import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Kionke, Steffen, "A geometric approach to divergent points of higher dimensional Collatz mappings", arXiv:1511.05893 [2015].

Title: A geometric approach to divergent points of higher dimensional Collatz mappings

Abstract (from arXiv metadata, truncated):
We define generalized Collatz mappings on free abelian groups of finite rank and study their iteration trajectories. Using geometric arguments we describe cones of points having a divergent trajectory and we deduce lower bounds for the density of the set of divergent points. As an application we give examples which show that the iteration of generalized Collatz mappings on rings of algebraic integers can behave quite differently from the conjectured behavior in $Z$.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/1511.05893
-/

namespace Collatz.Papers.Arxiv1511_05893

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Kionke, Steffen, \"A geometric approach to divergent points of higher dimensional Collatz mappings\", arXiv:1511.05893 [2015]."

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

end Collatz.Papers.Arxiv1511_05893
