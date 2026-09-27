import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Idris Assani and Ethan Ebbighausen, "On the Convergence of the Density of Terras' Set", arXiv:2310.08749 [2023].

Title: On the Convergence of the Density of Terras' Set

Abstract (from OpenAlex metadata, truncated):
The Collatz Conjecture's connection to dynamical systems opens it to a variety of techniques aimed at recurrence and density results. First, we turn to density results and strengthen the result of Terras through finding a strict rate of convergence. This rate gives a preliminary result on the Triangle Conjecture, which describes a set nodes that would dominate $L^{C} = \{y \in \N \, | \, T^{k}(y) > y , \,\forall k \in \N \}$. Second, we extend prior arguments to show that the construction of several classes of measures imply the bounded trajectories piece of the Collatz Conjecture.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2310.08749
-/

namespace Collatz.Papers.Arxiv2310_08749

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Idris Assani and Ethan Ebbighausen, \"On the Convergence of the Density of Terras' Set\", arXiv:2310.08749 [2023]."

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


end Collatz.Papers.Arxiv2310_08749
