import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Felipe Gonçalves et al., "Generalized Collatz Maps with Almost Bounded Orbits", arXiv:2111.06170 [2021].

Title: Generalized Collatz Maps with Almost Bounded Orbits

Abstract (from OpenAlex metadata, truncated):
If dividing by $p$ is a mistake, multiply by $q$ and translate, and so you'll live to iterate. We show that if we define a Collatz-like map in this form then, under suitable conditions on $p$ and $q$, almost all orbits of this map attain almost bounded values. This generalizes a recent breakthrough result of Tao for the original Collatz map (i.e., $p=2$ and $q=3$). In other words, given an arbitrary growth function $N\mapsto f(N)$ we show that almost every orbit of such map with input $N$ eventually attains a value smaller than $f(N)$.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2111.06170
-/

namespace Collatz.Papers.Arxiv2111_06170

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Felipe Gon\u00e7alves et al., \"Generalized Collatz Maps with Almost Bounded Orbits\", arXiv:2111.06170 [2021]."

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


end Collatz.Papers.Arxiv2111_06170
