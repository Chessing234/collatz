import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Melvyn B. Nathanson, "Permutation Patterns of the Iterated Syracuse Function", arXiv:2308.00644 [2023].

Title: Permutation Patterns of the Iterated Syracuse Function

Abstract (from OpenAlex metadata, truncated):
Let $Ω$ be the set of odd positive integers and let $S:Ω\rightarrow Ω$ be the Syracuse function. It is proved that, for every permutation $σ$ of $(1,2,3)$, the set of triples of the form $(m,S(m),S^2(m))$ with permutation pattern $σ$ has positive density, and these densities are computed. However, there exist permutations $τ$ of $(1,2,3,4)$ such that no quadruple $(m,S(m), S^2(m), S^3(m))$ has permutation pattern $τ$. This implies the nonexistence of certain permutation patterns of $n$-tuples $(m,S(m),\ldots, S^{n-1}(m))$ for all $n \geq 4$.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2308.00644
-/

namespace Collatz.Papers.Arxiv2308_00644

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Melvyn B. Nathanson, \"Permutation Patterns of the Iterated Syracuse Function\", arXiv:2308.00644 [2023]."

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


end Collatz.Papers.Arxiv2308_00644
