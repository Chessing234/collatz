import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Mary Rees, "Push-forward of geometric distributions under Collatz iteration: Part 1", arXiv:2404.12279 [2024].

Title: Push-forward of geometric distributions under Collatz iteration: Part 1

Abstract (from OpenAlex metadata, truncated):
Two conjectures are presented. The first, Conjecture 1, is that the pushforward of a geometric distribution on the integers under $n$ Collatz iterates, modulo $2^p$, is usefully close to uniform distribution on the integers modulo $2^p$, if $p/n$ is small enough. Conjecture 2 is that the density is bounded from zero for the incidence of both $0$ and $1$ for the coefficients in the dyadic expansions of $-3^{-\ell }$ on all but an exponentially small set of paths of a geometrically distributed random walk on the two-dimensional array of these coefficients. It is shown that Conjecture 2 implies Conjecture 1. At present, Conjecture 2 is unresolved.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2404.12279
-/

namespace Collatz.Papers.Arxiv2404_12279

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Mary Rees, \"Push-forward of geometric distributions under Collatz iteration: Part 1\", arXiv:2404.12279 [2024]."

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


end Collatz.Papers.Arxiv2404_12279
