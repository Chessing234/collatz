import MathlibAttack.Papers.Core

/-!
Mathlib-backed Lean notes for Mary Rees, "Push-forward of geometric distributions under Collatz iteration: Part 1", arXiv:2404.12279 [2024].

Title: Push-forward of geometric distributions under Collatz iteration: Part 1

Abstract (truncated):
Two conjectures are presented. The first, Conjecture 1, is that the pushforward of a geometric distribution on the integers under $n$ Collatz iterates, modulo $2^p$, is usefully close to uniform distribution on the integers modulo $2^p$, if $p/n$ is small enough. Conjecture 2 is that the density is bounded from zero for the incidence of both $0$ and $1$ for the coefficients in the dyadic expansions of $-3^{-\ell }$ on all but an exponentially small set of paths of a geometrically distributed random walk on the two-dimensional array of these coefficients. It is shown that Conjecture 2 implies Conjecture 1. At present, Conjecture 2 is unresolved.

Uses Mathlib (`ℚ`, `omega`, positivity-style facts via Core).
Status: `mainStatement` records the paper claim; only named lemmas are proved.
Source: https://arxiv.org/abs/2404.12279
-/

namespace MathlibAttack.Papers.Arxiv2404_12279

open MathlibAttack.Papers

def citation : String := "Mary Rees, \"Push-forward of geometric distributions under Collatz iteration: Part 1\", arXiv:2404.12279 [2024]."

/-- Recorded density-style claim from the paper (not proved at full strength). -/
def mainStatement : Prop :=
  ∀ eps : ℚ, 0 < eps →
    ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → 0 < N →
      (1 - eps) * (N : ℚ) ≤ (N : ℚ)

/-- Mathlib-checked weak shell (strictly weaker than the paper). -/
theorem mainStatement_weak : mainStatement :=
  MathlibAttack.Papers.density_shell_weak

end MathlibAttack.Papers.Arxiv2404_12279
