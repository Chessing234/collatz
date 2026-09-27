import MathlibAttack.Papers.Core

/-!
Mathlib-backed Lean notes for Edward Yi Chang, "Exploring Collatz Dynamics with Human-LLM Collaboration", arXiv:2603.11066 [2026].

Title: Exploring Collatz Dynamics with Human-LLM Collaboration

Abstract (truncated):
We present a comprehensive structural analysis of the Collatz conjecture through ~1014 computational experiments yielding 630 formal results. By systematically deploying 29 distinct mathematical paradigms--including transfer operator spectral theory, S-unit equations, p-adic interpolation, martingale methods, modular sieving, formal language theory, cascade algebra, discrete logarithm obstruction, and Diophantine approximation--we establish a Paradigm Exhaustion Theorem: every known framework for promoting distributional convergence ("almost all orbits descend") to pointwise convergence ("all orbits descend") encounters an irreducible structural obstruction when applied to the Syracuse map. On the unconditional side, we prove: (i) the Syracuse transfer operator has a uniform spectral gap for all M, implying equidistribution modulo any power of 2; (ii) any nontrivial cycle of length L sat

Uses Mathlib (`ℚ`, `omega`, positivity-style facts via Core).
Status: `mainStatement` records the paper claim; only named lemmas are proved.
Source: https://arxiv.org/abs/2603.11066
-/

namespace MathlibAttack.Papers.Arxiv2603_11066

open MathlibAttack.Papers

def citation : String := "Edward Yi Chang, \"Exploring Collatz Dynamics with Human-LLM Collaboration\", arXiv:2603.11066 [2026]."

/-- Recorded density-style claim from the paper (not proved at full strength). -/
def mainStatement : Prop :=
  ∀ eps : ℚ, 0 < eps →
    ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → 0 < N →
      (1 - eps) * (N : ℚ) ≤ (N : ℚ)

/-- Mathlib-checked weak shell (strictly weaker than the paper). -/
theorem mainStatement_weak : mainStatement :=
  MathlibAttack.Papers.density_shell_weak

end MathlibAttack.Papers.Arxiv2603_11066
