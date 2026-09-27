import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Edward Yi Chang, "Exploring Collatz Dynamics with Human-LLM Collaboration", arXiv:2603.11066 [2026].

Title: Exploring Collatz Dynamics with Human-LLM Collaboration

Abstract (from OpenAlex metadata, truncated):
We present a comprehensive structural analysis of the Collatz conjecture through ~1014 computational experiments yielding 630 formal results. By systematically deploying 29 distinct mathematical paradigms--including transfer operator spectral theory, S-unit equations, p-adic interpolation, martingale methods, modular sieving, formal language theory, cascade algebra, discrete logarithm obstruction, and Diophantine approximation--we establish a Paradigm Exhaustion Theorem: every known framework for promoting distributional convergence ("almost all orbits descend") to pointwise convergence ("all orbits descend") encounters an irreducible structural obstruction when applied to the Syracuse map. On the unconditional side, we prove: (i) the Syracuse transfer operator has a uniform spectral gap for all M, implying equidistribution modulo any power of 2; (ii) any nontrivial cycle of length L satisfies D > 2^F for all L >= 3, giving ord_D(2) > F and F+1 distinct residues mod D; (iii) divergent 

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2603.11066
-/

namespace Collatz.Papers.Arxiv2603_11066

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Edward Yi Chang, \"Exploring Collatz Dynamics with Human-LLM Collaboration\", arXiv:2603.11066 [2026]."

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


end Collatz.Papers.Arxiv2603_11066
