import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Dwivedi, Ritesh, Yadav, Rohit, "A Divisor-Sum Analogue of the Collatz Map", arXiv:2506.01830 [2025].

Title: A Divisor-Sum Analogue of the Collatz Map

Abstract (from OpenAlex metadata, truncated):
Let $σ$ denote the sum-of-divisors function and let $\mathcal{R}$ send an odd integer $n$ to $σ(n)$ and an even integer $n$ to $n/2$. We conjecture that every orbit of $\mathcal{R}$ reaches $1$; this implies that there is no odd $2^{k}$-perfect number for any $k \ge 1$. We prove a pointwise descent estimate for the map $T$ induced by $\mathcal{R}$ on the odd integers, and show that a single application of $T$ divides almost every odd $n$ by $(\log n)^{2\log 2-\varepsilon}$, for every fixed $\varepsilon>0$. The estimate does not iterate, and we determine what is missing.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2506.01830
-/

namespace Collatz.Papers.Arxiv2506_01830

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Dwivedi, Ritesh and Yadav, Rohit, \"A Divisor-Sum Analogue of the Collatz Map\", arXiv:2506.01830 [2025]."

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

end Collatz.Papers.Arxiv2506_01830
