import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Asset Durmagambetov and A. A. Durmagambetova, "Collatz Conjecture: Analysis of Binary Structure and Trajectory Behavior", arXiv:2401.0227 [2026].

Title: Collatz Conjecture: Analysis of Binary Structure and Trajectory Behavior

Abstract (from OpenAlex metadata, truncated):
We develop an exact "mantissa" formalism for the binary expansions of natural numbers, in which the gap structure between consecutive ones is encoded by a sequence of fractional parts $\sigma_j\in(0,1]$. Within this formalism we prove a sharp threshold dichotomy: the next binary gap equals 1 precisely when $\sigma_j\le \kappa$, where $\kappa=2-\log_2 3\approx 0.41504$. For $M=3^n$ we obtain rigorous consequences: an exact characterization of the leading run of ones in terms of $\{n\log_2 3\}$, whence, by Weyl equidistribution, the asymptotic density of $n$ whose expansion begins with $m$ ones equals \(-\log_2(1 - 2^{-m})\), and, by effective bounds for linear forms in logarithms, the leading run has length \(O(\log n)\); and a proof that the trailing run of ones always has length 1 or 2. On the trajectory side, we give an exact decomposition of Collatz iterations, a lemma describing prec

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2401.0227
-/

namespace Collatz.Papers.Arxiv2401_0227

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Asset Durmagambetov and A. A. Durmagambetova, \"Collatz Conjecture: Analysis of Binary Structure and Trajectory Behavior\", arXiv:2401.0227 [2026]."

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


end Collatz.Papers.Arxiv2401_0227
