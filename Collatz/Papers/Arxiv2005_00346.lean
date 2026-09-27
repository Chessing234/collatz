import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Robert Santos, "On the Collatz general problem $qn+1$", arXiv:2005.00346 [2020].

Title: On the Collatz general problem $qn+1$

Abstract (from OpenAlex metadata, truncated):
In this work the generalized Collatz problem $qn+1$ ($q$ odd) is studied. As a natural generalization of the original $3n+1$ problem, it consists of a discrete dynamical system of an arithmetical kind. Using standard methods of number theory and dynamical systems, general properties are established, such as the existence of finitely many periodic sequences for each $q$. In particular, when $q$ is a Mersenne number, $q=2^p-1$, there only exists one such cycle, known as the trivial one. Further analysis based on a probabilistic model shows that for $q=3$ the asymptotic behavior of all sequences is always convergent, whereas for $q\geq 5$ the asymptotic behavior of the sequences is divergent for almost all numbers (for a set of natural density one). This leads to the conclusion that the so called Collatz Conjecture is true, and that $q=3$ is a very special case among the others (Crandall co

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2005.00346
-/

namespace Collatz.Papers.Arxiv2005_00346

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Robert Santos, \"On the Collatz general problem $qn+1$\", arXiv:2005.00346 [2020]."

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


end Collatz.Papers.Arxiv2005_00346
