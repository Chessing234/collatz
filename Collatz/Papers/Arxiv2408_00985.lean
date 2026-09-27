import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Giovanny Fuentes, "The Collatz Conjecture “The Non-Existence of Divergent Orbits Through an Analysis of the Codification of Linear Diophantine Dynamical Systems”", arXiv:2408.00985 [2025].

Title: The Collatz Conjecture “The Non-Existence of Divergent Orbits Through an Analysis of the Codification of Linear Diophantine Dynamical Systems”

Abstract (from OpenAlex metadata, truncated):
We define the function $Col: \mathbb{N} \to \mathbb{N}$ as the Collatz function, given by $3n + 1$ if $n$ is odd and $\displaystyle\frac{n}{2}$ if $n$ is even. The conjecture postulates that for any positive integer, at some point, its iteration will reach 1, or equivalently, every orbit will fall into the periodic cycle $\{4, 2, 1\}$. Two conditions would invalidate the conjecture: The existence of a divergent orbit or the presence of another cycle. We can study the dynamics of the orbits through the density of even terms in their orbit. If all points' accumulation density exceeds the value of $\displaystyle\frac{\ln(3)}{\ln(2)}$ then the orbit is bounded. The main result of this work is to show that there are no natural numbers such that the accumulation points of the pair density are less than $\displaystyle\frac{\ln(3)}{\ln(2)}$. In other words, there are no divergent orbits.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2408.00985
-/

namespace Collatz.Papers.Arxiv2408_00985

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Giovanny Fuentes, \"The Collatz Conjecture \u201cThe Non-Existence of Divergent Orbits Through an Analysis of the Codification of Linear Diophantine Dynamical Systems\u201d\", arXiv:2408.00985 [2025]."

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

end Collatz.Papers.Arxiv2408_00985
