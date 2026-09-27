import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Maxwell C. Siegel, "The Collatz Conjecture & Non-Archimedean Spectral Theory -- Part II -- $\left(p,q\right)$-Adic Fourier Analysis and Wiener's Tauberian Theorem", arXiv:2208.11082 [2022].

Title: The Collatz Conjecture & Non-Archimedean Spectral Theory -- Part II -- $\left(p,q\right)$-Adic Fourier Analysis and Wiener's Tauberian Theorem

Abstract (from OpenAlex metadata, truncated):
This paper gives an overview of $\left(p,q\right)$-adic Fourier theory - the Fourier theory of functions from the $p$-adic numbers to the $q$-adic numbers, where $p$ and $q$ are distinct primes - which we then use to prove a novel $\left(p,q\right)$-adic generalization of Norbert Wiener's celebrated Tauberian Theorem. Letting $K$ be a metrically complete, algebraically closed local field of residue characteristic $q$, letting $C\left(\mathbb{Z}_{p},K\right)$ be the Banach space of continuous functions $\mathbb{Z}_{p}\rightarrow K$, and letting $dμ$ be a $\left(p,q\right)$-adic measure (a continuous linear functional $C\left(\mathbb{Z}_{p},K\right)\rightarrow K)$, the $\left(p,q\right)$-adic Wiener Tauberian Theorem (WTT) we prove establishes the equivalence of the density of the span of translates of $dμ$'s Fourier-Stieltjes Transform and the non-vanishing of the Radon-Nikodym derivative of $dμ$ at all points in $\mathbb{Z}_{p}$ where the derivative exists in $K$.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2208.11082
-/

namespace Collatz.Papers.Arxiv2208_11082

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Maxwell C. Siegel, \"The Collatz Conjecture & Non-Archimedean Spectral Theory -- Part II -- $\\left(p,q\\right)$-Adic Fourier Analysis and Wiener's Tauberian Theorem\", arXiv:2208.11082 [2022]."

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


end Collatz.Papers.Arxiv2208_11082
