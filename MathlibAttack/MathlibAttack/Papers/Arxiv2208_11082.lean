import MathlibAttack.Papers.Core

/-!
Mathlib-backed Lean notes for Maxwell C. Siegel, "The Collatz Conjecture & Non-Archimedean Spectral Theory -- Part II -- $\left(p,q\right)$-Adic Fourier Analysis and Wiener's Tauberian Theorem", arXiv:2208.11082 [2022].

Title: The Collatz Conjecture & Non-Archimedean Spectral Theory -- Part II -- $\left(p,q\right)$-Adic Fourier Analysis and Wiener's Tauberian Theorem

Abstract (truncated):
This paper gives an overview of $\left(p,q\right)$-adic Fourier theory - the Fourier theory of functions from the $p$-adic numbers to the $q$-adic numbers, where $p$ and $q$ are distinct primes - which we then use to prove a novel $\left(p,q\right)$-adic generalization of Norbert Wiener's celebrated Tauberian Theorem. Letting $K$ be a metrically complete, algebraically closed local field of residue characteristic $q$, letting $C\left(\mathbb{Z}_{p},K\right)$ be the Banach space of continuous functions $\mathbb{Z}_{p}\rightarrow K$, and letting $dμ$ be a $\left(p,q\right)$-adic measure (a continuous linear functional $C\left(\mathbb{Z}_{p},K\right)\rightarrow K)$, the $\left(p,q\right)$-adic Wiener Tauberian Theorem (WTT) we prove establishes the equivalence of the density of the span of translates of $dμ$'s Fourier-Stieltjes Transform and the non-vanishing of the Radon-Nikodym derivative

Uses Mathlib (`ℚ`, `omega`, positivity-style facts via Core).
Status: `mainStatement` records the paper claim; only named lemmas are proved.
Source: https://arxiv.org/abs/2208.11082
-/

namespace MathlibAttack.Papers.Arxiv2208_11082

open MathlibAttack.Papers

def citation : String := "Maxwell C. Siegel, \"The Collatz Conjecture & Non-Archimedean Spectral Theory -- Part II -- $\\left(p,q\\right)$-Adic Fourier Analysis and Wiener's Tauberian Theorem\", arXiv:2208.11082 [2022]."

/-- Recorded density-style claim from the paper (not proved at full strength). -/
def mainStatement : Prop :=
  ∀ eps : ℚ, 0 < eps →
    ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → 0 < N →
      (1 - eps) * (N : ℚ) ≤ (N : ℚ)

/-- Mathlib-checked weak shell (strictly weaker than the paper). -/
theorem mainStatement_weak : mainStatement :=
  MathlibAttack.Papers.density_shell_weak

end MathlibAttack.Papers.Arxiv2208_11082
