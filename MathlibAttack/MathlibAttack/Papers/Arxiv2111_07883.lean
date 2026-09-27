import MathlibAttack.Papers.Core

/-!
Mathlib-backed Lean notes for Maxwell C. Siegel, "The Collatz Conjecture & Non-Archimedean Spectral Theory -- Part I.5 -- How To Write The (Weak) Collatz Conjecture As A Contour Integral", arXiv:2111.07883 [2021].

Title: The Collatz Conjecture & Non-Archimedean Spectral Theory -- Part I.5 -- How To Write The (Weak) Collatz Conjecture As A Contour Integral

Abstract (truncated):
Let $q$ be an odd prime, and let $T_{q}:\mathbb{Z}\rightarrow\mathbb{Z}$ be the Shortened $qx+1$ map, defined by $T_{q}\left(n\right)=n/2$ if $n$ is even and $T_{q}\left(n\right)=\left(qn+1\right)/2$ if $n$ is odd. The study of the dynamics of these maps is infamous for its difficulty, with the characterization of the dynamics of $T_{3}$ being an alternative formulation of the famous Collatz Conjecture. This series of papers presents a new paradigm for studying such arithmetic dynamical systems by way of a neglected area of ultrametric analysis which we have termed $\left(p,q\right)$-adic analysis, the study of functions from the $p$-adics to the $q$-adics, where $p$ and $q$ are distinct primes. In this, the first-and-a-halfth paper of the series, as a first application, we show that the numen $χ_{q}$ of $T_{q}$ can be used in conjunction with the Correspondence Principle (CP) and classi

Uses Mathlib (`ℚ`, `omega`, positivity-style facts via Core).
Status: `mainStatement` records the paper claim; only named lemmas are proved.
Source: https://arxiv.org/abs/2111.07883
-/

namespace MathlibAttack.Papers.Arxiv2111_07883

open MathlibAttack.Papers

def citation : String := "Maxwell C. Siegel, \"The Collatz Conjecture & Non-Archimedean Spectral Theory -- Part I.5 -- How To Write The (Weak) Collatz Conjecture As A Contour Integral\", arXiv:2111.07883 [2021]."

/-- Recorded cycle-exclusion shell (paper theorem not proved). -/
def mainStatement : Prop :=
  ∀ n : ℕ, 1 < n → ∀ k : ℕ, 0 < k → orbit k n = n →
    ∃ j : ℕ, j ≤ k ∧ orbit j n = 1

/-- Checked: the trivial 1-cycle returns. -/
theorem orbit_one_cycle : orbit 3 1 = 1 :=
  MathlibAttack.Papers.orbit_one_returns

end MathlibAttack.Papers.Arxiv2111_07883
