import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Maxwell C. Siegel, "The Collatz Conjecture & Non-Archimedean Spectral Theory -- Part I.5 -- How To Write The (Weak) Collatz Conjecture As A Contour Integral", arXiv:2111.07883 [2021].

Title: The Collatz Conjecture & Non-Archimedean Spectral Theory -- Part I.5 -- How To Write The (Weak) Collatz Conjecture As A Contour Integral

Abstract (from OpenAlex metadata, truncated):
Let $q$ be an odd prime, and let $T_{q}:\mathbb{Z}\rightarrow\mathbb{Z}$ be the Shortened $qx+1$ map, defined by $T_{q}\left(n\right)=n/2$ if $n$ is even and $T_{q}\left(n\right)=\left(qn+1\right)/2$ if $n$ is odd. The study of the dynamics of these maps is infamous for its difficulty, with the characterization of the dynamics of $T_{3}$ being an alternative formulation of the famous Collatz Conjecture. This series of papers presents a new paradigm for studying such arithmetic dynamical systems by way of a neglected area of ultrametric analysis which we have termed $\left(p,q\right)$-adic analysis, the study of functions from the $p$-adics to the $q$-adics, where $p$ and $q$ are distinct primes. In this, the first-and-a-halfth paper of the series, as a first application, we show that the numen $χ_{q}$ of $T_{q}$ can be used in conjunction with the Correspondence Principle (CP) and classic complex-analytic tools of analytic number theory to reformulate the study of periodic points of $T

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2111.07883
-/

namespace Collatz.Papers.Arxiv2111_07883

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Maxwell C. Siegel, \"The Collatz Conjecture & Non-Archimedean Spectral Theory -- Part I.5 -- How To Write The (Weak) Collatz Conjecture As A Contour Integral\", arXiv:2111.07883 [2021]."

/-- Recorded main claim shell (cycle); not proved.
States that any accelerated return to `n > 1` has already visited `1`. -/
def mainStatement : Prop :=
  ∀ n : Nat, n > 1 → ∀ k : Nat, 0 < k → Collatz.orbit k n = n →
    ∃ j : Nat, j ≤ k ∧ Collatz.orbit j n = 1

/-- Checked: the trivial 1-cycle returns to 1. -/
theorem orbit_one_returns : Collatz.orbit 3 1 = 1 :=
  (Collatz.Papers.MathlibCopied.trivial_cycle).1

theorem step_branches_on_cycle :
    Collatz.step 1 = 4 ∧ Collatz.step 4 = 2 ∧ Collatz.step 2 = 1 := by
  have h := Collatz.Papers.MathlibCopied.trivial_cycle
  exact ⟨h.2.1, h.2.2.1, h.2.2.2⟩


end Collatz.Papers.Arxiv2111_07883
