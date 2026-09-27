import MathlibAttack.Papers.Core

/-!
Mathlib-backed Lean notes for Maxwell C. Siegel, "$\left(p,q\right)$-adic Analysis and the Collatz Conjecture", arXiv:2412.02902 [2024].

Title: $\left(p,q\right)$-adic Analysis and the Collatz Conjecture

Abstract (truncated):
What use can there be for a function from the $p$-adic numbers to the $q$-adic numbers, where $p$ and $q$ are distinct primes? The traditional answer, courtesy of the half-century old theory of non-archimedean functional analysis: not much. It turns out this judgment was premature. '$\left(p,q\right)$-adic analysis' of this sort appears to be naturally suited for studying the infamous Collatz map and similar arithmetical dynamical systems. Given such a map $H:\mathbb{Z}\rightarrow\mathbb{Z}$, one can construct a function $χ_{H}:\mathbb{Z}_{p}\rightarrow\mathbb{Z}_{q}$ for an appropriate choice of distinct primes $p,q$ with the property that $x\in\mathbb{Z}\backslash\left\{ 0\right\} $ is a periodic point of $H$ if and only if there is a $p$-adic integer $\mathfrak{z}\in\left(\mathbb{Q}\cap\mathbb{Z}_{p}\right)\backslash\left\{ 0,1,2,\ldots\right\} $ so that $χ_{H}\left(\mathfrak{z}\right

Uses Mathlib (`ℚ`, `omega`, positivity-style facts via Core).
Status: `mainStatement` records the paper claim; only named lemmas are proved.
Source: https://arxiv.org/abs/2412.02902
-/

namespace MathlibAttack.Papers.Arxiv2412_02902

open MathlibAttack.Papers

def citation : String := "Maxwell C. Siegel, \"$\\left(p,q\\right)$-adic Analysis and the Collatz Conjecture\", arXiv:2412.02902 [2024]."

/-- Recorded cycle-exclusion shell (paper theorem not proved). -/
def mainStatement : Prop :=
  ∀ n : ℕ, 1 < n → ∀ k : ℕ, 0 < k → orbit k n = n →
    ∃ j : ℕ, j ≤ k ∧ orbit j n = 1

/-- Checked: the trivial 1-cycle returns. -/
theorem orbit_one_cycle : orbit 3 1 = 1 :=
  MathlibAttack.Papers.orbit_one_returns

end MathlibAttack.Papers.Arxiv2412_02902
