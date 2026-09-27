import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Maxwell C. Siegel, "$\left(p,q\right)$-adic Analysis and the Collatz Conjecture", arXiv:2412.02902 [2024].

Title: $\left(p,q\right)$-adic Analysis and the Collatz Conjecture

Abstract (from OpenAlex metadata, truncated):
What use can there be for a function from the $p$-adic numbers to the $q$-adic numbers, where $p$ and $q$ are distinct primes? The traditional answer, courtesy of the half-century old theory of non-archimedean functional analysis: not much. It turns out this judgment was premature. '$\left(p,q\right)$-adic analysis' of this sort appears to be naturally suited for studying the infamous Collatz map and similar arithmetical dynamical systems. Given such a map $H:\mathbb{Z}\rightarrow\mathbb{Z}$, one can construct a function $χ_{H}:\mathbb{Z}_{p}\rightarrow\mathbb{Z}_{q}$ for an appropriate choice of distinct primes $p,q$ with the property that $x\in\mathbb{Z}\backslash\left\{ 0\right\} $ is a periodic point of $H$ if and only if there is a $p$-adic integer $\mathfrak{z}\in\left(\mathbb{Q}\cap\mathbb{Z}_{p}\right)\backslash\left\{ 0,1,2,\ldots\right\} $ so that $χ_{H}\left(\mathfrak{z}\right)=x$. By generalizing Monna-Springer integration theory and establishing a $\left(p,q\right)$-adic a

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2412.02902
-/

namespace Collatz.Papers.Arxiv2412_02902

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Maxwell C. Siegel, \"$\\left(p,q\\right)$-adic Analysis and the Collatz Conjecture\", arXiv:2412.02902 [2024]."

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


end Collatz.Papers.Arxiv2412_02902
