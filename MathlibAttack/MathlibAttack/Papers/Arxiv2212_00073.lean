import MathlibAttack.Papers.Core

/-!
Mathlib-backed Lean notes for Naouel Boulkaboul, "$3n+3^k$: New Perspective on Collatz Conjecture", arXiv:2212.00073 [2022].

Title: $3n+3^k$: New Perspective on Collatz Conjecture

Abstract (truncated):
Collatz conjecture is generalized to $3n+3^k$ ($k\in N$). Operating as usual, every sequence seems to reach $3^k$ and end up in the loop $3^k, 4.3^k, 2.3^k,3^k$. The usual $3n+1$ conjecture is recovered for $k=0$. For $k>0$, we noticed the existence of a sequence of period 3, namely, $3^{k-1}, 2.3^k, 3^k$, alongside the cycle $4.3^k, 2.3^k,3^k$ encountered in the $3n+1 (k=0)$ sequence. A term formula of the $3n+3^k$ conjecture has been derived, and hence the total stopping time.

Uses Mathlib (`ℚ`, `omega`, positivity-style facts via Core).
Status: `mainStatement` records the paper claim; only named lemmas are proved.
Source: https://arxiv.org/abs/2212.00073
-/

namespace MathlibAttack.Papers.Arxiv2212_00073

open MathlibAttack.Papers

def citation : String := "Naouel Boulkaboul, \"$3n+3^k$: New Perspective on Collatz Conjecture\", arXiv:2212.00073 [2022]."

/-- Recorded cycle-exclusion shell (paper theorem not proved). -/
def mainStatement : Prop :=
  ∀ n : ℕ, 1 < n → ∀ k : ℕ, 0 < k → orbit k n = n →
    ∃ j : ℕ, j ≤ k ∧ orbit j n = 1

/-- Checked: the trivial 1-cycle returns. -/
theorem orbit_one_cycle : orbit 3 1 = 1 :=
  MathlibAttack.Papers.orbit_one_returns

end MathlibAttack.Papers.Arxiv2212_00073
