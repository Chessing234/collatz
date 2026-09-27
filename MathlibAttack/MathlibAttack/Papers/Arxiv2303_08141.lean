import MathlibAttack.Papers.Core

/-!
Mathlib-backed Lean notes for M. Bruschi and F. Calogero, "Variations on a Theme of Collatz", arXiv:2303.08141 [2023].

Title: Variations on a Theme of Collatz

Abstract (truncated):
Consider the recursive relation generating a new positive integer $n_{\ell +1}$ from the positive integer $n_{\ell }$ according to the following simple rules: if the integer $n_{\ell }$ is odd, $n_{\ell +1}=3n_{\ell }+1$; if the integer $n_{\ell }$ is even, $n_{\ell +1}=n_{\ell }/2$. The so-called Collatz conjecture states that, starting from any positive integer $N$, the recursion characterized by the continued application of these rules ends up in the cycle $4,$ $2,1$. This conjecture is generally believed to be true (on the basis of extensive numerical checks), but it is as yet unproven. In this paper -- based on the assumption that the Collatz conjecture is indeed true -- we present a quite simple extension of it, which entails the possibility to divide all natural numbers into $3$ disjoint classes, to each of which we conjecture -- on the basis of (not very extensive) numerical chec

Uses Mathlib (`ℚ`, `omega`, positivity-style facts via Core).
Status: `mainStatement` records the paper claim; only named lemmas are proved.
Source: https://arxiv.org/abs/2303.08141
-/

namespace MathlibAttack.Papers.Arxiv2303_08141

open MathlibAttack.Papers

def citation : String := "M. Bruschi and F. Calogero, \"Variations on a Theme of Collatz\", arXiv:2303.08141 [2023]."

/-- Recorded cycle-exclusion shell (paper theorem not proved). -/
def mainStatement : Prop :=
  ∀ n : ℕ, 1 < n → ∀ k : ℕ, 0 < k → orbit k n = n →
    ∃ j : ℕ, j ≤ k ∧ orbit j n = 1

/-- Checked: the trivial 1-cycle returns. -/
theorem orbit_one_cycle : orbit 3 1 = 1 :=
  MathlibAttack.Papers.orbit_one_returns

end MathlibAttack.Papers.Arxiv2303_08141
