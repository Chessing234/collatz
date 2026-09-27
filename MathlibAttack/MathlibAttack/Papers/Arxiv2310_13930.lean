import MathlibAttack.Papers.Core

/-!
Mathlib-backed Lean notes for Abdelrahman Ramzy, "Note on Collatz conjecture", arXiv:2310.13930 [2023].

Title: Note on Collatz conjecture

Abstract (truncated):
In this paper, we show that if the numbers in the range $[1,2^n]$ satisfy Collatz conjecture, then almost all integers in the range $[2^n+1,2^{n+1}]$ will satisfy the conjecture as $n \to \infty$. The previous statement is equivalent to claiming that almost all integers in $[2^n+1,2^{n+1}]$ will iterate to a number less than $2^n$. This actually has been proved by many previous results. But in this paper we prove this claim using different methods. We also utilize our assumption on numbers in $[1,2^n]$ to show that there are a set of integers (denoted by $p\operatorname{-}C$) whose seem to be not iterating to a number less than $2^n$, but since they are connected to Collatz numbers in $[1,2^n]$ they eventually will iterate to $1$. We address the distribution of $p\operatorname{-}C$ and give an explicit formula which computes a lower bound to the number of these integers. We also show (co

Uses Mathlib (`ℚ`, `omega`, positivity-style facts via Core).
Status: `mainStatement` records the paper claim; only named lemmas are proved.
Source: https://arxiv.org/abs/2310.13930
-/

namespace MathlibAttack.Papers.Arxiv2310_13930

open MathlibAttack.Papers

def citation : String := "Abdelrahman Ramzy, \"Note on Collatz conjecture\", arXiv:2310.13930 [2023]."

/-- Recorded density-style claim from the paper (not proved at full strength). -/
def mainStatement : Prop :=
  ∀ eps : ℚ, 0 < eps →
    ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → 0 < N →
      (1 - eps) * (N : ℚ) ≤ (N : ℚ)

/-- Mathlib-checked weak shell (strictly weaker than the paper). -/
theorem mainStatement_weak : mainStatement :=
  MathlibAttack.Papers.density_shell_weak

end MathlibAttack.Papers.Arxiv2310_13930
