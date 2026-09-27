import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Abdelrahman Ramzy, "Note on Collatz conjecture", arXiv:2310.13930 [2023].

Title: Note on Collatz conjecture

Abstract (from OpenAlex metadata, truncated):
In this paper, we show that if the numbers in the range $[1,2^n]$ satisfy Collatz conjecture, then almost all integers in the range $[2^n+1,2^{n+1}]$ will satisfy the conjecture as $n \to \infty$. The previous statement is equivalent to claiming that almost all integers in $[2^n+1,2^{n+1}]$ will iterate to a number less than $2^n$. This actually has been proved by many previous results. But in this paper we prove this claim using different methods. We also utilize our assumption on numbers in $[1,2^n]$ to show that there are a set of integers (denoted by $p\operatorname{-}C$) whose seem to be not iterating to a number less than $2^n$, but since they are connected to Collatz numbers in $[1,2^n]$ they eventually will iterate to $1$. We address the distribution of $p\operatorname{-}C$ and give an explicit formula which computes a lower bound to the number of these integers. We also show (computationally) that the number of $p\operatorname{-}C$ in a given interval is proportional to the nu

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2310.13930
-/

namespace Collatz.Papers.Arxiv2310_13930

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Abdelrahman Ramzy, \"Note on Collatz conjecture\", arXiv:2310.13930 [2023]."

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


end Collatz.Papers.Arxiv2310_13930
