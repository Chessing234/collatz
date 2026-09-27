import MathlibAttack.Papers.Core

/-!
Mathlib-backed Lean notes for Zeraoulia Rafik, "Amazing behavior and transition to chaos of some sequences using Collatz like problems and Quibic duffing", arXiv:2302.01904 [2022].

Title: Amazing behavior and transition to chaos of some sequences using Collatz like problems and Quibic duffing

Abstract (truncated):
In this paper we shall show amazing behavior of some discrete maps using Collatze like problems and some advanced theories in analytic number theory and dynamical system,we have investigated the driven cubic-quintic Duffing equation such that , We were able to predict the number of limit cycles around the equilibrium and to develop a theoretical approach to chaos suppression in damped driven systems using Collatze like problem sequences , some new results regarding behavior of that sequence are presented.

Uses Mathlib (`ℚ`, `omega`, positivity-style facts via Core).
Status: `mainStatement` records the paper claim; only named lemmas are proved.
Source: https://arxiv.org/abs/2302.01904
-/

namespace MathlibAttack.Papers.Arxiv2302_01904

open MathlibAttack.Papers

def citation : String := "Zeraoulia Rafik, \"Amazing behavior and transition to chaos of some sequences using Collatz like problems and Quibic duffing\", arXiv:2302.01904 [2022]."

/-- Recorded cycle-exclusion shell (paper theorem not proved). -/
def mainStatement : Prop :=
  ∀ n : ℕ, 1 < n → ∀ k : ℕ, 0 < k → orbit k n = n →
    ∃ j : ℕ, j ≤ k ∧ orbit j n = 1

/-- Checked: the trivial 1-cycle returns. -/
theorem orbit_one_cycle : orbit 3 1 = 1 :=
  MathlibAttack.Papers.orbit_one_returns

end MathlibAttack.Papers.Arxiv2302_01904
