import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Zeraoulia Rafik, "Amazing behavior and transition to chaos of some sequences using Collatz like problems and Quibic duffing", arXiv:2302.01904 [2022].

Title: Amazing behavior and transition to chaos of some sequences using Collatz like problems and Quibic duffing

Abstract (from OpenAlex metadata, truncated):
In this paper we shall show amazing behavior of some discrete maps using Collatze like problems and some advanced theories in analytic number theory and dynamical system,we have investigated the driven cubic-quintic Duffing equation such that , We were able to predict the number of limit cycles around the equilibrium and to develop a theoretical approach to chaos suppression in damped driven systems using Collatze like problem sequences , some new results regarding behavior of that sequence are presented.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2302.01904
-/

namespace Collatz.Papers.Arxiv2302_01904

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Zeraoulia Rafik, \"Amazing behavior and transition to chaos of some sequences using Collatz like problems and Quibic duffing\", arXiv:2302.01904 [2022]."

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


end Collatz.Papers.Arxiv2302_01904
