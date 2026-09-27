import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Yagub N. Aliyev, "On integer linear combinations of terms of rational cycles for the generalized 3x+1 problem", arXiv:2307.11990 [2023].

Title: On integer linear combinations of terms of rational cycles for the generalized 3x+1 problem

Abstract (from OpenAlex metadata, truncated):
In the paper, some special linear combinations of the terms of rational cycles of generalized Collatz sequences are studied. It is proved that if the coefficients of the linear combinations satisfy some conditions then these linear combinations are integers. The discussed results are demonstrated on some examples. In some particular cases the obtained results can be used to explain some patterns of digits in $p$-adic representations of the terms of the rational cycles.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2307.11990
-/

namespace Collatz.Papers.Arxiv2307_11990

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Yagub N. Aliyev, \"On integer linear combinations of terms of rational cycles for the generalized 3x+1 problem\", arXiv:2307.11990 [2023]."

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


end Collatz.Papers.Arxiv2307_11990
