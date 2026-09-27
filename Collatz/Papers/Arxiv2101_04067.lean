import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Darrell Cox et al., "Collatz Cycles and $3n+c$ Cycles", arXiv:2101.04067 [2021].

Title: Collatz Cycles and $3n+c$ Cycles

Abstract (from OpenAlex metadata, truncated):
Halbeisen and Hungerbuhler determined optimal bounds for the length of rational Collatz cycles. Their methods are extended to $3n+c$ cycles. Another sequence having properties similar to those of Riemann zeta function zeros is introduced.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2101.04067
-/

namespace Collatz.Papers.Arxiv2101_04067

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Darrell Cox et al., \"Collatz Cycles and $3n+c$ Cycles\", arXiv:2101.04067 [2021]."

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


end Collatz.Papers.Arxiv2101_04067
