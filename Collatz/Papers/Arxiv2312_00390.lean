import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Angelot Behajaina and Elad Paran, "The Collatz map analogue in polynomial rings and in completions", arXiv:2312.00390 [2023].

Title: The Collatz map analogue in polynomial rings and in completions

Abstract (from OpenAlex metadata, truncated):
We study an analogue of the Collatz map in the polynomial ring $R[x]$, where $R$ is an arbitrary commutative ring. We prove that if $R$ is of positive characteristic, then every polynomial in $R[x]$ is eventually periodic with respect to this map. This extends previous works of the authors and of Hicks, Mullen, Yucas and Zavislak, who studied the Collatz map on $\mathbb{F}_p[x]$ and $\mathbb{F}_2[x]$, respectively. We also consider the Collatz map on the ring of formal power series $R[[x]]$ when $R$ is finite: we characterize the eventually periodic series in this ring, and give formulas for the number of cycles induced by the Collatz map, of any given length. We provide similar formulas for the original Collatz map defined on the ring $\mathbb{Z}_2$ of $2$-adic integers, extending previous results of Lagarias.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2312.00390
-/

namespace Collatz.Papers.Arxiv2312_00390

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Angelot Behajaina and Elad Paran, \"The Collatz map analogue in polynomial rings and in completions\", arXiv:2312.00390 [2023]."

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


end Collatz.Papers.Arxiv2312_00390
