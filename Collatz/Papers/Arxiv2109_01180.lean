import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Quang-Nhat Le and Edward Smith, "Observations on cycles in a variant of the Collatz Graph", arXiv:2109.01180 [2021].

Title: Observations on cycles in a variant of the Collatz Graph

Abstract (from OpenAlex metadata, truncated):
It is well known that the Collatz Conjecture can be reinterpreted as the Collatz Graph with root vertex 1, asking whether all positive integers are within the tree generated. It is further known that any cycle in the Collatz Graph can be represented as a tuple, given that inputting them into a function outputs an odd positive integer; yet, it is an open question as to whether there exist any tuples not of the form $(2,2,...,2)$, thus disproving the Collatz Conjecture. In this paper, we explore a variant of the Collatz Graph, which allows the 3x+1 operation to be applied to both even and odd integers. We prove an analogous function for this variant, called the Loosened Collatz Function (LCF), and observe various properties of the LCF in relation to tuples and outputs. We prove a certain underlying unique factorisation monoid structure for tuples to the LCF and provide a geometric interpretation of satisfying tuples in higher dimensions. Research into this variant of the Collatz Graph ma

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2109.01180
-/

namespace Collatz.Papers.Arxiv2109_01180

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Quang-Nhat Le and Edward Smith, \"Observations on cycles in a variant of the Collatz Graph\", arXiv:2109.01180 [2021]."

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


end Collatz.Papers.Arxiv2109_01180
