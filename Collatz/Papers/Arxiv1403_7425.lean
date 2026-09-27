import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Kerstin Andersson, "On the Boundedness of Collatz Sequences", arXiv:1403.7425 [2014].

Title: On the Boundedness of Collatz Sequences

Abstract (from OpenAlex metadata, truncated):
An attempt to come closer to a resolution of the Collatz conjecture is presented. The central idea is the formation of a tree consisting of positive odd numbers with number 1 as root. Functions for generating the tree from the root are presented and paths from nodes to the root are given by modified Collatz sequences (with the even numbers omitted). The Collatz problem is thus reduced to showing that all positive odd numbers are present in the tree. The main result is the proof of the boundedness of Collatz sequences. With the even numbers omitted they either end up in the number 1 (convergence) or in a repetitive cycle of numbers (divergence). The existence/non-existence of cycles in Collatz sequences (with the even numbers omitted) is still an open question.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/1403.7425
-/

namespace Collatz.Papers.Arxiv1403_7425

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Kerstin Andersson, \"On the Boundedness of Collatz Sequences\", arXiv:1403.7425 [2014]."

/-- Recorded nontrivial-cycle exclusion shell; the paper's theorem is not proved. -/
def mainStatement : Prop :=
  ∀ n : Nat, 1 < n → ∀ k : Nat, 0 < k → Collatz.orbit k n = n →
    ∃ j : Nat, j ≤ k ∧ Collatz.orbit j n = 1

/-- Checked: the trivial cycle through `1` returns after three steps. -/
theorem orbit_one_returns : Collatz.orbit 3 1 = 1 :=
  (Collatz.Papers.MathlibCopied.trivial_cycle).1

theorem step_branches_on_cycle :
    Collatz.step 1 = 4 ∧ Collatz.step 4 = 2 ∧ Collatz.step 2 = 1 := by
  have h := Collatz.Papers.MathlibCopied.trivial_cycle
  exact ⟨h.2.1, h.2.2.1, h.2.2.2⟩

end Collatz.Papers.Arxiv1403_7425
