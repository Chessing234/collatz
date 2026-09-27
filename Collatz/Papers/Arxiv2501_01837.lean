import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Eyob Solomon Getachew, "The Collatz Infinite Tree: Inclusion of Natural Numbers and Nonexistence of Nontrivial Cycles", arXiv:2501.01837 [2025].

Title: The Collatz Infinite Tree: Inclusion of Natural Numbers and Nonexistence of Nontrivial Cycles

Abstract (from OpenAlex metadata, truncated):
The complete proof of the Collatz Conjecture is presented by constructing the Collatz infinite tree through inverse transformations of the Collatz equation. The inclusion of all natural numbers in the tree and the nonexistence of cycles other than the trivial 1-2-4-1 cycle are shown. For any given natural number N, specific branches of the tree are shown to contain all natural numbers up to N. This result is generalized for all N using mathematical induction, confirming the completeness of the tree. Analysis of the tree's structure demonstrates that the only cycle present is the trivial 1-2-4-1 cycle in the backbone. All conditions necessary for the existence of nontrivial cycles are shown to be unsatisfiable, affirming the conjecture's validity. An algorithm is also designed to construct the subtree containing all natural numbers up to any specified N, offering a practical complement to

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2501.01837
-/

namespace Collatz.Papers.Arxiv2501_01837

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Eyob Solomon Getachew, \"The Collatz Infinite Tree: Inclusion of Natural Numbers and Nonexistence of Nontrivial Cycles\", arXiv:2501.01837 [2025]."

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

end Collatz.Papers.Arxiv2501_01837
