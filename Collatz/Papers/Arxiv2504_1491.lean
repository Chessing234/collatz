import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Kazuhito Owada, "Collatz Trees: A Structural Framework for Understanding the 3x+1 Problem", arXiv:2504.1491 [2025].

Title: Collatz Trees: A Structural Framework for Understanding the 3x+1 Problem

Abstract (from OpenAlex metadata, truncated):
The Collatz Conjecture remains one of the most enduring unsolved problems in mathematics, despite being based on an extraordinarily simple rule. Given any natural number n, the conjecture posits that repeatedly applying the operation—dividing by 2 if even, or multiplying by 3 and adding 1 if odd—will eventually result in the number 1.This paper develops a structural perspective by proposing the Collatz Tree as a framework to organize and visualize natural numbers. Each branch is the geometric ray {k·2^b} for an odd core k, and the trunk is the ray from 1. We introduce a trunk–branch indexing that bijects N with Z≥0 × Z≥0.Algebraically, we encode Collatz steps as affine maps and prove the absence of nontrivial finite cycles for a three-way map T. Through a bridge theorem, this implies the same for the standard accelerated map A(n) = (3n+1)/2^ν₂(3n+1) on odd integers. Thus, the global Coll

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2504.1491
-/

namespace Collatz.Papers.Arxiv2504_1491

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Kazuhito Owada, \"Collatz Trees: A Structural Framework for Understanding the 3x+1 Problem\", arXiv:2504.1491 [2025]."

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


end Collatz.Papers.Arxiv2504_1491
