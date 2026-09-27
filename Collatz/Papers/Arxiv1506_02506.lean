import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Yanlong Zhou, "A New Way to Proof 3x+1 Problem", arXiv:1506.02506 [2015].

Title: A New Way to Proof 3x+1 Problem

Abstract (from OpenAlex metadata, truncated):
Under the 3x+1 problem, classified the number into four kind by mod 4. The four kind number can form a cycle base on 3x+b1 problem. Base on this cycle, if the number of kind number is zero the 3x+1 will be proofed.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/1506.02506
-/

namespace Collatz.Papers.Arxiv1506_02506

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Yanlong Zhou, \"A New Way to Proof 3x+1 Problem\", arXiv:1506.02506 [2015]."

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


end Collatz.Papers.Arxiv1506_02506
