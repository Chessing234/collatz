import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Yannis Almirantis and Wentian Li, "Rich dynamical behaviors from a digital reversal operation", arXiv:2408.02527 [2024].

Title: Rich dynamical behaviors from a digital reversal operation

Abstract (from OpenAlex metadata, truncated):
Repeatedly adding or subtracting the digital reversal to or from an integer, depending on which one is larger, can be treated as a dynamical system. On one hand, a three-digit version of this map running only two steps is the 1089 mathematical trick problem; on the other hand, this mapping can be compared to John Conway's reverse-add-then-sort (RATS) iteration, as well as the 3x+1 problem, also known as Collatz's map. We numerically run this map and find interesting dynamics, including limiting cycles with unusual periodicity and length-8 diverging trajectories.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2408.02527
-/

namespace Collatz.Papers.Arxiv2408_02527

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Yannis Almirantis and Wentian Li, \"Rich dynamical behaviors from a digital reversal operation\", arXiv:2408.02527 [2024]."

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


end Collatz.Papers.Arxiv2408_02527
