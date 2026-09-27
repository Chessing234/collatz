import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Paparella, Pietro, "A matricial view of the Collatz conjecture", arXiv:2406.08498 [2024].

Title: A matricial view of the Collatz conjecture

Abstract (from OpenAlex metadata, truncated):
In this note, it is shown that the nilpotency of submatrices of a certain class of adjacency matrices is equivalent to the aperiodic Collatz conjecture.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2406.08498
-/

namespace Collatz.Papers.Arxiv2406_08498

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Paparella, Pietro, \"A matricial view of the Collatz conjecture\", arXiv:2406.08498 [2024]."

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

end Collatz.Papers.Arxiv2406_08498
