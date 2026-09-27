import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Robert H. Nichols, "A Collatz Conjecture Proof", arXiv:2112.07361 [2021].

Title: A Collatz Conjecture Proof

Abstract (from OpenAlex metadata, truncated):
We represent the generalized Collatz function with the recursive ruler function r(2n) = r(n) + 1 and r(2n + 1) = 1. We generate even-only and odd-only Collatz subsequences that contain significantly fewer elements term by term, to 2 and 1, respectively, than are present in the original 3n + 1 and the Terras-modified Collatz sequences. We show that a nonlinear, coupled system of difference equations yields a complete acyclic (except for the trivial cycle) Collatz tree in odds not divisible by 3 with root vertex 1. We construct a complete Collatz tree with the axiom of choice and prove the Collatz conjecture.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2112.07361
-/

namespace Collatz.Papers.Arxiv2112_07361

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Robert H. Nichols, \"A Collatz Conjecture Proof\", arXiv:2112.07361 [2021]."

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


end Collatz.Papers.Arxiv2112_07361
