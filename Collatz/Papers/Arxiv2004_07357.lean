import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Hassan Sedaghat, "Bounded Orbits of Quadratic Collatz-type Recursions", arXiv:2004.07357 [2020].

Title: Bounded Orbits of Quadratic Collatz-type Recursions

Abstract (from OpenAlex metadata, truncated):
We characterize all bounded orbits of two similar Collatz-type quadratic mappings of the set of non-negative integers. In one case, where cycles of all possible lengths may occur, an orbit is bounded if and only if it reaches a cycle. For the other map we prove that every bounded orbit must reach 0 (in particular, there are no cycles).

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2004.07357
-/

namespace Collatz.Papers.Arxiv2004_07357

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Hassan Sedaghat, \"Bounded Orbits of Quadratic Collatz-type Recursions\", arXiv:2004.07357 [2020]."

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


end Collatz.Papers.Arxiv2004_07357
