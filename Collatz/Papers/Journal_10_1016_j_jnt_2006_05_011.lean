import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for John L. Simons, "A simple (inductive) proof for the non-existence of 2-cycles of the 3x+1 problem", 2006.

Title: A simple (inductive) proof for the non-existence of 2-cycles of the 3x+1 problem

Abstract (from harvested metadata, truncated):
(No abstract in harvested metadata; statement recorded from title/venue only.)

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.1016/j.jnt.2006.05.011
-/

namespace Collatz.Papers.Journal_10_1016_j_jnt_2006_05_011

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "John L. Simons, \"A simple (inductive) proof for the non-existence of 2-cycles of the 3x+1 problem\", Journal of Number Theory, DOI:10.1016/j.jnt.2006.05.011 [2006]."

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

end Collatz.Papers.Journal_10_1016_j_jnt_2006_05_011
