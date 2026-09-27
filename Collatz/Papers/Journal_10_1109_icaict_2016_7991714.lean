import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Yagub N. Aliyev, "Existence of repetitions of digits in the construction of periodic sequences related to 3x+1 problem: Proof of the theorem on the periods in the 3-adic representation of terms of periodic sequences that appear in Collatz problem", 2016.

Title: Existence of repetitions of digits in the construction of periodic sequences related to 3x+1 problem: Proof of the theorem on the periods in the 3-adic representation of terms of periodic sequences that appear in Collatz problem

Abstract (from harvested metadata, truncated):
(No abstract in harvested metadata; statement recorded from title/venue only.)

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.1109/icaict.2016.7991714
-/

namespace Collatz.Papers.Journal_10_1109_icaict_2016_7991714

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Yagub N. Aliyev, \"Existence of repetitions of digits in the construction of periodic sequences related to 3x+1 problem: Proof of the theorem on the periods in the 3-adic representation of terms of periodic sequences that appear in Collatz problem\", DOI:10.1109/icaict.2016.7991714 [2016]."

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

end Collatz.Papers.Journal_10_1109_icaict_2016_7991714
