import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Aya Thompson, "The Collatz Conjecture, While F(x) = 1 as X → ∞", 2023.

Title: The Collatz Conjecture, While F(x) = 1 as X → ∞

Abstract (from harvested metadata, truncated):
The Collatz Conjecture is one of the most famous unsolved problems in mathematics, and the most basic unsolved one. Our contribution is to show that the problem can be split into two dimensions, each dimension can be represented by a single function that can then be shown to not form a loop, other than the established X = 1. The lack of other loops in the collatz conjecture is direct proof of the conjecture itself.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.31219/osf.io/dhrnv
-/

namespace Collatz.Papers.Journal_10_31219_osf_io_dhrnv

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Aya Thompson, \"The Collatz Conjecture, While F(x) = 1 as X → ∞\", DOI:10.31219/osf.io/dhrnv [2023]."

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

end Collatz.Papers.Journal_10_31219_osf_io_dhrnv
