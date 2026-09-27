import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Charles L. Webber, "Polar recurrence plots on Collatz sequences devoid of exact recurrences", 2026.

Title: Polar recurrence plots on Collatz sequences devoid of exact recurrences

Abstract (from harvested metadata, truncated):
(No abstract in harvested metadata; statement recorded from title/venue only.)

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.1140/epjs/s11734-026-02343-6
-/

namespace Collatz.Papers.Journal_10_1140_epjs_s11734_026_02343_6

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Charles L. Webber, \"Polar recurrence plots on Collatz sequences devoid of exact recurrences\", The European Physical Journal Special Topics, DOI:10.1140/epjs/s11734-026-02343-6 [2026]."

/-- Recorded main claim shell (structural); the paper's theorem is not proved here.
This placeholder is the standard Collatz conjecture proposition. -/
def mainStatement : Prop := Collatz.CollatzConjecture

/-- Checked bridge facts only. -/
theorem step_one_eq : Collatz.step 1 = 4 := Collatz.step_one

theorem step_two_eq : Collatz.step 2 = 1 := Collatz.step_two

/-- Checked: every power of two reaches `1` (Mathlib-copied parity/division facts). -/
theorem powers_of_two_reach_one (k : Nat) :
    ∃ t : Nat, Collatz.orbit t (2 ^ k) = 1 :=
  Collatz.Papers.MathlibCopied.orbit_pow_two_reaches_one k

end Collatz.Papers.Journal_10_1140_epjs_s11734_026_02343_6
