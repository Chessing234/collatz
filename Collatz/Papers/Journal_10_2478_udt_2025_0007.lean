import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Mojtaba Moniri, "Ramsey-Collatz Correlation and Some Extremal Combinatorics, along with Ramsey-Mahler Rare Concurrencies", 2025.

Title: Ramsey-Collatz Correlation and Some Extremal Combinatorics, along with Ramsey-Mahler Rare Concurrencies

Abstract (from harvested metadata, truncated):
Abstract For a ternary tree T of depth n with 0-1 labeled edges, its weight f ( T ) is the least number of path labels among binary subtrees. The maximum f ( n ), over all labelings, of these weights starts with 1,2,3,4,8. We show f (6) ≥ 12, but focus on depth 5 (with 2 363 trees). We approximate the percentages for weights 1–8: 0, 1.04, 23.6, 55.0, 18.8, 1.54, 0, 0; our linked supplements include thousands of mined trees of rare weights 7-8. Our next products additionally relate to Mahler’s 3 2 {3 \over 2} -problem and large stopping times showing a real number is not a Z-number. Our version is iterated multiplication of integers by 2 3 {2 \over 3} . For a certain sequence of integer intervals, we present a choice function. Our interval I g has left endpoint a ( g ) = min { k | { g ⋅ (...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.2478/udt-2025-0007
-/

namespace Collatz.Papers.Journal_10_2478_udt_2025_0007

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Mojtaba Moniri, \"Ramsey-Collatz Correlation and Some Extremal Combinatorics, along with Ramsey-Mahler Rare Concurrencies\", Uniform distribution theory, DOI:10.2478/udt-2025-0007 [2025]."

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

end Collatz.Papers.Journal_10_2478_udt_2025_0007
