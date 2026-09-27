import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Al_ibraheem, "The final proof of Collatz conjecture", 2026.

Title: The final proof of Collatz conjecture

Abstract (from harvested metadata, truncated):
This historic paper presents the first comprehensive and definitive proof of the validity of the Collatz Conjecture through an innovative partition of odd numbers into three disjoint sets. The approach begins by applying the Collatz function to set V (numbers congruent to 5 modulo 12) and rigorously proving that it satisfies the relation f(V) = V ∪ {1}. From this relation, a simple mathematical induction establishes the convergence of all odd numbers—except multiples of 3—toward 1. The result is then readily generalized to multiples of 3 and to even numbers, thereby conclusively proving the Collatz Conjecture. This work is identical to the version previously published on viXra: https://vixra.org/pdf/2510.0073v5.pdf

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.18736343
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_18736343

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Al_ibraheem, \"The final proof of Collatz conjecture\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.18736343 [2026]."

/-- Recorded generalization-style claim shell; the paper's theorem is not proved here.
This placeholder is the standard Collatz conjecture proposition. -/
def mainStatement : Prop := Collatz.CollatzConjecture

/-- Checked bridge facts only. -/
theorem step_one_eq : Collatz.step 1 = 4 := Collatz.step_one

theorem step_two_eq : Collatz.step 2 = 1 := Collatz.step_two

/-- Checked: every power of two reaches `1` (Mathlib-copied parity/division facts). -/
theorem powers_of_two_reach_one (k : Nat) :
    ∃ t : Nat, Collatz.orbit t (2 ^ k) = 1 :=
  Collatz.Papers.MathlibCopied.orbit_pow_two_reaches_one k

end Collatz.Papers.Journal_10_5281_zenodo_18736343
