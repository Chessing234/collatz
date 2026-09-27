import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Çiftçi Ü., "Controlling large numbers with smaller ones in the Collatz conjecture: an outline", 2023.

Title: Controlling large numbers with smaller ones in the Collatz conjecture: an outline

Abstract (from harvested metadata, truncated):
Abstract We report on our observations and progress on the 3n + 1 problem, and then point out keys to a proof. Our consideration depends on keeping track of the number of digits of binary numbers by looking at examples. We show that for a large number, it is possible to understand the long time behaviour by looking at the ending digits. 2010 MSC: 00A05, 11-04

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.21203/rs.3.rs-2692111/v1
-/

namespace Collatz.Papers.Journal_10_21203_rs_3_rs_2692111_v1

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Çiftçi Ü., \"Controlling large numbers with smaller ones in the Collatz conjecture: an outline\", DOI:10.21203/rs.3.rs-2692111/v1 [2023]."

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

end Collatz.Papers.Journal_10_21203_rs_3_rs_2692111_v1
