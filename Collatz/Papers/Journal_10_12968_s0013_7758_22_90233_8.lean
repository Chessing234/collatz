import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Nick Smith, "<b>ARCHIMEDES OF SYRACUSE</b>", 2020.

Title: <b>ARCHIMEDES OF SYRACUSE</b>

Abstract (from harvested metadata, truncated):
Remembered today primarily for inventing a rudimentary screw pump, there is so much more to the Ancient Greek polymath Archimedes of Syracuse, the greatest scientist of antiquity.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.12968/s0013-7758(22)90233-8
-/

namespace Collatz.Papers.Journal_10_12968_s0013_7758_22_90233_8

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Nick Smith, \"<b>ARCHIMEDES OF SYRACUSE</b>\", The Engineer, DOI:10.12968/s0013-7758(22)90233-8 [2020]."

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

end Collatz.Papers.Journal_10_12968_s0013_7758_22_90233_8
