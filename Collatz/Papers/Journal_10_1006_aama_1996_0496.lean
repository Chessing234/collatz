import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for G. Venturini, "On a Generalization of the 3x+ 1 Problem", 1997.

Title: On a Generalization of the 3x+ 1 Problem

Abstract (from harvested metadata, truncated):
(No abstract in harvested metadata; statement recorded from title/venue only.)

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.1006/aama.1996.0496
-/

namespace Collatz.Papers.Journal_10_1006_aama_1996_0496

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "G. Venturini, \"On a Generalization of the 3x+ 1 Problem\", Advances in Applied Mathematics, DOI:10.1006/aama.1996.0496 [1997]."

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

end Collatz.Papers.Journal_10_1006_aama_1996_0496
