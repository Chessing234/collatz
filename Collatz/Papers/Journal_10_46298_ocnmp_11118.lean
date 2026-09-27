import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Fabio Briscese and F. Calogero, "Conjectures analogous to the Collatz conjecture", 2024.

Title: Conjectures analogous to the Collatz conjecture

Abstract (from harvested metadata, truncated):
In this paper we introduce some conjectures analogous to the well-known Collatz conjecture.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.46298/ocnmp.11118
-/

namespace Collatz.Papers.Journal_10_46298_ocnmp_11118

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Fabio Briscese and F. Calogero, \"Conjectures analogous to the Collatz conjecture\", Open Communications in Nonlinear Mathematical Physics, DOI:10.46298/ocnmp.11118 [2024]."

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

end Collatz.Papers.Journal_10_46298_ocnmp_11118
