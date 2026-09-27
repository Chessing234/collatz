import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Cerdà Bennassar, Miquel, "THE COLLATZ CONJECTURE interpreted with graph theory and the properties of the digital root of natural numbers.", 2023.

Title: THE COLLATZ CONJECTURE interpreted with graph theory and the properties of the digital root of natural numbers.

Abstract (from harvested metadata, truncated):
In this paper I present a study of the Collatz problem and its conjecture using graph theory and the properties of the digital root of natural numbers.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.6084/m9.figshare.22217026
-/

namespace Collatz.Papers.Journal_10_6084_m9_figshare_22217026

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Cerdà Bennassar, Miquel, \"THE COLLATZ CONJECTURE interpreted with graph theory and the properties of the digital root of natural numbers.\", figshare, DOI:10.6084/m9.figshare.22217026 [2023]."

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

end Collatz.Papers.Journal_10_6084_m9_figshare_22217026
