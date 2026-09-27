import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Eldar Sultanow et al., "Introducing a Finite State Machine for Processing Collatz Sequences", 2017.

Title: Introducing a Finite State Machine for Processing Collatz Sequences

Abstract (from harvested metadata, truncated):
The present work will introduce a Finite State Machine (FSM) that processes any Collatz Sequence; further, we will endeavor to investigate its behavior in relationship to transformations of a special infinite input. Moreover, we will prove that the machine’s word transformation is equivalent to the standard Collatz number transformation and then discuss the possibilities for utilizing this approach for solving similar problems. The benefit of this approach is that the investigation of the word transformation performed by the Finite State Machine is less complicated than the traditional number-theoretical transformation.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.18052/www.scipress.com/ijpms.19.10
-/

namespace Collatz.Papers.Journal_10_18052_www_scipress_com_ijpms_19_10

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Eldar Sultanow et al., \"Introducing a Finite State Machine for Processing Collatz Sequences\", International Journal of Pure Mathematical Sciences, DOI:10.18052/www.scipress.com/ijpms.19.10 [2017]."

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

end Collatz.Papers.Journal_10_18052_www_scipress_com_ijpms_19_10
