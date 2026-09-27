import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Emily Gowers, "Augustus and ‘Syracuse’", 2010.

Title: Augustus and ‘Syracuse’

Abstract (from harvested metadata, truncated):
ABSTRACT Suetonius ( Aug. 72.2) records among the habits of Augustus his inclination to retreat from time to time to a place he called ‘Syracuse’ or his ‘technophuon’ (workshop). These names have been variously explained, without agreement. The paper argues that ‘Syracuse’ evokes a complex of associations beyond the obvious connection with Archimedes and his inventions. By recalling other well-known figures, such as Marcellus and Dionysius, as well as Augustus’ own experiences in Syracuse, the name of his den effectively encapsulates the courses of action available to the emperor as ruler and as private citizen.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.1017/s007543581000002x
-/

namespace Collatz.Papers.Journal_10_1017_s007543581000002x

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Emily Gowers, \"Augustus and ‘Syracuse’\", Journal of Roman Studies, DOI:10.1017/s007543581000002x [2010]."

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

end Collatz.Papers.Journal_10_1017_s007543581000002x
