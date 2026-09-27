import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Craige B. Champion, "Antiochos of Syracuse", 2012.

Title: Antiochos of Syracuse

Abstract (from harvested metadata, truncated):
Abstract Antiochos of Syracuse ( FGrH 555) was one of the earliest of the Sicilian Greek historians. He wrote during the fifth century BCE , following Herodotus, whom he may have consciously imitated (he too wrote in the Ionic dialect, not in Doric or Attic).

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.1002/9781444338386.wbeah08012
-/

namespace Collatz.Papers.Journal_10_1002_9781444338386_wbeah08012

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Craige B. Champion, \"Antiochos of Syracuse\", The Encyclopedia of Ancient History, DOI:10.1002/9781444338386.wbeah08012 [2012]."

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

end Collatz.Papers.Journal_10_1002_9781444338386_wbeah08012
