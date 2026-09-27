import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Efrem Zambon, "Hieron I of Syracuse", 2012.

Title: Hieron I of Syracuse

Abstract (from harvested metadata, truncated):
Abstract Hieron I (d. 467 BCE ) was the brother of Gelon, and when the latter died (478/7) he became tyrant of Syracuse, greatly increasing the power and the influence of his city, both in Sicily and in southern Italy. He possessed great personal prestige also in mainland Greece: he won several times in the chariot races at Delphi and Olympia, and he made dedications in the two sanctuaries to celebrate his athletic triumphs and his military successes in the West.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.1002/9781444338386.wbeah09125
-/

namespace Collatz.Papers.Journal_10_1002_9781444338386_wbeah09125

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Efrem Zambon, \"Hieron I of Syracuse\", The Encyclopedia of Ancient History, DOI:10.1002/9781444338386.wbeah09125 [2012]."

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

end Collatz.Papers.Journal_10_1002_9781444338386_wbeah09125
