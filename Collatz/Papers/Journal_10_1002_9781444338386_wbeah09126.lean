import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Efrem Zambon, "Hieron II of Syracuse", 2012.

Title: Hieron II of Syracuse

Abstract (from harvested metadata, truncated):
Abstract Hieron II (306–215 BCE ) was tyrant and king of Syracuse from 270 to his death. He began his career as an officer of Pyrrhos' army during his expedition to Sicily, and when the king departed from the island in 276, he was appointed by the Syracusan people with the title of archon . To strengthen his position and gain the support of the upper classes he married Philistis, the daughter of Leptines, one of the leaders of the aristocracy. He encouraged the prosecution of the war against the carthaginians, more for propaganda reasons than with conviction; he was thus appointed as strategos autokrator and commander in chief of the army.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.1002/9781444338386.wbeah09126
-/

namespace Collatz.Papers.Journal_10_1002_9781444338386_wbeah09126

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Efrem Zambon, \"Hieron II of Syracuse\", The Encyclopedia of Ancient History, DOI:10.1002/9781444338386.wbeah09126 [2012]."

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

end Collatz.Papers.Journal_10_1002_9781444338386_wbeah09126
