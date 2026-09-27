import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Keith R. Matthews, "Some Borel measures associated with the generalized Collatz mapping", 1992.

Title: Some Borel measures associated with the generalized Collatz mapping

Abstract (from harvested metadata, truncated):
This paper is a continuation of a recent paper [2], in which the authors studied some Markov matrices arising from a mapping T:ℤ → ℤ, which generalizes the famous 3x+1 mapping of Collatz. We extended T to a mapping of the polyadic numbers $\widehat{ℤ}$ an

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.4064/cm-63-2-191-202
-/

namespace Collatz.Papers.Journal_10_4064_cm_63_2_191_202

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Keith R. Matthews, \"Some Borel measures associated with the generalized Collatz mapping\", Colloquium Mathematicum, DOI:10.4064/cm-63-2-191-202 [1992]."

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

end Collatz.Papers.Journal_10_4064_cm_63_2_191_202
