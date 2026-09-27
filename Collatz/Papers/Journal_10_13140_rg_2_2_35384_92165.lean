import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Peter Cookson, "Linking Collatz Conjecture, Fermat's last theorem and Claude Shannon's information Equation to form an analogy for Market activity: harmonising Marxist and Thomas Sowell's visions of dynamic markets 1 Recasting Collatz Conjecture to our Structural Analysis", 2026.

Title: Linking Collatz Conjecture, Fermat's last theorem and Claude Shannon's information Equation to form an analogy for Market activity: harmonising Marxist and Thomas Sowell's visions of dynamic markets 1 Recasting Collatz Conjecture to our Structural Analysis

Abstract (from harvested metadata, truncated):
(No abstract in harvested metadata; statement recorded from title/venue only.)

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.13140/rg.2.2.35384.92165
-/

namespace Collatz.Papers.Journal_10_13140_rg_2_2_35384_92165

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Peter Cookson, \"Linking Collatz Conjecture, Fermat's last theorem and Claude Shannon's information Equation to form an analogy for Market activity: harmonising Marxist and Thomas Sowell's visions of dynamic markets 1 Recasting Collatz Conjecture to our Structural Analysis\", DOI:10.13140/rg.2.2.35384.92165 [2026]."

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

end Collatz.Papers.Journal_10_13140_rg_2_2_35384_92165
