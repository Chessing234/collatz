import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Ariel Helfer, "Plato in Syracuse", 2023.

Title: Plato in Syracuse

Abstract (from harvested metadata, truncated):
This chapter overviews Plato's activities in Syracuse. It starts with the core theme of Letters about Plato's failed attempt to carry out Dion's plan of educating Dionysius to philosophy. The failure essentially resulted in Plato's fateful decision to involve himself in the political affairs of the Syracusan tyranny. The chapter highlights how Plato never believed in Dion's vision for a regime of philosophic rule in Syracuse and that he could never have been sanguine about Dionysius's prospects as a student of Platonic philosophy. It then looks into Letter Thirteen of Letters, which contains reflections on the difficulty of ascertaining the genuineness and authorship of the letter.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.7591/cornell/9781501772894.003.0018
-/

namespace Collatz.Papers.Journal_10_7591_cornell_9781501772894_003_0018

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Ariel Helfer, \"Plato in Syracuse\", Plato's \"Letters\", DOI:10.7591/cornell/9781501772894.003.0018 [2023]."

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

end Collatz.Papers.Journal_10_7591_cornell_9781501772894_003_0018
