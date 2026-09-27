import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Miguel Cerdá Bennassar, "Structural Reduction of the Collatz Conjecture to the Dynamics of an Induced Function", 2026.

Title: Structural Reduction of the Collatz Conjecture to the Dynamics of an Induced Function

Abstract (from harvested metadata, truncated):
This work develops a structural reformulation of the Collatz conjecture based on the decomposition of trajectories into maximal odd segments and the introduction of an induced map acting on their segment-starts. The conjecture is shown to be equivalent to an eventual descent property for this induced function. Odd integers of the form 4n+1 are identified as structural critical points (“portals”) where binary information is reorganized. The analysis isolates the core difficulty of the problem, reducing it to a precise arithmetic question concerning the distribution of 2-adic valuations of certain exponential expressions. This is the English version of the paper originally written in Spanish....

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.18611196
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_18611196

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Miguel Cerdá Bennassar, \"Structural Reduction of the Collatz Conjecture to the Dynamics of an Induced Function\", Zenodo, DOI:10.5281/zenodo.18611196 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_18611196
