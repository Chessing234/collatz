import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Qiu, Changming, "On the 3n+1 Problem: Binary Carry Dynamics, Pipeline Model, and a Reduction of the Collatz Conjecture to a Combinatorial Hypothesis", 2026.

Title: On the 3n+1 Problem: Binary Carry Dynamics, Pipeline Model, and a Reduction of the Collatz Conjecture to a Combinatorial Hypothesis

Abstract (from harvested metadata, truncated):
This manuscript provides a rigorous combinatorial reduction of the Collatz conjecture via original binary carry dynamics and pipeline orbit decomposition. We construct a state potential function governed by bit-level carry propagation parameters P and M, and prove that the entire 3n+1 conjecture reduces to a single local contraction hypothesis on finite pipeline units. All previous definitional errors and logical ambiguities are fully corrected in this refined version.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.21600761
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_21600761

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Qiu, Changming, \"On the 3n+1 Problem: Binary Carry Dynamics, Pipeline Model, and a Reduction of the Collatz Conjecture to a Combinatorial Hypothesis\", DOI:10.5281/zenodo.21600761 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_21600761
