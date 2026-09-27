import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Young, Chris, "Unlocking the Collatz Conjecture: Simple, Repeating Patterns Define the Path to Unity", 2025.

Title: Unlocking the Collatz Conjecture: Simple, Repeating Patterns Define the Path to Unity

Abstract (from harvested metadata, truncated):
AbstractThe Collatz Conjecture is notable for its simple formulation yet exceptional difficulty to prove. This paper introduces a novel framework for analyzing the conjecture, producing a set of patterns that illustrate how all starting numbers converge to 1. These patterns are organized in rows generated as starting numbers and their stopping times increase. Each pattern allows a term in a future sequence to be predicted from a previous term in the same row. As sequences grow, additional patterns emerge, showing lower terms at consistent steps for each repetition. This approach provides evidence supporting the convergence of all positive integers to 1 under the Collatz iteration and offers...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.17767433
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_17767433

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Young, Chris, \"Unlocking the Collatz Conjecture: Simple, Repeating Patterns Define the Path to Unity\", Zenodo, DOI:10.5281/zenodo.17767433 [2025]."

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

end Collatz.Papers.Journal_10_5281_zenodo_17767433
