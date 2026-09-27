import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Caldin, Andrew Stewart, "Collatz Conjecture Proved Algorithmically Undecidable, Revealing Computational Limits — E8 Intelligence Research", 2026.

Title: Collatz Conjecture Proved Algorithmically Undecidable, Revealing Computational Limits — E8 Intelligence Research

Abstract (from harvested metadata, truncated):
FINDING: Collatz Conjecture is a simple iterative arithmetic problem proven to be algorithmically undecidable in general, highlighting limits of computation. | MATH: For n even: n→n/2; for n odd: n→3n+1. No closed-form solution or invariant found. No known constants or ratios emerge from the iteration. | CONNECTION: No direct link to geometric harmony ratios (0.382, 0.618, 0.786, 1.618, 2.618), base-60, or crystallographic symmetries. The problem is purely number-theoretic and discrete. | DEPTH: 3 — Important for computability theory, but no geometric or harmonic structure revealed. FINDING: Hilbert's Decision Problem (Entscheidungsproblem) proven unsolvable by Turing — no algorithm can deci...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.21897929
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_21897929

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Caldin, Andrew Stewart, \"Collatz Conjecture Proved Algorithmically Undecidable, Revealing Computational Limits — E8 Intelligence Research\", Zenodo, DOI:10.5281/zenodo.21897929 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_21897929
