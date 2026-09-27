import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Caldin, Andrew Stewart, "Collatz Conjecture Unproven; Olympiad Algebra Solved Without New Insights — E8 Intelligence Research", 2026.

Title: Collatz Conjecture Unproven; Olympiad Algebra Solved Without New Insights — E8 Intelligence Research

Abstract (from harvested metadata, truncated):
FINDING: Collatz Conjecture remains unsolved; no progress on impossibility proofs. | MATH: f(n) = n/2 if n even, 3n+1 if n odd; no closed-form solution or invariant found. | CONNECTION: None—no geometric ratios, symmetries, or base-60 links. | DEPTH: 1 (no new mathematical essence extracted). FINDING: Olympiad algebra problem solved (specific value of x). | MATH: Equation not provided; typical form a^x + b^x = c. | CONNECTION: None—standard algebraic manipulation, no harmonic ratios. | DEPTH: 1 (trivial, no universal insight). FINDING: Summary of unsolved math problems (likely Riemann Hypothesis, P vs NP, etc.). | MATH: No specific equations given. | CONNECTION: None—general overview, no geo...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.21617623
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_21617623

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Caldin, Andrew Stewart, \"Collatz Conjecture Unproven; Olympiad Algebra Solved Without New Insights — E8 Intelligence Research\", Zenodo, DOI:10.5281/zenodo.21617623 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_21617623
