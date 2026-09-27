import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Pradhyumnaa Ganapathi Subramanian, "Two Paths to Convergence: Observations of the Collatz Conjecture", 2024.

Title: Two Paths to Convergence: Observations of the Collatz Conjecture

Abstract (from harvested metadata, truncated):
The Collatz conjecture, a longstanding unsolved problem in number theory, suggests that starting with any positive integer n, applying the rule n/2 for even numbers or 3n+1 for odd numbers will eventually lead to the number 1. This paper presents insights into the convergence behavior of the Collatz conjecture. Specifically, numbers not in the form of 2^n must follow one of two distinct pathways towards convergence: they either reach a number expressible as (4^m - 1)/3 or (10*(4^(m-1)) - 1)/3 for integer m &amp;gt;= 1 within their Collatz sequence to converge to 1. Reaching one of these forms in the Collatz sequence is essential for convergence to 1. Conversely, if a number reaches one of th...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.31219/osf.io/25w7b
-/

namespace Collatz.Papers.Journal_10_31219_osf_io_25w7b

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Pradhyumnaa Ganapathi Subramanian, \"Two Paths to Convergence: Observations of the Collatz Conjecture\", DOI:10.31219/osf.io/25w7b [2024]."

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

end Collatz.Papers.Journal_10_31219_osf_io_25w7b
