import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Andrew Gleibman, "Reformulating Collatz Conjecture Without Numerical Concepts", 2023.

Title: Reformulating Collatz Conjecture Without Numerical Concepts

Abstract (from harvested metadata, truncated):
In this paper, we reformulate the algorithm for calculating a sequence of numbers, related to the Collatz conjecture, in such a way that it does not apply any number-related concepts. Instead of the number-related mathematics, a set of simple and intuitive string processing rules is applied. In order to do this, we generalize the traditional base-b numerical systems, aiming at a simplification of the involved 3∙n+1 operation. The behavior of the reformulated algorithm is analyzed for various kinds of input strings, including special strings and some very large ones.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.31219/osf.io/3zagr
-/

namespace Collatz.Papers.Journal_10_31219_osf_io_3zagr

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Andrew Gleibman, \"Reformulating Collatz Conjecture Without Numerical Concepts\", DOI:10.31219/osf.io/3zagr [2023]."

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

end Collatz.Papers.Journal_10_31219_osf_io_3zagr
