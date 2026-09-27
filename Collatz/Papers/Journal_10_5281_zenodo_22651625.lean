import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Michelle Shiu, "Collatz 101: An Experimental Investigation of the Collatz Conjecture", 2026.

Title: Collatz 101: An Experimental Investigation of the Collatz Conjecture

Abstract (from harvested metadata, truncated):
The Collatz Conjecture, also known as the 3x+1 problem, is one of mathematics' most famous unsolved problems. Despite its simple definition---take any positive integer, divide it by 2 if even, or multiply by 3 and add 1 if odd---no one has been able to prove that every sequence eventually reaches 1. This paper presents an experimental investigation of the conjecture using Python. I analyze stopping times, maximum heights, and sequence behavior across various ranges. My results show that stopping times do not increase smoothly with starting value, that consecutive numbers can have dramatically different behaviors, and that sequences from different starting points frequently merge onto the sam...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.22651625
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_22651625

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Michelle Shiu, \"Collatz 101: An Experimental Investigation of the Collatz Conjecture\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.22651625 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_22651625
