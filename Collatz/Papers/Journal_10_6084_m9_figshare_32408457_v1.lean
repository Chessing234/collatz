import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Xiangyu Lu, "The Shark Function and Iterative Convergence Structure: A New Framework for Analyzing the Collatz Problem", 2026.

Title: The Shark Function and Iterative Convergence Structure: A New Framework for Analyzing the Collatz Problem

Abstract (from harvested metadata, truncated):
This work presents an original theoretical study of the Collatz conjecture. It defines the Shark Function and related new concepts, establishes a proposition splitting analysis framework, and completes systematic logical reasoning and proof for the iterative convergence problem. This preprint is submitted for open academic archiving and priority record.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.6084/m9.figshare.32408457.v1
-/

namespace Collatz.Papers.Journal_10_6084_m9_figshare_32408457_v1

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Xiangyu Lu, \"The Shark Function and Iterative Convergence Structure: A New Framework for Analyzing the Collatz Problem\", Figshare, DOI:10.6084/m9.figshare.32408457.v1 [2026]."

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

end Collatz.Papers.Journal_10_6084_m9_figshare_32408457_v1
