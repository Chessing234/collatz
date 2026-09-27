import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Chen, Yongkuo, "The Inverse-Generated Set of Convergent Numbers in the Collatz Conjecture", 2025.

Title: The Inverse-Generated Set of Convergent Numbers in the Collatz Conjecture

Abstract (from harvested metadata, truncated):
This set presents a constructive recursive definition for the set of all Collatz-convergent positive integers. The process begins with powers of 2 and iteratively applies inverse operations under strict modular conditions (mod 6 ≡ 4), forming a tree structure rooted at 1. The union of all levels is conjectured to coincide with the full set of Collatz-converging numbers.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.6084/m9.figshare.29037818
-/

namespace Collatz.Papers.Journal_10_6084_m9_figshare_29037818

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Chen, Yongkuo, \"The Inverse-Generated Set of Convergent Numbers in the Collatz Conjecture\", figshare, DOI:10.6084/m9.figshare.29037818 [2025]."

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

end Collatz.Papers.Journal_10_6084_m9_figshare_29037818
