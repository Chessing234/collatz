import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Diedrich E., "The Collatz Conjecture: A Proof Through Inverse Generation Analysis", 2025.

Title: The Collatz Conjecture: A Proof Through Inverse Generation Analysis

Abstract (from harvested metadata, truncated):
We present a complete proof of the Collatz conjecture using a novel approach based on generator functions. By analyzing the inverse mappings of the Collatz function through carefully defined generator operations, we establish that all natural numbers must eventually reach 1 under the Collatz iteration. The proof relies on demonstrating fundamental incompatibilities between the requirements for divergent sequences and the constraints imposed by even-odd patterns in the natural numbers.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.20944/preprints202502.1308.v2
-/

namespace Collatz.Papers.Journal_10_20944_preprints202502_1308_v2

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Diedrich E., \"The Collatz Conjecture: A Proof Through Inverse Generation Analysis\", DOI:10.20944/preprints202502.1308.v2 [2025]."

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

end Collatz.Papers.Journal_10_20944_preprints202502_1308_v2
