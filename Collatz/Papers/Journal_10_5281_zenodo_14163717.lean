import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Bagchi, Aditya, "Collatz Conjecture :Deterministic Approach To Prove Universality", 2024.

Title: Collatz Conjecture :Deterministic Approach To Prove Universality

Abstract (from harvested metadata, truncated):
Essence of the Paper:a) There are 8 types of odd integers by the last four bits of their binary expressions or by the modulo residue of 16 such that: 16k + m (m = 1, 3, 5, 7, 9, 11, 13, 15) b) There are 8 types of even integers in the same way: 16k + n (n = 0, 2, 4, 6, 8, 10, 12, 14) c) The even integers are being considered as intermediates between two odd successive integers in a Collatz sequence. d) Type 1 (16k+1) integers become divisible by 4 after 3x+1 operation and transform into Type 1, Type 3, Type 5 and Type 7 only, after division by 4. e) Type 2 (16k+3) integers become divisible by 2 after 3x+1 operation and transform into Type 3 and Type 7 only, after division by 2. f) Type 3 (16...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.14163717
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_14163717

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Bagchi, Aditya, \"Collatz Conjecture :Deterministic Approach To Prove Universality\", Zenodo, DOI:10.5281/zenodo.14163717 [2024]."

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

end Collatz.Papers.Journal_10_5281_zenodo_14163717
