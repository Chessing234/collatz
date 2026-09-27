import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Rjd2 Rj Poeling, "A Zero-Free Expression Framework for Collatz Sequences", 2026.

Title: A Zero-Free Expression Framework for Collatz Sequences

Abstract (from harvested metadata, truncated):
This paper proposes a zero-free expression framework for representing Collatz sequences. The standard Collatz map operates on positive integers using the rule that even values are divided by two and odd values are mapped by 3n + 1, The framework presented here does not alter the numerical value of Collatz terms, but rejects zero as a primitive digit in the written sequence. Any value containing the digit 0 is instead rewritten as an equivalent expression using nonzero digits and standard arithmetic operations. For example, "10 may be represented as 9 + 1, 20 as 19 + 1, and 100 as 99 + 1", This allows Collatz paths to be displayed through zero-free expression form while preserving their ordinary value. The paper also discusses a signed mirror extension in which positive odd terms use 3n +...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.20017288
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_20017288

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Rjd2 Rj Poeling, \"A Zero-Free Expression Framework for Collatz Sequences\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.20017288 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_20017288
