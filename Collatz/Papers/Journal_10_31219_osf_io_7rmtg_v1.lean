import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Kiemes, Jochen, "Collatz Conjecture: The Race To One", 2025.

Title: Collatz Conjecture: The Race To One

Abstract (from harvested metadata, truncated):
This paper presents an approach that reinterprets the Collatz sequence by transforming it into a new sequence, highlighting the dynamic relationship between the trailing and leading bits of its elements. This mapping enables the study of a "bit-race," whose well-defined statistical properties rigorously guarantee the convergence of all Collatz sequences to 1.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.31219/osf.io/7rmtg_v1
-/

namespace Collatz.Papers.Journal_10_31219_osf_io_7rmtg_v1

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Kiemes, Jochen, \"Collatz Conjecture: The Race To One\", DOI:10.31219/osf.io/7rmtg_v1 [2025]."

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

end Collatz.Papers.Journal_10_31219_osf_io_7rmtg_v1
