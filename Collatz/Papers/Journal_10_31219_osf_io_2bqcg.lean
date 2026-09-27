import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Bennassar, Miguel Cerda, "THE COLLATZ CONJECTURE. Order and harmony in the sequence numbers.", 2019.

Title: THE COLLATZ CONJECTURE. Order and harmony in the sequence numbers.

Abstract (from harvested metadata, truncated):
Abstract: I propose a numerical table that demonstrates visually that the sequences formed withCollatz's algorithm always reach 1.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.31219/osf.io/2bqcg
-/

namespace Collatz.Papers.Journal_10_31219_osf_io_2bqcg

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Bennassar, Miguel Cerda, \"THE COLLATZ CONJECTURE. Order and harmony in the sequence numbers.\", DOI:10.31219/osf.io/2bqcg [2019]."

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

end Collatz.Papers.Journal_10_31219_osf_io_2bqcg
