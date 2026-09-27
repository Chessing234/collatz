import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Jonathan Jared Wilson, "Collatz solution Collatz the Fact!", 2024.

Title: Collatz solution Collatz the Fact!

Abstract (from harvested metadata, truncated):
In this paper, I present a comprehensive resolution of the Collatz Conjecture, achievedthrough a novel synthesis of theoretical insights, computational exploration, and machine learning techniques [11]. The approach centers on the development of two key concepts: theBase-p Alternation Metric (BAM_p) and the P-adic Convergence Invariant (PCI) [15]

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.31219/osf.io/7adfb
-/

namespace Collatz.Papers.Journal_10_31219_osf_io_7adfb

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Jonathan Jared Wilson, \"Collatz solution Collatz the Fact!\", DOI:10.31219/osf.io/7adfb [2024]."

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

end Collatz.Papers.Journal_10_31219_osf_io_7adfb
