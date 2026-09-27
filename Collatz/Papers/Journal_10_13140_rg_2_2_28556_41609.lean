import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Tim Tarver, "The Collatz Conjecture: Determining an Infinite Convergent Sequence", 2017.

Title: The Collatz Conjecture: Determining an Infinite Convergent Sequence

Abstract (from harvested metadata, truncated):
The field of number theory is vital in mathematics. Vitality of this field includes and is not limited to the distribution of prime numbers and cryptography. One of the most important unsolved mathematics problems are the Collatz conjecture. This conjecture consists of a sequence to determine whether it converges to one for all positive initial integer values. The conjecture may hint to other findings later down the road. This paper was developed to numerically specify the Collatz sequence. Also, the specification was set up to lead towards proof.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.13140/rg.2.2.28556.41609
-/

namespace Collatz.Papers.Journal_10_13140_rg_2_2_28556_41609

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Tim Tarver, \"The Collatz Conjecture: Determining an Infinite Convergent Sequence\", DOI:10.13140/rg.2.2.28556.41609 [2017]."

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

end Collatz.Papers.Journal_10_13140_rg_2_2_28556_41609
