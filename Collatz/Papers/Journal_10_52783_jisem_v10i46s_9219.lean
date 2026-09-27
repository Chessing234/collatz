import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Vidyashree H R, "A Unified Proof of the Collatz Conjecture for Positive and Negative Integers", 2025.

Title: A Unified Proof of the Collatz Conjecture for Positive and Negative Integers

Abstract (from harvested metadata, truncated):
The Collatz Conjecture, a long-standing unsolved problem in mathematics, proposes that repeated application of a simple transformation: dividing even numbers by two and mapping odd numbers to three times the number plus one, eventually leads every positive integer to the number one. In this paper, we present a structured, theorem-based approach to proving the conjecture. We first establish that all numbers of the form 2n directly reach 1 through successive divisions by 2. We then prove that every even number reduces to a power of 2 and hence reaches 1. Extending this, we show that odd numbers become even through one Collatz step, allowing the previous results to apply. Finally, we propose a...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.52783/jisem.v10i46s.9219
-/

namespace Collatz.Papers.Journal_10_52783_jisem_v10i46s_9219

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Vidyashree H R, \"A Unified Proof of the Collatz Conjecture for Positive and Negative Integers\", Journal of Information Systems Engineering and Management, DOI:10.52783/jisem.v10i46s.9219 [2025]."

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

end Collatz.Papers.Journal_10_52783_jisem_v10i46s_9219
