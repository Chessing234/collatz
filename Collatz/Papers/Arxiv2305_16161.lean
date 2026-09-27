import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Eduardo M. K. Souza, "Infinity increasing steps on the Collatz sequences", arXiv:2305.16161 [2023].

Title: Infinity increasing steps on the Collatz sequences

Abstract (from OpenAlex metadata, truncated):
We intend to contribute to the Collatz dynamics problem by seeking to analyze the Collatz conjecture from the tree of numbers sequences. First, we show numerically that the distribution of odd numbers has an initial transient, and proceeds to a power law growth to its maximum. Second, using the formulation that uses only odd numbers, we present analytically a set of odd number sequences that is always increasing and can have an infinite number of terms.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2305.16161
-/

namespace Collatz.Papers.Arxiv2305_16161

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Eduardo M. K. Souza, \"Infinity increasing steps on the Collatz sequences\", arXiv:2305.16161 [2023]."

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

end Collatz.Papers.Arxiv2305_16161
