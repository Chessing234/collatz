import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Liu Chunlei, "Counting the Collatz numbers", arXiv:2512.13760 [2025].

Title: Counting the Collatz numbers

Abstract (from OpenAlex metadata, truncated):
The counting function for the numbers satisfying the Collatz conjecture is studied. A related exponential congruence equation is investigated, yielding a method to construct its solutions from free variables, and enabling us to find at least $x^{0.3227}$ Collatz numbers in the interval $[1,x]$. The historical record is 0.84.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2512.13760
-/

namespace Collatz.Papers.Arxiv2512_13760

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Liu Chunlei, \"Counting the Collatz numbers\", arXiv:2512.13760 [2025]."

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

end Collatz.Papers.Arxiv2512_13760
