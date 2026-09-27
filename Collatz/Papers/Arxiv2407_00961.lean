import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Gaurav Goyal, "$2^m - 1$ as the Integer Formulation to Govern the Dynamics of Collatz-Type Sequences", arXiv:2407.00961 [2024].

Title: $2^m - 1$ as the Integer Formulation to Govern the Dynamics of Collatz-Type Sequences

Abstract (from OpenAlex metadata, truncated):
It has been discovered that representing odd integers as modified binary expressions of the form $\sum \limits_{n > m}2^n + 2^m - 1$ for $m \geq 1$ helps in understanding the dynamics of Collatz-type sequences. Starting with the original Collatz sequence $3x + 1$, it is found that when the odd step is applied to an odd integer $\sum \limits_{n > m}2^n + 2^m - 1$, an even integer $3\left(\sum \limits_{n > m}2^{n}\right) + 2^{m + 1} + 2^m - 2$ is obtained, which is exactly once divisible by 2, unless the lowest index reduces to zero. This implies that the sequence alternates between odd and even steps $m$ times. This governs the dynamics of the Collatz-type sequences because the value of $m$ determines the number of times the integer can be divided by 2 in each even step. A shortcut method is developed based on this dynamics that states that the even integer after $m$ odd-even steps are co

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2407.00961
-/

namespace Collatz.Papers.Arxiv2407_00961

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Gaurav Goyal, \"$2^m - 1$ as the Integer Formulation to Govern the Dynamics of Collatz-Type Sequences\", arXiv:2407.00961 [2024]."

/-- Recorded main claim shell (generalization); the paper's theorem is not proved here.
This placeholder is the standard Collatz conjecture proposition. -/
def mainStatement : Prop := Collatz.CollatzConjecture

/-- Checked bridge facts only. -/
theorem step_one_eq : Collatz.step 1 = 4 := Collatz.step_one

theorem step_two_eq : Collatz.step 2 = 1 := Collatz.step_two

/-- Checked: every power of two reaches `1` (Mathlib-copied parity/division facts). -/
theorem powers_of_two_reach_one (k : Nat) :
    ∃ t : Nat, Collatz.orbit t (2 ^ k) = 1 :=
  Collatz.Papers.MathlibCopied.orbit_pow_two_reaches_one k

end Collatz.Papers.Arxiv2407_00961
