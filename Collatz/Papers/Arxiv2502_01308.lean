import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Eduardo Diedrich, "A Complete Proof of the Collatz Conjecture Using Generator Functions", arXiv:2502.01308 [2025].

Title: A Complete Proof of the Collatz Conjecture Using Generator Functions

Abstract (from OpenAlex metadata, truncated):
We present a complete proof of the Collatz conjecture using a novel approach based on generator functions. By analyzing the inverse mappings of the Collatz function through carefully defined generator operations, we establish that all natural numbers must eventually reach 1 under the Collatz iteration. The proof relies on demonstrating fundamental incompatibilities between the requirements for divergent sequences and the constraints imposed by even-odd patterns in the natural numbers.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2502.01308
-/

namespace Collatz.Papers.Arxiv2502_01308

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Eduardo Diedrich, \"A Complete Proof of the Collatz Conjecture Using Generator Functions\", arXiv:2502.01308 [2025]."

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

end Collatz.Papers.Arxiv2502_01308
