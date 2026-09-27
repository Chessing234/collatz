import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Yasuaki Ito and Koji Nakano, "A Hardware-Software Cooperative Approach for the Exhaustive Verification of the Collatz Conjecture", 2009.

Title: A Hardware-Software Cooperative Approach for the Exhaustive Verification of the Collatz Conjecture

Abstract (from harvested metadata, truncated):
Consider the following operation on an arbitrary positive number: if the number is even, divide it by two, and if the number is odd, triple it and add one. The Collatz conjecture assert that, starting from any positive number n, repeated iteration of the operations eventually produces the value 1. The main contribution of this paper is to present hardware-software cooperative approach to verify the Collatz conjecture. The key idea of our approach is to sieve numbers n that produces 1 using a circuit implemented on an FPGA. The numbers that fail to be verified by overflow are reported to the host PC. The host PC verifies those numbers using unlimited bits operations by software. We have implemented 24 coprocessors on the Vertex II family FPGA XC2V3000-4. The experimental results show that...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.1109/ispa.2009.35
-/

namespace Collatz.Papers.Journal_10_1109_ispa_2009_35

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Yasuaki Ito and Koji Nakano, \"A Hardware-Software Cooperative Approach for the Exhaustive Verification of the Collatz Conjecture\", DOI:10.1109/ispa.2009.35 [2009]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Journal_10_1109_ispa_2009_35
