import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Yasuaki Ito and Koji Nakano, "Efficient exhaustive verification of the Collatz conjecture using DSP48E blocks of Xilinx Virtex-5 FPGAs", 2010.

Title: Efficient exhaustive verification of the Collatz conjecture using DSP48E blocks of Xilinx Virtex-5 FPGAs

Abstract (from harvested metadata, truncated):
Consider the following operation on an arbitrary positive number: if the number is even, divide it by two, and if the number is odd, triple it and add one. The Collatz conjecture asserts that, starting from any positive number m, repeated iteration of the operations eventually produces the value 1. The main contribution of this paper is to present an efficient implementation of a coprocessor that performs the exhaustive search to verify the Collatz conjecture using a DSP48E Xilinx Virtex-5 blocks, each of which contains one multiplier and one adder. The experimental results show that, our coprocessor can verify 3.88 × 10864-bit numbers per second.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.1109/ipdpsw.2010.5470837
-/

namespace Collatz.Papers.Journal_10_1109_ipdpsw_2010_5470837

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Yasuaki Ito and Koji Nakano, \"Efficient exhaustive verification of the Collatz conjecture using DSP48E blocks of Xilinx Virtex-5 FPGAs\", DOI:10.1109/ipdpsw.2010.5470837 [2010]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Journal_10_1109_ipdpsw_2010_5470837
