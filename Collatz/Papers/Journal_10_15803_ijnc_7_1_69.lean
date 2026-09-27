import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Takumi Honda et al., "GPU-accelerated Exhaustive Verification of the Collatz Conjecture", 2017.

Title: GPU-accelerated Exhaustive Verification of the Collatz Conjecture

Abstract (from harvested metadata, truncated):
The main contribution of this paper is to present an implementation that performs the exhaustive search to verify the Collatz conjecture using a GPU. Consider the following operation on an arbitrary positive number: if the number is even, divide it by two, and if the number is odd, triple it and add one. The Collatz conjecture asserts that, starting from any positive number m, repeated iteration of the operations eventually produces the value 1. We have implemented it on NVIDIA GeForce GTX TITAN X and evaluated the performance. The experimental results show that, our GPU implementation can verify 1.31×1012 64-bit numbers per second. While the sequential CPU implementation on Intel Core i7-4790 can verify 5.25×109 64-bit numbers per second. Thus, our implementation on the GPU attains a...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.15803/ijnc.7.1_69
-/

namespace Collatz.Papers.Journal_10_15803_ijnc_7_1_69

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Takumi Honda et al., \"GPU-accelerated Exhaustive Verification of the Collatz Conjecture\", International Journal of Networking and Computing, DOI:10.15803/ijnc.7.1_69 [2017]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Journal_10_15803_ijnc_7_1_69
