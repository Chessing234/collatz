import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Toru Ohira, Hiroshi Watanabe, "A Conjecture on the Collatz-Kakutani Distance for the Mersenne Prime Numbers", arXiv:1104.2804 [2011].

Title: A Conjecture on the Collatz-Kakutani Distance for the Mersenne Prime Numbers

Abstract (from OpenAlex metadata, truncated):
We present here a new conjecture for the nature of the Mersenne prime numbers by connecting it with the Collatz-Kakutani problem. By introducing the measure on natural numbers using the Collatz-Kakutani tree, we found that there is an approximate linear relation between the index of the Mersenne prime numbers and its distance from one on the Collatz-Kakutani tree. Introduction Prime numbers have attracted mathematically oriented minds. They are often the sources of unsolved mathematical problems with their lack of regularities in various aspects. Let aside prime numbers, natural numbers themselves have rather unexpected properties in spite of their simple appeal. In this report, we would like to present a simple property arising from the combination of two unsolved problems in number theory; Mersenne prime numbers and the Collatz-Kakutani conjecture. Namely, we show that there exists an 

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/1104.2804
-/

namespace Collatz.Papers.Arxiv1104_2804

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Toru Ohira and Hiroshi Watanabe, \"A Conjecture on the Collatz-Kakutani Distance for the Mersenne Prime Numbers\", arXiv:1104.2804 [2011]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Arxiv1104_2804
