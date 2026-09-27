import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Toru Ohira and Hiroshi Watanabe, "A Conjecture on the Collatz-Kakutani Path Length for the Mersenne Primes", 2011.

Title: A Conjecture on the Collatz-Kakutani Path Length for the Mersenne Primes

Abstract (from harvested metadata, truncated):
We present here a new conjecture for the nature of the Mersenne prime numbers by connecting it with the Collatz-Kakutani problem. By introducing a natural path length on the basis of the Collatz-Kakutani tree, we conjecture that this path length of a Mersenne prime from the root of the Collatz-Kakutani tree is approximately proportional to the index of the Mersenne prime. We also discuss difference of behaviors between Mersenne numbers and Mersenne primes.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.48550/arxiv.1104.2804
-/

namespace Collatz.Papers.Journal_10_48550_arxiv_1104_2804

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Toru Ohira and Hiroshi Watanabe, \"A Conjecture on the Collatz-Kakutani Path Length for the Mersenne Primes\", arXiv (Cornell University), DOI:10.48550/arxiv.1104.2804 [2011]."

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

end Collatz.Papers.Journal_10_48550_arxiv_1104_2804
