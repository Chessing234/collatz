import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Lu, Ping, "Lu Collatz Reverse Pruning Sieve (2026): A Dichotomy Proof of the Collatz Conjecture", 2026.

Title: Lu Collatz Reverse Pruning Sieve (2026): A Dichotomy Proof of the Collatz Conjecture

Abstract (from harvested metadata, truncated):
This paper presents a complete proof of the Collatz conjecture. We establish three foundational facts: (1) every even number reduces to an odd number; (2) every odd number belongs to exactly one of the three classes 6a + 1, 6a + 3, or 6a + 5; (3) numbers of the form 6a + 3 (odd multiples of 3) serve as the base case within the induction framework. By constructing a "pruned reverse tree" sieve, we prove that any number in the classes 6a +1 or 6a +5, if it is a counterexample, must survive all finite levels of the sieve and therefore must belong to the3-adic limit intersection Roo. We characterize Roo algebraically as the set of numbers of the form 2k-3n - 1. Then, using the accelerated Collatz map T(n) = (3n + 1)/2t2(3n+1), we prove that any such number either strictly collapses to a...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.21502070
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_21502070

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Lu, Ping, \"Lu Collatz Reverse Pruning Sieve (2026): A Dichotomy Proof of the Collatz Conjecture\", DOI:10.5281/zenodo.21502070 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_21502070
