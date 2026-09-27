import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Wang, Zhendong, "A Note on the Structure of y = n mod 2^{v₂(3n+1)} in Collatz Iteration (Working Note, Version 3)", 2026.

Title: A Note on the Structure of y = n mod 2^{v₂(3n+1)} in Collatz Iteration (Working Note, Version 3)

Abstract (from harvested metadata, truncated):
This is a working note (Version 3) on an elementary structural observation in the Collatz / Syracuse iteration. For an odd positive integer n, let m = v₂(3n + 1). The note records that the residue y = n mod 2^m depends only on m, and admits the closed form y_m = (4^{⌈m/2⌉} − 1)/3. This leads to a simple decomposition of the Syracuse function T(n) = 3q + 1 or 3q + 2 according to the parity of m. The note also connects this residue structure to the Jacobsthal sequence and, in Version 3, to a multiplicative-order recursion tower that links the observation to the author's related work on the distribution of primes near powers of 2. The author presents this as a working note rather than a claim of new results, noting that the core observation is elementary and likely known to specialists in...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.20587119
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_20587119

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Wang, Zhendong, \"A Note on the Structure of y = n mod 2^{v₂(3n+1)} in Collatz Iteration (Working Note, Version 3)\", DOI:10.5281/zenodo.20587119 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_20587119
