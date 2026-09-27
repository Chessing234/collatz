import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Michael Williams, "Collatz Conjecture: An Order Machine", 2022.

Title: Collatz Conjecture: An Order Machine

Abstract (from harvested metadata, truncated):
Collatz conjecture (3n+1 problem) is an application of Cantor's isomorphism theorem (Cantor-Bernstein) under recursion. The set of 3n+1 for all odd positive integers n, is an order isomorphism for (odd X, 3X+1). The other (odd X, 3X+1) linear order has been discovered as a bijective order-embedding, with values congruent to powers of four. This is demonstrated using a binomial series as a set rule, then showing the isomorphic structure, mapping, and cardinality of those sets. Collatz conjecture is representative of an order machine for congruence to powers of two. If an initial value is not congruent to a power of two, then the iterative program operates the (odd X, 3X+1) order isomorphism until an embedded value is attained. Since this value is a power of four, repeated division by two...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.20944/preprints202203.0401.v1
-/

namespace Collatz.Papers.Journal_10_20944_preprints202203_0401_v1

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Michael Williams, \"Collatz Conjecture: An Order Machine\", Preprints.org, DOI:10.20944/preprints202203.0401.v1 [2022]."

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

end Collatz.Papers.Journal_10_20944_preprints202203_0401_v1
