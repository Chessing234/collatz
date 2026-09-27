import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Max Milkert et al., "Prime Holdout Problems", arXiv:2205.12932 [2022].

Title: Prime Holdout Problems

Abstract (from OpenAlex metadata, truncated):
This paper introduces prime holdout problems, a problem class related to the Collatz conjecture. After applying a linear function, instead of removing a finite set of prime factors, a holdout problem specifies a set of primes to be retained. A proof that all positive integers converge to 1 is given for both a finite and an infinite holdout problem. It is conjectured that finite holdout problems cannot diverge for any starting value, which has implications for divergent sequences in the Collatz conjecture.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2205.12932
-/

namespace Collatz.Papers.Arxiv2205_12932

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Max Milkert et al., \"Prime Holdout Problems\", arXiv:2205.12932 [2022]."

/-- Recorded claim shell (structural); the paper's theorem is not proved.
Placeholder equals the standard Collatz conjecture proposition. -/
def mainStatement : Prop := Collatz.CollatzConjecture

/-- Checked bridge facts only. -/
theorem step_one_eq : Collatz.step 1 = 4 := Collatz.step_one

theorem step_two_eq : Collatz.step 2 = 1 := Collatz.step_two

/-- Checked: every power of two reaches `1` (Mathlib-copied parity/division facts). -/
theorem powers_of_two_reach_one (k : Nat) :
    ∃ t : Nat, Collatz.orbit t (2 ^ k) = 1 :=
  Collatz.Papers.MathlibCopied.orbit_pow_two_reaches_one k

end Collatz.Papers.Arxiv2205_12932
