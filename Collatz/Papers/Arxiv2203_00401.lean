import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Michael Williams, "Collatz conjecture: an order isomorphic recursive machine", arXiv:2203.00401 [2024].

Title: Collatz conjecture: an order isomorphic recursive machine

Abstract (from OpenAlex metadata, truncated):
Collatz conjecture (3x+1 problem) is a natural phenomenon in set theory that may be reconstructed using known combinatorics and order theory. Construction begins by selecting a specific order isomorphism with a bijectional order-embedding. Mapping by 3x+1 induces a unique property to only members of the mapped embedding. Under selective congruence from recursive division by two, that complex controls sequence behavior. This demonstration uses an order isomorphism consisting of two linear orders: the (1) odd positive integers and the always odd (2) Rule 50 Jacobsthal numbers, as the embedding. The argument proceeds by cardinality. When the order isomorphism is mapped under 3x+1, all Rule 50 Jacobsthal numbers are mapped to all the powers of four. This one-to-one correspondence guarantees that every odd integer is assigned to a Rule 50 Jacobsthal number, and subsequently, to a power of fou

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2203.00401
-/

namespace Collatz.Papers.Arxiv2203_00401

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Michael Williams, \"Collatz conjecture: an order isomorphic recursive machine\", arXiv:2203.00401 [2024]."

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

end Collatz.Papers.Arxiv2203_00401
