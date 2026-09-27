import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Livio Colussi, "Some contributions to Collatz conjecture", arXiv:1703.03918 [2017].

Title: Some contributions to Collatz conjecture

Abstract (from OpenAlex metadata, truncated):
The Collatz conjecture can be stated in terms of the reduced Collatz function R(x) = (3x+1)/2^m (where 2^m is the larger power of 2 that divides 3x+1). The conjecture is: Starting from any odd positive integer and repeating R(x) we eventually get to 1. In a previous paper of the author the set of odd positive integers x such that R^k(x) = 1 has been characterized as the set of odd integers whose binary representation belongs to a set of strings G_k. Each string in G_k is the concatenation of k strings z_k z_{k-1} ... z_1 where each z_i is a finite and contiguous extract from some power of a string s_i of length 2x3^{i-1} (the seed of order i). Clearly Collatz conjecture will be true if the binary representation of any odd integer belongs to some G_k. Lately Patrick Chisan Hew showed that seeds s_i are the repetends of 1/3^i. Here two contributions to Collatz conjecture are given: - Colla

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/1703.03918
-/

namespace Collatz.Papers.Arxiv1703_03918

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Livio Colussi, \"Some contributions to Collatz conjecture\", arXiv:1703.03918 [2017]."

/-- Recorded finite-verification claim shell; the paper's bound is not proved here. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1


/-- Miniature checked verification for `B = 2`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩


end Collatz.Papers.Arxiv1703_03918
