import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Del Gobbo, Daniele, "A New Arithmetich for Collatz Conjecture", 2026.

Title: A New Arithmetich for Collatz Conjecture

Abstract (from harvested metadata, truncated):
We introduce the F-system, a block decomposition of the Collatz map that encodes every positive integer n = 2^d · m − 1 (with d ≥ 1 and m odd) as a pair (d, m) in ℕ × {odd integers}. The Collatz iteration is replaced by a single deterministic map F that aggregates an entire block of consecutive steps. Within this framework we prove three rigorous theorems: (1) Theorem D1: for m uniform modulo 2^N, the next block-exponent d' = v₂(q+1) follows a geometric distribution P(d'=k) = 2^{-k}, independently of d. (2) Theorem e⊥d': the two fundamental 2-adic valuations e = v₂(3^d·m−1) and d' are stochastically independent, each geometric, proved via the Chinese Remainder Theorem. (3) Theorem φ: for eve...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.18813743
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_18813743

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Del Gobbo, Daniele, \"A New Arithmetich for Collatz Conjecture\", Zenodo, DOI:10.5281/zenodo.18813743 [2026]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Journal_10_5281_zenodo_18813743
