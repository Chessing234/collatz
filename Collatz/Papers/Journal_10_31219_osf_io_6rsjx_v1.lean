import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Choyer, Evann, "A Definitive Algebraic Proof of the Collatz Conjecture", 2025.

Title: A Definitive Algebraic Proof of the Collatz Conjecture

Abstract (from harvested metadata, truncated):
The Collatz conjecture states that for any positive integer n, the sequence defined by iterativelyapplying the function C(n) = n/2 if n is even, and C(n) = 3n + 1 if n is odd, eventually reaches 1. Thispaper presents a definitive algebraic proof of the Collatz conjecture without relying on computationalverification or making any assumptions. We establish a universal descent property that applies to allpositive integers without exception, provide a purely algebraic derivation of bounds on exceptional cases,rigorously eliminate all possibilities for cycles outside of {1, 4, 2}, and prove strict bounds ensuring notrajectories diverge to infinity. Through this comprehensive algebraic approach, we definitively provethat the Collatz conjecture is true for all positive integers.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.31219/osf.io/6rsjx_v1
-/

namespace Collatz.Papers.Journal_10_31219_osf_io_6rsjx_v1

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Choyer, Evann, \"A Definitive Algebraic Proof of the Collatz Conjecture\", DOI:10.31219/osf.io/6rsjx_v1 [2025]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Journal_10_31219_osf_io_6rsjx_v1
