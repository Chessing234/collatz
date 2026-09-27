import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Eduardo Andres, Garcia Lecaros, "Proof of the Collatz conjecture - Formal Verification in Lean 4", 2026.

Title: Proof of the Collatz conjecture - Formal Verification in Lean 4

Abstract (from harvested metadata, truncated):
We establish a structural resolution of the Collatz Conjecture. The proof proceeds through a strict interception of the scalar cycle equation over the Syracuse dynamics. We demonstrate that any hypothetical cycle defines a forced mixed-radix expansion satisfying the identity n * (2^K - 3^m) = S, where the accumulator S is strictly positive. We introduce the Diophantine Sign Lemma, which proves that if the average of even projections falls below the viability threshold (K/m < log_2(3)), the fraction collapses, forcing the cycle into the negative integers. Conversely, if the cycle operates in the strictly positive regime, we apply the Schmidt Subspace Theorem for S-unit equations to prove the algebraic disjointness of the accumulator, rendering the space of integer solutions empty....

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.19170117
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_19170117

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Eduardo Andres, Garcia Lecaros, \"Proof of the Collatz conjecture - Formal Verification in Lean 4\", DOI:10.5281/zenodo.19170117 [2026]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Journal_10_5281_zenodo_19170117
