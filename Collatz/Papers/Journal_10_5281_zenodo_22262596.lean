import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Kyle Harper, "Harper's Sieve of Collatz", 2026.

Title: Harper's Sieve of Collatz

Abstract (from harvested metadata, truncated):
Abstract This paper presents an algorithmic and programmatic optimization to the verification process of the Collatz Conjecture. A sieve is developed capable of a deterministic, monotonic reduction of the search space $\mathbb{N}$ via strict adherence to dyadic scaling of values and the subsequent parity vectors of their lower $k$ bits generating contractive affine transformations. The supporting data structure naturally encodes the commonly used $2^{k}$ modulo sieve and provides a new lens to view the classifications.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.22262596
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_22262596

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Kyle Harper, \"Harper's Sieve of Collatz\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.22262596 [2026]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Journal_10_5281_zenodo_22262596
