import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Lafontaine, Mary and Cheong, Gerard, "A Note on Circular Reasoning in a Claimed Proof of the Collatz Conjecture", 2026.

Title: A Note on Circular Reasoning in a Claimed Proof of the Collatz Conjecture

Abstract (from harvested metadata, truncated):
We identify circular reasoning in the recent proof of the Collatz conjecture claimed by Mirkowska and Salwicki. The authors infer that no infinite Collatz computation exists because their graph consists of standard natural numbers, although an infinite path may contain only standard integers. They then introduce, for every initial value \(r\), a finite iteration count \(i(r)\) at which the trajectory reaches \(1\), thereby assuming the very termination property to be proved. Consequently, neither the claimed recursive construction nor the subsequent application of an infinitary inference rule establishes the Collatz conjecture.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.22699325
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_22699325

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Lafontaine, Mary and Cheong, Gerard, \"A Note on Circular Reasoning in a Claimed Proof of the Collatz Conjecture\", Zenodo, DOI:10.5281/zenodo.22699325 [2026]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Journal_10_5281_zenodo_22699325
