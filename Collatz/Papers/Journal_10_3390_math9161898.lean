import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Alexander Rahn et al., "An Algorithm for Linearizing the Collatz Convergence", 2021.

Title: An Algorithm for Linearizing the Collatz Convergence

Abstract (from harvested metadata, truncated):
The Collatz dynamic is known to generate a complex quiver of sequences over natural numbers for which the inflation propensity remains so unpredictable it could be used to generate reliable proof-of-work algorithms for the cryptocurrency industry; it has so far resisted every attempt at linearizing its behavior. Here, we establish an ad hoc equivalent of modular arithmetics for Collatz sequences based on five arithmetic rules that we prove apply to the entire Collatz dynamical system and for which the iterations exactly define the full basin of attractions leading to any odd number. We further simulate these rules to gain insight into their quiver geometry and computational properties and observe that they linearize the proof of convergence of the full rows of the binary tree over odd...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.3390/math9161898
-/

namespace Collatz.Papers.Journal_10_3390_math9161898

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Alexander Rahn et al., \"An Algorithm for Linearizing the Collatz Convergence\", Mathematics, DOI:10.3390/math9161898 [2021]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Journal_10_3390_math9161898
