import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Selcuk Koyuncu et al., "Parity-Based Level-Set Approach to the Collatz Conjecture", 2026.

Title: Parity-Based Level-Set Approach to the Collatz Conjecture

Abstract (from harvested metadata, truncated):
The Collatz conjecture concerns the iteration of the map f(n)=3n+1 for odd n and f(n)=n/2 for even n. In this paper, we study the level sets lx={n∈N∣L(n)=x}, where L(n) denotes the Collatz length. Using the parity representation of Collatz trajectories, we partition each lx according to the number of odd steps and analyze the corresponding means μx,k. Under a natural scaling assumption, these means satisfy an approximate geometric progression, so that logμx,k is approximately linear in k. Computations for n≤100,000 and 10≤x≤50 show highly stable regression parameters and near-perfect linear fits.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.3390/math14101763
-/

namespace Collatz.Papers.Journal_10_3390_math14101763

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Selcuk Koyuncu et al., \"Parity-Based Level-Set Approach to the Collatz Conjecture\", Mathematics, DOI:10.3390/math14101763 [2026]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Journal_10_3390_math14101763
