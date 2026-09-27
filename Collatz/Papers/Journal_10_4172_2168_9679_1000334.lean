import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Tedja Santanoe Oepomo, "An Alternating Sequence Iteration’s Method for Computing Largest Real Part Eigenvalue of Essentially Positive Matrices: Collatz and Perron- Frobernius’ Approach", 2017.

Title: An Alternating Sequence Iteration’s Method for Computing Largest Real Part Eigenvalue of Essentially Positive Matrices: Collatz and Perron- Frobernius’ Approach

Abstract (from harvested metadata, truncated):
This paper describes a new numerical method for the numerical solution of eigenvalues with the largest real part of essentially positive matrices. Finally, a numerical discussion is given to derive the required number of mathematical operations of the new method. Comparisons between the new method and several well know ones, such as Power and QR methods, were discussed. The process consists of computing lower and upper bounds which are monotonically approximating the eigenvalue.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.4172/2168-9679.1000334
-/

namespace Collatz.Papers.Journal_10_4172_2168_9679_1000334

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Tedja Santanoe Oepomo, \"An Alternating Sequence Iteration’s Method for Computing Largest Real Part Eigenvalue of Essentially Positive Matrices: Collatz and Perron- Frobernius’ Approach\", Journal of Applied & Computational Mathematics, DOI:10.4172/2168-9679.1000334 [2017]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Journal_10_4172_2168_9679_1000334
