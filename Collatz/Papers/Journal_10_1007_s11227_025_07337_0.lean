import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for David Barina, "Improved verification limit for the convergence of the Collatz conjecture", 2025.

Title: Improved verification limit for the convergence of the Collatz conjecture

Abstract (from harvested metadata, truncated):
Abstract This article presents our project, which aims to verify the Collatz conjecture computationally. As a main point of the article, we introduce a new result that pushes the limit for which the conjecture is verified up to $$2^{71}$$ 2 71 . We present our baseline algorithm and then several sub-algorithms that enhance acceleration. The total acceleration from the first algorithm we used on the CPU to our best algorithm on the GPU is $$1\,335\times$$ 1 335 × . We further distribute individual tasks to thousands of parallel workers running on several European supercomputers. Besides the convergence verification, our program also checks for path records during the convergence test. We found four new path records.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.1007/s11227-025-07337-0
-/

namespace Collatz.Papers.Journal_10_1007_s11227_025_07337_0

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "David Barina, \"Improved verification limit for the convergence of the Collatz conjecture\", The Journal of Supercomputing, DOI:10.1007/s11227-025-07337-0 [2025]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Journal_10_1007_s11227_025_07337_0
