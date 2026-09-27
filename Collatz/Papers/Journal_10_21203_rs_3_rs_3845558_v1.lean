import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for David Barina, "Computational Verification of the Collatz Problem", 2024.

Title: Computational Verification of the Collatz Problem

Abstract (from harvested metadata, truncated):
Abstract This article presents our project, which aims to verify the convergence of the Collatz problem computationally. As a main point of the article, we introduce a new result that pushes the limit for which the problem is verified up to 1.5 × 270. We present our baseline algorithm and then several sub-algorithms that bring some acceleration. The total acceleration from the first algorithm we used on the CPU to our best algorithm on the GPU is 1 335×. We further distribute individual tasks to thousands of parallel workers running on several European supercomputers. Besides the convergence verification, our program also checks for path records during the convergence test. We found four new path records.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.21203/rs.3.rs-3845558/v1
-/

namespace Collatz.Papers.Journal_10_21203_rs_3_rs_3845558_v1

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "David Barina, \"Computational Verification of the Collatz Problem\", Research Square, DOI:10.21203/rs.3.rs-3845558/v1 [2024]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Journal_10_21203_rs_3_rs_3845558_v1
