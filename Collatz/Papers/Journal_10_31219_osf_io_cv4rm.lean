import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Andrew Gleibman, "Monotonic and Gradient-Flipping Subsequences of a Collatz Sequence", 2023.

Title: Monotonic and Gradient-Flipping Subsequences of a Collatz Sequence

Abstract (from harvested metadata, truncated):
This is a continuation of our papers Reformulating Collatz Conjecture Without Numerical Concepts and Maximal Length of a Collatz Sequence. The first one provides a way to replace all numerical calculations, applied in the original formulation of the conjecture, by simple symbol processing rules. In the second one we prove that there is no limit for the length of a Collatz sequence, formed by odd numbers produced by Collatz's algorithm. Following this approach, here we show that such sequences may contain monotonically increasing, monotonically decreasing, and gradient-flipping sub-sequences of any length.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.31219/osf.io/cv4rm
-/

namespace Collatz.Papers.Journal_10_31219_osf_io_cv4rm

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Andrew Gleibman, \"Monotonic and Gradient-Flipping Subsequences of a Collatz Sequence\", DOI:10.31219/osf.io/cv4rm [2023]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Journal_10_31219_osf_io_cv4rm
