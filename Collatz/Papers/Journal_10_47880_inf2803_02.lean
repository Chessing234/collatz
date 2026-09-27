import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Hosei University, Japan et al., "A Numerical Verification for Asymptotic Approach of the Collatz Conjecture", 2025.

Title: A Numerical Verification for Asymptotic Approach of the Collatz Conjecture

Abstract (from harvested metadata, truncated):
By using an asymptotic approach method, it has been shown that the Collatz Conjecture is true with a ratio 98.22% in all positive integers [6]. In this paper, we expand the range of numerical experiment and show that the Collatz Conjecture is true with a ratio 99.8216% in all positive integers.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.47880/inf2803-02
-/

namespace Collatz.Papers.Journal_10_47880_inf2803_02

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Hosei University, Japan et al., \"A Numerical Verification for Asymptotic Approach of the Collatz Conjecture\", Information, DOI:10.47880/inf2803-02 [2025]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Journal_10_47880_inf2803_02
