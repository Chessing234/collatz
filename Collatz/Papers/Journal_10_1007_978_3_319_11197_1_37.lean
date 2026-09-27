import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Takumi Honda et al., "GPU-Accelerated Verification of the Collatz Conjecture", 2014.

Title: GPU-Accelerated Verification of the Collatz Conjecture

Abstract (from harvested metadata, truncated):
(No abstract in harvested metadata; statement recorded from title/venue only.)

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.1007/978-3-319-11197-1_37
-/

namespace Collatz.Papers.Journal_10_1007_978_3_319_11197_1_37

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Takumi Honda et al., \"GPU-Accelerated Verification of the Collatz Conjecture\", Lecture notes in computer science, DOI:10.1007/978-3-319-11197-1_37 [2014]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Journal_10_1007_978_3_319_11197_1_37
