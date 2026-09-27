import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Jeffrey Alexander Webb, "Collatz Conjecture Solved", 2026.

Title: Collatz Conjecture Solved

Abstract (from harvested metadata, truncated):
I solved the Collatz conjecture -Jeffrey Alexander Webb - Dragon knight is symbolic, I never had one person let me know how good or bad my paper was, I never recieved any feed back or anything about what I have published. I solved the Collatz Conjecture, I wish my work was worth any of your time. I have deleted it from my computer now. I hope one of you can solve it, good luck.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.21643101
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_21643101

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Jeffrey Alexander Webb, \"Collatz Conjecture Solved\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.21643101 [2026]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Journal_10_5281_zenodo_21643101
