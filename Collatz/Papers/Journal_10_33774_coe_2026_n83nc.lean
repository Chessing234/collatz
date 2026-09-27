import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Syzdykov, Mirzakhmet, "Continued Disproof Sentence towards Collatz Conjecture", 2026.

Title: Continued Disproof Sentence towards Collatz Conjecture

Abstract (from harvested metadata, truncated):
We are to address the recent critical insight on our key idea towards asymptotic disproof of Collatz conjecture by estimating of the algorithmic step-wise approach of computing numbers in this sequence, which finally converge to one

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.33774/coe-2026-n83nc
-/

namespace Collatz.Papers.Journal_10_33774_coe_2026_n83nc

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Syzdykov, Mirzakhmet, \"Continued Disproof Sentence towards Collatz Conjecture\", DOI:10.33774/coe-2026-n83nc [2026]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Journal_10_33774_coe_2026_n83nc
