import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for David Mailland and Petro Kosobutskyy, "MODELLING THE COLLATZ PROBLEM FROM A JACOBSTHAL VIEWPOINT", 2026.

Title: MODELLING THE COLLATZ PROBLEM FROM A JACOBSTHAL VIEWPOINT

Abstract (from harvested metadata, truncated):
This work does not aim to solve the Collatz conjecture, but to reformulate it within a new analytical framework based on Jacobsthal sequences. This reformulation reveals structural regularities and symmetries that remain hidden in the traditional approach, offering a new mathematical perspective from which the Collatz-type problems may be further explored. This approach can be reproduced in System Engineering analyses, where alternative representation are often valuable for exposing hidden structure and improving understanding. Beyond its mathematical significance, the proposed framework may also offer conceptual and methodological benefits for the field of Information Technology (IT). Many problems in computer science involve the analysis of iterative processes, recursive algorithms, and...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.23939/cds2026.01.049
-/

namespace Collatz.Papers.Journal_10_23939_cds2026_01_049

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "David Mailland and Petro Kosobutskyy, \"MODELLING THE COLLATZ PROBLEM FROM A JACOBSTHAL VIEWPOINT\", Computer Design Systems Theory and Practice, DOI:10.23939/cds2026.01.049 [2026]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Journal_10_23939_cds2026_01_049
