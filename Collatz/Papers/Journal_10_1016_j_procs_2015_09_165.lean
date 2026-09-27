import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Michael A. Idowu, "A Novel Theoretical Framework Formulated for Information Discovery from Number System and Collatz Conjecture Data", 2015.

Title: A Novel Theoretical Framework Formulated for Information Discovery from Number System and Collatz Conjecture Data

Abstract (from harvested metadata, truncated):
Newly discovered fundamental theories (metamathematics) of integer numbers may be used to formalise and formulate a new theoretical number system from which other formal analytical frameworks may be discovered, primed and developed. The proposed number system, as well as its most general framework which is based on the modelling results derived from an investigation of the Collatz conjecture (i.e., the 3x+1 problem), has emerged as an effective exploratory tool for visualising, mining and extracting new knowledge about quite a number of mathematical theorems and conjectures, including the Collatz conjecture. Here, we introduce and demonstrate many known applications of this prime framework and show the subsequent results of further analyses as new evidences to justify the claimed...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.1016/j.procs.2015.09.165
-/

namespace Collatz.Papers.Journal_10_1016_j_procs_2015_09_165

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Michael A. Idowu, \"A Novel Theoretical Framework Formulated for Information Discovery from Number System and Collatz Conjecture Data\", Procedia Computer Science, DOI:10.1016/j.procs.2015.09.165 [2015]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Journal_10_1016_j_procs_2015_09_165
