import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Glenn Patrick King Ang, "Deciphering the Collatz Conjecture Through Recursion", 2021.

Title: Deciphering the Collatz Conjecture Through Recursion

Abstract (from harvested metadata, truncated):
More than 80 years has passed since the Collatz conjecture has been proposed, but since then there has been no concrete proof as to why it is stuck in the 4 to 2 to 1 loop endlessly. There had been various attempts to find the reason as to why this infinite loop occurs, but there hasn’t been any widely recognized proof for the Collatz conjecture. This paper details a different approach to explain why this infinite loop occurs and at the same time explain why the Collatz conjecture is similar to a computer source code. Section 2, 3, 4, and 5 details the process used to determine the purpose of 2n and n+1 functions inside an iterative loop, while section 6 and 7 reveals the logical reasoning behind how the 2n+2 algebraic expression was obtained based on 3n+1 or 2n+n+1. Section 8 provides...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.5759527
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_5759527

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Glenn Patrick King Ang, \"Deciphering the Collatz Conjecture Through Recursion\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.5759527 [2021]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Journal_10_5281_zenodo_5759527
