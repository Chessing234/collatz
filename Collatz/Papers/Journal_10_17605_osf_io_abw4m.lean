import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Fahil Fahil, "Collatz-Root Hypothesis: A Framework Towards the Collatz Conjecture", 2026.

Title: Collatz-Root Hypothesis: A Framework Towards the Collatz Conjecture

Abstract (from harvested metadata, truncated):
The Collatz conjecture asks whether every natural number eventually reaches 1 under iteration of the map f (n) = n/2 if n is even and f (n) = 3n + 1 if n is odd. Despite extensive computational verification up to 268, a general proof remains elusive. In this paper, I introduce the Collatz-Root Hypothesis (CRH), a structural framework based on backward expansion of 1 via predecessor sets. I define Collatz and Collatz roots, construct depth levels Db up to D100, and present evidence of non-repetition and infinite expansion. CRH asserts that every number has a distinct Collatz root, that the Collatz root tree expands without merging, and that all numbers ultimately collapse to 1. If CRH holds g...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.17605/osf.io/abw4m
-/

namespace Collatz.Papers.Journal_10_17605_osf_io_abw4m

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Fahil Fahil, \"Collatz-Root Hypothesis: A Framework Towards the Collatz Conjecture\", OSF, DOI:10.17605/osf.io/abw4m [2026]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Journal_10_17605_osf_io_abw4m
