import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Fisher, Christopher, "A Complete Proof of the Collatz Conjecture: Deterministic Descent and Convergence", 2025.

Title: A Complete Proof of the Collatz Conjecture: Deterministic Descent and Convergence

Abstract (from harvested metadata, truncated):
This work presents a complete and rigorously verified proof of the Collatz Conjecture using a deterministic approach to descent, convergence, and stopping time behavior. The method combines inductive reasoning with explicit computational bounds and empirical validation. The central result establishes that every positive integer, when subjected to the Collatz function, will descend below its starting value within at most 36 odd iterations. Using this deterministic bound, the proof confirms global convergence for all positive integers through complete induction. The paper also demonstrates that the number of steps required to reach the final fixed point grows logarithmically with respect to th...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.15088509
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_15088509

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Fisher, Christopher, \"A Complete Proof of the Collatz Conjecture: Deterministic Descent and Convergence\", Zenodo, DOI:10.5281/zenodo.15088509 [2025]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Journal_10_5281_zenodo_15088509
