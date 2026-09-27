import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Ibbotson, James Norman, "The Collatz Conjecture: Computational Analysis Through Temporal Dynamics Framework", 2026.

Title: The Collatz Conjecture: Computational Analysis Through Temporal Dynamics Framework

Abstract (from harvested metadata, truncated):
This paper applies the Temporal Dynamics Framework resonance and decoherence analysis to the Collatz Conjecture (also known as the 3n + 1 problem). The Collatz Conjecture states that for any positive integer n, the sequence defined by n/2 if n is even and 3n + 1 if n is odd will eventually reach 1. Despite its simple statement, the conjecture remains unproven. The analysis examines iterative dynamics, convergence patterns, and Universal Prime modular structure in Collatz trajectories. Paper 39 in the Temporal Dynamics Framework Research Series.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.19544271
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_19544271

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Ibbotson, James Norman, \"The Collatz Conjecture: Computational Analysis Through Temporal Dynamics Framework\", Zenodo, DOI:10.5281/zenodo.19544271 [2026]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Journal_10_5281_zenodo_19544271
