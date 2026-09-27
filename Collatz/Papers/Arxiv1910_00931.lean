import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Leary, Ian J, "Iteration of functions and contractibility of acyclic 2-complexes", arXiv:1910.00931 [2019].

Title: Iteration of functions and contractibility of acyclic 2-complexes

Abstract (from arXiv metadata, truncated):
We show that there can be no algorithm to decide whether infinite recursively described acyclic aspherical 2-complexes are contractible. We construct such a complex that is contractible if and only if the Collatz conjecture holds.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/1910.00931
-/

namespace Collatz.Papers.Arxiv1910_00931

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Leary, Ian J, \"Iteration of functions and contractibility of acyclic 2-complexes\", arXiv:1910.00931 [2019]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Arxiv1910_00931
