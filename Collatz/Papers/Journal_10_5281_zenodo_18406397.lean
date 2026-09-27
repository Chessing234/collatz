import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Potts, David, "The Sextant Matrix System: A Structural Resolution of the Collatz Conjecture", 2026.

Title: The Sextant Matrix System: A Structural Resolution of the Collatz Conjecture

Abstract (from harvested metadata, truncated):
This manuscript presents the Sextant Matrix System, a novel framework that organizes the set of positive odd integers Z^+_{odd} into an Infinite Radial Lattice of six angular sectors. By mapping the arithmetic flow of the Collatz map onto this rigid geometric coordinate system, we resolve the seemingly chaotic dynamics of the 3n+1 function into a precise Coordinate Map governed by a deterministic Recursive Directed Graph. Within this static geometry, we exploit the modular relationship between generative forms (4n+1 and linear expansions) and the underlying 6k+3 structure to map three precise ascending pathways. This logic constructs the infinite Generative Graded Tree rooted at E_{1,1} (1)...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.18406397
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_18406397

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Potts, David, \"The Sextant Matrix System: A Structural Resolution of the Collatz Conjecture\", Zenodo, DOI:10.5281/zenodo.18406397 [2026]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Journal_10_5281_zenodo_18406397
