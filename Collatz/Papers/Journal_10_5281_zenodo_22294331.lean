import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Andrew Stewart Caldin, "Collatz and Halting: The Boundary of Algorithmic Solvability — E8 Intelligence Research", 2026.

Title: Collatz and Halting: The Boundary of Algorithmic Solvability — E8 Intelligence Research

Abstract (from harvested metadata, truncated):
FINDING: The Collatz Conjecture (3n+1) and the Halting Problem define the boundary of algorithmic solvability; the former is an unproven dynamical system, the latter a proven undecidable one. | MATH: Collatz map: T(n) = n/2 if n even, (3n+1)/2 if n odd. No closed-form solution; known to be equivalent to a Turing machine with no halting proof for all n. Halting Problem: no general algorithm H(P,I) decides if program P halts on input I — proof via diagonalization (Cantor's argument). | CONNECTION: Collatz trajectories, when plotted, show no simple scaling; but the map's structure is a 2-adic dynamical system — the 2-adic integers form a lattice with base-2 symmetry, not base-60. However, the *...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.22294331
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_22294331

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Andrew Stewart Caldin, \"Collatz and Halting: The Boundary of Algorithmic Solvability — E8 Intelligence Research\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.22294331 [2026]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Journal_10_5281_zenodo_22294331
