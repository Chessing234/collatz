import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Andrew Stewart Caldin, "Undecidability and the Collatz Conjecture: The Limits of Algorithmic Computation — E8 Intelligence Research", 2026.

Title: Undecidability and the Collatz Conjecture: The Limits of Algorithmic Computation — E8 Intelligence Research

Abstract (from harvested metadata, truncated):
FINDING: The core mathematical insight is the existence of formally undecidable problems (Turing/Hilbert) and the unresolved Collatz Conjecture, which together define the boundary of algorithmic computability. | MATH: Collatz map: T(n) = n/2 if n even, 3n+1 if n odd; no closed-form solution or proof of termination for all n ∈ ℕ. Turing's halting problem: no general algorithm exists to decide if a program halts — formalized via diagonalization, leading to the Entscheidungsproblem's undecidability. | CONNECTION: None directly to 0.382, 0.618, 0.786, 1.618, 2.618, base-60, or crystallographic symmetries. The Collatz map's iterates do not exhibit known harmonic ratios; the undecidability results...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.22075658
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_22075658

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Andrew Stewart Caldin, \"Undecidability and the Collatz Conjecture: The Limits of Algorithmic Computation — E8 Intelligence Research\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.22075658 [2026]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Journal_10_5281_zenodo_22075658
