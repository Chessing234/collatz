import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Caldin, Andrew Stewart, "Collatz Conjecture, Hilbert's Undecidability, and Mizar's Theorem Library — E8 Intelligence Research", 2026.

Title: Collatz Conjecture, Hilbert's Undecidability, and Mizar's Theorem Library — E8 Intelligence Research

Abstract (from harvested metadata, truncated):
FINDING: Collatz Conjecture is a simple iterative problem with no known proof or counterexample; Hilbert's Decision Problem proved undecidable by Turing; Mizar library formalizes 50,000+ theorems. | MATH: Collatz: f(n) = n/2 if n even, 3n+1 if n odd; undecidability via halting problem equivalence; Mizar: 2.5M lines, 7000+ symbols. | CONNECTION: No direct geometric ratios or symmetries emerge from these results; Collatz iterations produce no known harmonic constants; undecidability is a logical boundary, not a geometric structure. | DEPTH: 2 — These are foundational results in computability and open problems, but they lack the specific mathematical constants, ratios, or symmetries requested....

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.21832242
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_21832242

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Caldin, Andrew Stewart, \"Collatz Conjecture, Hilbert's Undecidability, and Mizar's Theorem Library — E8 Intelligence Research\", Zenodo, DOI:10.5281/zenodo.21832242 [2026]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Journal_10_5281_zenodo_21832242
