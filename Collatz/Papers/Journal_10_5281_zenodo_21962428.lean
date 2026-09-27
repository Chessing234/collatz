import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Caldin, Andrew Stewart, "Collatz Conjecture and Halting Problem: Uncomputability and Chaotic Limits — E8 Intelligence Research", 2026.

Title: Collatz Conjecture and Halting Problem: Uncomputability and Chaotic Limits — E8 Intelligence Research

Abstract (from harvested metadata, truncated):
FINDING: Collatz Conjecture remains unsolved; Turing's halting problem proves some problems are fundamentally uncomputable. | MATH: Collatz function: f(n) = n/2 if n even, 3n+1 if n odd. No closed-form solution or proof of termination for all n. Halting problem: no general algorithm can decide if a given program halts. | CONNECTION: No direct geometric ratios or symmetries; the Collatz iteration exhibits chaotic behavior with no known harmonic scaling. The halting problem is a logical limit, not a geometric one. | DEPTH: 7 — The Collatz Conjecture is a deceptively simple number-theoretic problem with deep connections to dynamical systems and undecidability. The halting problem is foundationa...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.21962428
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_21962428

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Caldin, Andrew Stewart, \"Collatz Conjecture and Halting Problem: Uncomputability and Chaotic Limits — E8 Intelligence Research\", Zenodo, DOI:10.5281/zenodo.21962428 [2026]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Journal_10_5281_zenodo_21962428
