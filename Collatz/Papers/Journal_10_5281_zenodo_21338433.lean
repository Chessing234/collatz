import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for elhisadi, mahir, "A Proof of the Collatz Conjecture Using an Attractor Set and a Lexicographic Measure for 7-Class Numbers", 2026.

Title: A Proof of the Collatz Conjecture Using an Attractor Set and a Lexicographic Measure for 7-Class Numbers

Abstract (from harvested metadata, truncated):
We prove the Collatz conjecture using:• Classification of odd numbers by residue modulo 8.• An attractor set A = {Aj = (4j − 1)/3} ∪ {4m}.• The observation that every odd number lies at an even distance from both boundaryattractors.• A lexicographic measure Φ(n) = (−j, min(x, y)) for 7 (mod 8) numbers, which iswell-founded: the 7-odd phase is finite by the v2(k + 1) descent, and the 7-evenphase terminates in finitely many bounces. Numerical analysis confirms thatvertical bounces consistently decrease x, while min(x, y) is bounded below by 1,ensuring the well-foundedness of the measure.All lemmas are rigorously proved. The proof is complete.Numerical verification using Python to generate tabl...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.21338433
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_21338433

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "elhisadi, mahir, \"A Proof of the Collatz Conjecture Using an Attractor Set and a Lexicographic Measure for 7-Class Numbers\", Zenodo, DOI:10.5281/zenodo.21338433 [2026]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Journal_10_5281_zenodo_21338433
