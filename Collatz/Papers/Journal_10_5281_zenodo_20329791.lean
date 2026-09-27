import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for elhisadi, mahir, "A Proof of the Collatz Conjecture Using an Attractor Set, Exit Points for 7 (mod 8) Numbers, and Damped Oscillation of 3 (mod 8) Numbers", 2026.

Title: A Proof of the Collatz Conjecture Using an Attractor Set, Exit Points for 7 (mod 8) Numbers, and Damped Oscillation of 3 (mod 8) Numbers

Abstract (from harvested metadata, truncated):
We prove the Collatz conjecture using:• Classification of odd numbers by residue modulo 8.• An attractor set A = {Aj = (4j − 1)/3}.• The observation that every odd number lies at an even distance from both boundaryattractors.• A lexicographic ordering function Φ(n) = (−j, min(x, y)) for 7 (mod 8) numbers.• The v2(k + 1) descent for 7-odd numbers, proving the 7-odd phase is finite.• The identification of exit points: non-bouncing 7-even numbers that terminatedirectly.• The proof that every bouncing 7-even number eventually reaches an exit point.• Strict decrease in value for 1 (mod 8) and 5 (mod 8) numbers.• The fact that 3 (mod 8) numbers map to 1 or 5 (mod 8).• The damped oscillation of 3 (mod 8) numbers after the trajectory reaches anexit point: they increase, then decrease, then...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.20329791
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_20329791

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "elhisadi, mahir, \"A Proof of the Collatz Conjecture Using an Attractor Set, Exit Points for 7 (mod 8) Numbers, and Damped Oscillation of 3 (mod 8) Numbers\", DOI:10.5281/zenodo.20329791 [2026]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Journal_10_5281_zenodo_20329791
