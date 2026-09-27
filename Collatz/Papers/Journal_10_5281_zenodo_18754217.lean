import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Neel Alkoraishi, "A Binary Branch–Layer Structure and Explicit Decreasing Invariant for the Collatz Map", 2026.

Title: A Binary Branch–Layer Structure and Explicit Decreasing Invariant for the Collatz Map

Abstract (from harvested metadata, truncated):
AbstractI present a binary-based framework for the Collatz Conjecture thatorganizes all positive integers into a hierarchical branch–layer struc-ture. Every integer admits a unique decompositionn = 2^y(2^x(2R + 1) − 1) ,which determines its position within a finite branch. I prove thatunder the Collatz map T , the local branch parameters (x, y) strictlydecrease until reaching a canonical endpoint C = 2(3R + 1).Using the recursive 2n+1 construction, I show that all odd integersare generated uniquely, and I define an explicit integer-valued layerindex b(n) determined directly from this decomposition. I prove thatb(n) is well-defined for all n ≥ 1 and satisfiesb(T (n)) 1.Since b is nonnegative and strictly decreasing under T , every positiveinteger descends through finitely many layers to...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.18754217
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_18754217

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Neel Alkoraishi, \"A Binary Branch–Layer Structure and Explicit Decreasing Invariant for the Collatz Map\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.18754217 [2026]."

/-- Recorded generalization-style claim shell; the paper's theorem is not proved here.
This placeholder is the standard Collatz conjecture proposition. -/
def mainStatement : Prop := Collatz.CollatzConjecture

/-- Checked bridge facts only. -/
theorem step_one_eq : Collatz.step 1 = 4 := Collatz.step_one

theorem step_two_eq : Collatz.step 2 = 1 := Collatz.step_two

/-- Checked: every power of two reaches `1` (Mathlib-copied parity/division facts). -/
theorem powers_of_two_reach_one (k : Nat) :
    ∃ t : Nat, Collatz.orbit t (2 ^ k) = 1 :=
  Collatz.Papers.MathlibCopied.orbit_pow_two_reaches_one k

end Collatz.Papers.Journal_10_5281_zenodo_18754217
