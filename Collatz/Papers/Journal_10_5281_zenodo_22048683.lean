import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Jean Lauro Muller, "A Dyadic Functional for the Accelerated Collatz Map", 2026.

Title: A Dyadic Functional for the Accelerated Collatz Map

Abstract (from harvested metadata, truncated):
We introduce a weighted dyadic functional µ associated with the accelerated 3x+1 map and establish its basic analytic properties. We prove that µ is well-defined for all positive odd integers, derive a functional equation relating µ(n) and µ(T(n)), and exhibit its non-injectivity. The functional takes values in the dyadic rationals Z[1/2] for all orbits that reach 1. We present computational data for 5 × 10^5 odd integers and discuss a heuristic interpretation of the observed mean value µ¯ ≈ 2.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.22048683
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_22048683

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Jean Lauro Muller, \"A Dyadic Functional for the Accelerated Collatz Map\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.22048683 [2026]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Journal_10_5281_zenodo_22048683
