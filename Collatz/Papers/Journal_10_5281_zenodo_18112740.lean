import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for KyungUp Moon, "Residue Recurrence in the Odd-Only Collatz Dynamics: Reference Implementation", 2026.

Title: Residue Recurrence in the Odd-Only Collatz Dynamics: Reference Implementation

Abstract (from harvested metadata, truncated):
This record provides a fully reproducible reference implementation and complete supporting material for the empirical study “Residue Recurrence in the Odd-Only Collatz Dynamics: An Empirical Note via Modular Projection.” The package is designed to serve as a self-contained research object, enabling independent verification and reuse. It includes: a complete and deterministic Python implementation reproducing all experiments reported in the accompanying paper, row-level CSV datasets and automatically generated CCDF (complementary cumulative distribution function) plots, a fixed, non-optional observation rule for odd-only (Syracuse) Collatz trajectories, and detailed documentation specifying e...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.18112740
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_18112740

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "KyungUp Moon, \"Residue Recurrence in the Odd-Only Collatz Dynamics: Reference Implementation\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.18112740 [2026]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Journal_10_5281_zenodo_18112740
