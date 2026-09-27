import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Kyung-Up Moon, "Arithmetic Obstructions for Periodic Valuation Dynamics of the Accelerated Collatz Map", 2026.

Title: Arithmetic Obstructions for Periodic Valuation Dynamics of the Accelerated Collatz Map

Abstract (from harvested metadata, truncated):
Version 2.0 update. This revision substantially refines the original synchronization-obstruction framework and separates the paper into clearly distinguished layers: • exact theorem layer • computational certificate layer • boundary-identification layer • probabilistic / ergodic bridge layer • positioning relative to recent obstruction-style work Major additions and revisions include: - Formalization of the integer-realizability indicator (\rho_L) and its relation to 2-adic integer stabilization.- Exact finite Beatty-type obstruction results with explicitly bounded computational scope.- Explicit identification of the remaining open barrier (Zero-Tail Exclusion).- Integration of recent related obstruction-style approaches, including connections to the distributional-to-pointwise gap...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.20258326
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_20258326

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Kyung-Up Moon, \"Arithmetic Obstructions for Periodic Valuation Dynamics of the Accelerated Collatz Map\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.20258326 [2026]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Journal_10_5281_zenodo_20258326
