import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Jamil Assad de Lima, "Exact Arithmetic Transducers, 2-Adic Lifting, and Periodic-Orbit Exclusion in a Collatz-Like XOR Dynamical System", 2026.

Title: Exact Arithmetic Transducers, 2-Adic Lifting, and Periodic-Orbit Exclusion in a Collatz-Like XOR Dynamical System

Abstract (from harvested metadata, truncated):
V2-SIMPLE is a phase-dependent arithmetic-bitwise dynamical system that emerged at the COSMOS Scientific Laboratory during experiments originally designed to explore alternative representations of iterative dynamics inspired by the Collatz problem. The project did not begin with the intention of creating a new conjecture or a new mathematical system. Its origin was experimental. During an investigation conducted with multiple artificial-intelligence agents running locally in the ORCHARD environment, deliberate modifications of traditional iteration rules were used as exploratory perturbations to observe which mathematical structures would survive, disappear, or emerge under changes in the dy...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.22311617
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_22311617

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Jamil Assad de Lima, \"Exact Arithmetic Transducers, 2-Adic Lifting, and Periodic-Orbit Exclusion in a Collatz-Like XOR Dynamical System\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.22311617 [2026]."

/-- Recorded nontrivial-cycle exclusion shell; the paper's theorem is not proved. -/
def mainStatement : Prop :=
  ∀ n : Nat, 1 < n → ∀ k : Nat, 0 < k → Collatz.orbit k n = n →
    ∃ j : Nat, j ≤ k ∧ Collatz.orbit j n = 1

/-- Checked: the trivial cycle through `1` returns after three steps. -/
theorem orbit_one_returns : Collatz.orbit 3 1 = 1 :=
  (Collatz.Papers.MathlibCopied.trivial_cycle).1

theorem step_branches_on_cycle :
    Collatz.step 1 = 4 ∧ Collatz.step 4 = 2 ∧ Collatz.step 2 = 1 := by
  have h := Collatz.Papers.MathlibCopied.trivial_cycle
  exact ⟨h.2.1, h.2.2.1, h.2.2.2⟩

end Collatz.Papers.Journal_10_5281_zenodo_22311617
