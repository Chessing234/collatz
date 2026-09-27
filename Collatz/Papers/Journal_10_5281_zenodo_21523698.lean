import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Changming Qiu, "On Binary Carry Dynamics Tools for the 3n+1 Problem", 2026.

Title: On Binary Carry Dynamics Tools for the 3n+1 Problem

Abstract (from harvested metadata, truncated):
This paper develops a set of binary carry dynamics tools for analyzing the 3n+1 problem. The Collatz compressed map is equivalently transformed into a carry propagation process on binary sequences. A configuration classification theorem is established, and the concepts of carry toggle pairs, the order parameter Ψ, and the carry death theorem are introduced. The paper rigorously establishes the following: (1) local annihilation of carry toggle pairs necessarily induces a strict decrease in the global count P; (2) the behavior of the potential function Ψ under each step type is analyzed and precisely quantified; (3) Ψ = 0 if and only if n = 1. The complete lemma system for the carry death theo...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.21523698
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_21523698

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Changming Qiu, \"On Binary Carry Dynamics Tools for the 3n+1 Problem\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.21523698 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_21523698
