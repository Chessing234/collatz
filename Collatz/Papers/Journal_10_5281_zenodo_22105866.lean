import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Andrew Stewart Caldin, "Collatz Conjecture Unshaken: Kernel Exploit, Not Disproof; Progress Remains Topological — E8 Intelligence Research", 2026.

Title: Collatz Conjecture Unshaken: Kernel Exploit, Not Disproof; Progress Remains Topological — E8 Intelligence Research

Abstract (from harvested metadata, truncated):
FINDING: Collatz remains unsolved; the "disproof" was a Lean kernel exploit, not mathematics; recent progress is topological/ergodic, not arithmetic. | MATH: Collatz map T(n) = n/2 if n even, (3n+1)/2 if n odd; the conjecture asserts all orbits reach 1. No new constants or closed-form solutions. The arXiv paper (2601.03297v6) introduces a Borel σ-algebra and thermodynamic formalism, showing recurrence implies periodicity — but no explicit equations or ratios are given in the abstract. | CONNECTION: None found. No golden ratio, no base-60, no crystallographic symmetry. The topological approach hints at dynamical systems on compact spaces, but no geometric harmony is stated. | DEPTH: 2 — The L...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.22105866
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_22105866

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Andrew Stewart Caldin, \"Collatz Conjecture Unshaken: Kernel Exploit, Not Disproof; Progress Remains Topological — E8 Intelligence Research\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.22105866 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_22105866
