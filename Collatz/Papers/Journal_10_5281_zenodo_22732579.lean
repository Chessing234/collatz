import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Andrew Stewart Caldin, "Collatz Conjecture Unproven; Cayley Graph Model Offers No New Solution — E8 Intelligence Research", 2026.

Title: Collatz Conjecture Unproven; Cayley Graph Model Offers No New Solution — E8 Intelligence Research

Abstract (from harvested metadata, truncated):
FINDING: Collatz conjecture remains unproven; recent work frames it as automorphic Cayley colour graphs, with no new closed-form solution or harmonic constant emerging from the provided sources. | MATH: Collatz map: \(T(n) = n/2\) if \(n\) even, \(T(n) = 3n+1\) if \(n\) odd. Conjecture: \(\forall n \in \mathbb{N}, \exists k: T^k(n) = 1\). The arXiv paper (2008.13643v8) models the iteration as walks on a Cayley graph with root cycle \(4 \to 2 \to 1 \to 4\). No new constants or ratios appear in the search results — only the structural claim of decidability for generalized \(an+b\) maps. | CONNECTION: No direct geometric harmony (0.382, 0.618, 0.786, 1.618, 2.618) or base-60 link is present. Th...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.22732579
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_22732579

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Andrew Stewart Caldin, \"Collatz Conjecture Unproven; Cayley Graph Model Offers No New Solution — E8 Intelligence Research\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.22732579 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_22732579
