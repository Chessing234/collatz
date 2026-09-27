import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Andrew Stewart Caldin, "Collatz Conjecture Unproven; Unverified Cayley Graph Approach Emerges — E8 Intelligence Research", 2026.

Title: Collatz Conjecture Unproven; Unverified Cayley Graph Approach Emerges — E8 Intelligence Research

Abstract (from harvested metadata, truncated):
FINDING: No proof of Collatz conjecture found; one preprint claims automorphic Cayley graph approach but remains unverified. | MATH: Collatz map: f(n) = n/2 if n even, 3n+1 if n odd. Conjecture: ∀ n ∈ ℕ, iterates reach cycle 4→2→1→4. | CONNECTION: None identified. The automorphic Cayley graph approach may hint at lattice symmetries, but no explicit geometric ratios (0.382, 0.618, 0.786, 1.618, 2.618) or base-60 connections appear in the provided abstracts. | DEPTH: 2 — No substantive mathematical advance; the field remains open. The only potential depth is the structural link to automorphic graphs, but it is not validated. Author: Andrew Stewart Caldin, Independent Researcher, UK. Part of th...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.22022612
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_22022612

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Andrew Stewart Caldin, \"Collatz Conjecture Unproven; Unverified Cayley Graph Approach Emerges — E8 Intelligence Research\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.22022612 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_22022612
