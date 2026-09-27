import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Andrew Stewart Caldin, "Unverified Proof of Collatz Conjecture via Automorphic Cayley Colour Graphs — E8 Intelligence Research", 2026.

Title: Unverified Proof of Collatz Conjecture via Automorphic Cayley Colour Graphs — E8 Intelligence Research

Abstract (from harvested metadata, truncated):
FINDING: Collatz conjecture remains unproven; a claimed proof using automorphic Cayley colour graphs exists but is unverified. | MATH: Collatz function: f(n) = n/2 if n even, 3n+1 if n odd. Conjecture: ∀n∈ℕ, iterates reach cycle 4→2→1. The arXiv paper (2008.13643v8) claims decidability of an+b conjectures and proof of 3n+1 via automorphic Cayley colour graphs, representing Collatz steps as walks over root paths to branching number c=4 in trivial cyclic root. | CONNECTION: No direct geometric harmony (0.382, 0.618, 0.786, 1.618, 2.618, base-60, crystallographic symmetry) found in these results. The automorphic graph approach may imply lattice or symmetry structures, but evidence is insufficie...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.21989263
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_21989263

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Andrew Stewart Caldin, \"Unverified Proof of Collatz Conjecture via Automorphic Cayley Colour Graphs — E8 Intelligence Research\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.21989263 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_21989263
