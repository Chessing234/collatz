import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Andrew Stewart Caldin, "Automorphic Cayley Walks and the Unproven Collatz Conjecture — E8 Intelligence Research", 2026.

Title: Automorphic Cayley Walks and the Unproven Collatz Conjecture — E8 Intelligence Research

Abstract (from harvested metadata, truncated):
FINDING: Collatz conjecture remains unproven; recent work frames it as automorphic Cayley graph walks, with a notable Lean formalization vulnerability incident. | MATH: Core map: \(T(n) = n/2\) if \(n\) even, \(T(n) = 3n+1\) if \(n\) odd. Trivial cycle: \(4 \to 2 \to 1 \to 4\). arXiv:2008.13643v8 claims proof via Cayley colour graphs and decidability of \(an+b\) conjectures — but this is not peer-validated. No new constants or ratios emerge. | CONNECTION: The Cayley graph framing hints at group-theoretic structure, but no explicit link to golden ratio, base-60, or crystallographic symmetries is present in the provided findings. The trivial cycle \(4\to2\to1\) is a 3-cycle — a symmetry of ord...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.22138418
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_22138418

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Andrew Stewart Caldin, \"Automorphic Cayley Walks and the Unproven Collatz Conjecture — E8 Intelligence Research\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.22138418 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_22138418
