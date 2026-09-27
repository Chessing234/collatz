import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Andrew Stewart Caldin, "Collatz, Entscheidungsproblem, and the Limits of Formal Computation — E8 Intelligence Research", 2026.

Title: Collatz, Entscheidungsproblem, and the Limits of Formal Computation — E8 Intelligence Research

Abstract (from harvested metadata, truncated):
FINDING: The Collatz Conjecture (3n+1) is the simplest undecidable-looking problem; Hilbert's Entscheidungsproblem is the canonical proof that some problems are formally uncomputable. | MATH: Collatz map: T(n) = n/2 if n even, (3n+1)/2 if n odd. No known closed form; orbit lengths scale ~log(n) empirically. Entscheidungsproblem: no general algorithm exists to decide validity of first-order logic statements (Turing 1936, Church 1936). | CONNECTION: None direct to golden ratios or base-60. However, Collatz orbits exhibit a 2-adic structure (dyadic integers) — a lattice-like symmetry in the 2-adic metric, not Euclidean. The undecidability result implies a fundamental incompleteness in algorithm...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.22122069
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_22122069

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Andrew Stewart Caldin, \"Collatz, Entscheidungsproblem, and the Limits of Formal Computation — E8 Intelligence Research\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.22122069 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_22122069
