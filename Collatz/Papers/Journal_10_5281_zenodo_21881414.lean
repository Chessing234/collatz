import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Nikolai Arkhipov, "«Quadratic Reducer and Coordinate-Parabolic Potential Matrix: The Definitive Geometric Proof of the Collatz Conjecture»", 2026.

Title: «Quadratic Reducer and Coordinate-Parabolic Potential Matrix: The Definitive Geometric Proof of the Collatz Conjecture»

Abstract (from harvested metadata, truncated):
This combined work presents the comprehensive solution to non-linear numerical sequences (3n+1 systems). The first part delivers the fundamental derivation of the core quadratic equation 3x² - 4x - 4 = 0 from the internal structure of bit distribution and identifies its central attractor (the zero-anchor x = 2). The second part executes a transition to a continuous coordinate field of Y potentials. Based on this parabolic blueprint, the system determines the output height energy levels for any odd number sequence with absolute, micron-level precision across infinite macro-scales, including billions. The dynamics of column shifts are fully verified through the law of coordinate height differe...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.21881414
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_21881414

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Nikolai Arkhipov, \"«Quadratic Reducer and Coordinate-Parabolic Potential Matrix: The Definitive Geometric Proof of the Collatz Conjecture»\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.21881414 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_21881414
