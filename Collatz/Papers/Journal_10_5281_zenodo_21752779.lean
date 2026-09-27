import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Griff gurwell, "The Collatz Map on the 2a × 3b Lattice", 2026.

Title: The Collatz Map on the 2a × 3b Lattice

Abstract (from harvested metadata, truncated):
This paper gives a complete account of the Collatz (Syracuse) map in the coordinates of the 2ᵃ × 3ᵇ lattice, assembled from three research campaigns. **Part I** establishes the zone structure. Every odd step lands off the Spine. The zone of each iterate is determined by the parity of the halving exponent (the Parity Deposition Law). The resulting zone sequence is i.i.d. Bernoulli(2/3) — a genuine theorem about the Collatz odd backbone. **Part II** solves the 3-adic half of the map. The odd step is a pure 3-adic contraction of ratio exactly 1/3. After L steps the value modulo 3ᴸ depends only on the sequence of halving exponents (the Amnesia Theorem). The zone structure is exactly orthogonal t...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.21752779
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_21752779

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Griff gurwell, \"The Collatz Map on the 2a × 3b Lattice\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.21752779 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_21752779
