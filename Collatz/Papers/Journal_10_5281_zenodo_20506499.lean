import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Hu, Zhaolin and Hu, Bin, "A Rigorous Proof of the Collatz Conjecture: Modulo-8 Residue Mapping and Factor Accumulation Asymmetry", 2026.

Title: A Rigorous Proof of the Collatz Conjecture: Modulo-8 Residue Mapping and Factor Accumulation Asymmetry

Abstract (from harvested metadata, truncated):
We give a rigorous full proof of the Collatz conjecture via modulo-8 residue classification and 2-adic valuation. We construct the bijective residue dynamics for reduced odd Collatz iterations, restricting upward growth to limited residue classes with bounded amplification. Using exponent accumulation inequality and mathematical induction, we exclude non-trivial periodic orbits and infinite divergent trajectories. Combined with large-scale numerical test, we verify all positive integers eventually reach 1 under the Collatz map.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.20506499
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_20506499

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Hu, Zhaolin and Hu, Bin, \"A Rigorous Proof of the Collatz Conjecture: Modulo-8 Residue Mapping and Factor Accumulation Asymmetry\", Zenodo, DOI:10.5281/zenodo.20506499 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_20506499
