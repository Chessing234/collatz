import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Lee, Byoungwoo, "A Proof of the Collatz Conjecture via the Spectral Gap of an Entropic Laplacian (v2.0)", 2025.

Title: A Proof of the Collatz Conjecture via the Spectral Gap of an Entropic Laplacian (v2.0)

Abstract (from harvested metadata, truncated):
This record presents version 2.0 of this research series and contains the complete, unconditional proof of the Collatz Conjecture, fulfilling the framework established in v1.0 (DOI: 10.5281/zenodo.15700668). This final paper synthesizes a multi-year research program, demonstrating that the conjecture can be resolved by translating the discrete arithmetic problem into the spectral theory of an "entropic Laplacian" operator on a 2-adic moduli space. The core achievement is a rigorous proof that this operator possesses a strictly positive spectral gap, which analytically forces all Collatz orbits to converge to the unique trivial cycle. This Zenodo record contains the main proof paper ("Collatz...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.15834325
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_15834325

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Lee, Byoungwoo, \"A Proof of the Collatz Conjecture via the Spectral Gap of an Entropic Laplacian (v2.0)\", Zenodo, DOI:10.5281/zenodo.15834325 [2025]."

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

end Collatz.Papers.Journal_10_5281_zenodo_15834325
