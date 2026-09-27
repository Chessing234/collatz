import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Lee, Byoungwoo, "A Proof of the Collatz Conjecture via the Spectral Gap of an Entropic Laplacian (Version v3.0, Main Proof Only)", 2025.

Title: A Proof of the Collatz Conjecture via the Spectral Gap of an Entropic Laplacian (Version v3.0, Main Proof Only)

Abstract (from harvested metadata, truncated):
This release (Version v3.0, Main Proof Only) presents a complete and unconditional analytic proof of the Collatz conjecture based on the spectral gap of the entropic Laplacian on the Collatz moduli space \( M_C \simeq \mathbb{Z}_2 \). The paper establishes the global Poincaré inequality and uniform Dirichlet spectral gap \[\lambda_1 \ge \frac{p_e^2}{32} > 0,\]showing that every orbit of the Collatz map is exponentially absorbed into a finite verified domain \( B_{K_0} = \{1,2,\dots,K_0\} \).Combined with the finite verification of all integers up to \( K_0 \), this implies that every \( n \in \mathbb{N} \)eventually reaches the unique cycle \( \{1,2,4\} \), completing the Collatz conjecture....

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.17271603
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_17271603

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Lee, Byoungwoo, \"A Proof of the Collatz Conjecture via the Spectral Gap of an Entropic Laplacian (Version v3.0, Main Proof Only)\", Zenodo, DOI:10.5281/zenodo.17271603 [2025]."

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

end Collatz.Papers.Journal_10_5281_zenodo_17271603
