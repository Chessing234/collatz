import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Ricardo Hernández Reveles, "The Null Orbit of the Syracuse Map", 2026.

Title: The Null Orbit of the Syracuse Map

Abstract (from harvested metadata, truncated):
We identify a single arithmetic object — the null orbit \(\mathcal{N} = \{-\tfrac{1}{2} \cdot 2^{k} : k \in \mathbb{Z}\}\) of the map \(f(x) = 3x + 1\) — and show that it organises the divergence obstruction of the Syracuse map. The null \(x_0 = -1/2\) admits three independent characterisations: the algebraic fixed point of \(f\), the analytic-continuation value of \(\sum 3^i\) evaluated outside the disk of convergence, and (up to the transparent factor 2) the unique \(2\)-adic fixed point sustaining maximal expansion \(\kappa \equiv 1\). CYCLE OBSTRUCTION — The Syracuse cycle equation \((2^n - 3^T)x = S_T^*\) is not algebraically reducible to the pure map's fixed-point equation. Baker's the...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.19874522
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_19874522

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Ricardo Hernández Reveles, \"The Null Orbit of the Syracuse Map\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.19874522 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_19874522
