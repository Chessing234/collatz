import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Sugianto, Ogin, "Tree Level Descent Theory: A Structural Framework for the Collatz Conjecture", 2026.

Title: Tree Level Descent Theory: A Structural Framework for the Collatz Conjecture

Abstract (from harvested metadata, truncated):
Inspired by the Qur'anic parable of Al-Baqarah (2:261) — a single seed producing seven ears, each bearing a hundred grains — and the tillering physiology of wheat (Triticum aestivum), this paper presents a structural framework for the Collatz conjecture based on a modular tree constructed analytically from the Collatz function. The tree is built level by level, where each level partitions all positive integers according to their residue modulo 2^{k-1}. This construction guarantees coverage: every positive integer appears in the tree. We show that the 3n+1 operation is a horizontal movement in the tree (does not increase level), while the n/2 operation is a vertical downward movement (decreas...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.20733221
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_20733221

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Sugianto, Ogin, \"Tree Level Descent Theory: A Structural Framework for the Collatz Conjecture\", Zenodo, DOI:10.5281/zenodo.20733221 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_20733221
