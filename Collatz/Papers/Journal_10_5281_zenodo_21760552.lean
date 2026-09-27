import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Robert Polak, "Nontrivial Cycles of the Collatz Conjecture: The Smooth Model and the Diophantine Bridge", 2026.

Title: Nontrivial Cycles of the Collatz Conjecture: The Smooth Model and the Diophantine Bridge

Abstract (from harvested metadata, truncated):
Part 1 of a two-paper series on the Collatz conjecture. We study nontrivial cycles in a smooth model and build an exact Diophantine bridge Real→Integer. We prove the smooth model has no nontrivial cycles; the only discrete fixed point compatible with the original map is 1. For an odd→odd block σ with parameters (a,b), an integer fixed point exists iff D|S(σ) and n=S(σ)/D, where D=2^b−3^a and S(σ)=2^b C(σ). Using a telescoping identity and a gcd argument we exclude all orders except the trivial p_i=2 (yielding n=1). Together with the 3‑adic contraction of T(n)=(3n+1)/2^{v2(3n+1)}, potential cycles reduce to a finite congruence checklist. The companion paper “Excluding Infinite Growth” extends...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.21760552
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_21760552

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Robert Polak, \"Nontrivial Cycles of the Collatz Conjecture: The Smooth Model and the Diophantine Bridge\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.21760552 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_21760552
