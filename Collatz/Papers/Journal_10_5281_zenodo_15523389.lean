import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Fradkin, Yuval, "Energetic Proof: Energetic Proof: Formal Reformulation of the Collatz Conjecture via Even-Only Transition Sequences", 2026.

Title: Energetic Proof: Energetic Proof: Formal Reformulation of the Collatz Conjecture via Even-Only Transition Sequences

Abstract (from harvested metadata, truncated):
Abstract I present a complete proof of the Collatz Conjecture through an energetic framework that reformulates the problem as a dynamical system operating exclusively on even integers. The key innovation is the elimination of odd-step analysis by defining a direct even-to-even transition function T that captures the essential dynamics of Collatz sequences while bypassing the irregular behavior of odd values. Main Results: Reformulation: Every Collatz sequence can be equivalently analyzed as a sequence of even integers {xᵢ} governed by xᵢ₊₁ = T(xᵢ), where T(x) maps each even number to the next even number in its Collatz orbit. Energy Function: We introduce E(x) = log₂(x) as a strictly monoton...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.15523389
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_15523389

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Fradkin, Yuval, \"Energetic Proof: Energetic Proof: Formal Reformulation of the Collatz Conjecture via Even-Only Transition Sequences\", Zenodo, DOI:10.5281/zenodo.15523389 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_15523389
