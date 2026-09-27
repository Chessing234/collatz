import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Yoshiki Ueoka et al., "Canonical Chain–Node Encoding and Finite-Width Return Renormalization for the Accelerated Collatz Map", 2026.

Title: Canonical Chain–Node Encoding and Finite-Width Return Renormalization for the Accelerated Collatz Map

Abstract (from harvested metadata, truncated):
We select a canonical orientation of an alternating signed-binary representation of positive odd integers and refine it into a chain--node encoding, called the canonical CPE. The signed representation itself is classical in spirit and closely matches the alternating binary system of Hajnal; the present contribution begins with its Collatz-adapted canonical selection and CPE dynamics. The lowest chain length is exactly the $2$-adic valuation removed by the accelerated Collatz map. A zero-node statistic $H_K$ gives an exact finite-descent reformulation of the positive Collatz conjecture and reduces any hypothetical counterexample to a barrier orbit. Barrier orbits split into an infinite-width-growth branch and a fixed-width neutral-cycle branch. For the latter we derive a sequence of exact...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.21760714
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_21760714

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Yoshiki Ueoka et al., \"Canonical Chain–Node Encoding and Finite-Width Return Renormalization for the Accelerated Collatz Map\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.21760714 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_21760714
