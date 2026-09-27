import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Dillon, Timothy Joseph, "Compressed Odd Dynamics and a Structural Proof of the Collatz Conjecture", 2026.

Title: Compressed Odd Dynamics and a Structural Proof of the Collatz Conjecture

Abstract (from harvested metadata, truncated):
We study the compressed odd Collatz map U (n) = 3n+1 2β(n) , where β(n) = v2(3n + 1), and present a reduction-and-closure proof of the Collatz conjecture based on exact entropic persis- tence, deep-block contraction, structural exclusion, and residual-family elimination. The argu- ment develops exact identities, deterministic contraction in sufficiently deep syntropic blocks, a segment-model exclusion principle for mixed words, linear control of shallow fragmentation, deep-return dominance, and a finite near-critical candidate theorem with global incompatibility. We prove that each residual family is ∅ by explicit elimination theorems for the deep, segment- critical, shallow-return, and near...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.19562657
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_19562657

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Dillon, Timothy Joseph, \"Compressed Odd Dynamics and a Structural Proof of the Collatz Conjecture\", Zenodo, DOI:10.5281/zenodo.19562657 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_19562657
