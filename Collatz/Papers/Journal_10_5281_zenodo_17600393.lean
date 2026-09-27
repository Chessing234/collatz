import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Hamaji, Shinsuke, "A Direct Relocation Proof of the Collatz Conjecture via Peano--Cantor Dimensional Embedding", 2025.

Title: A Direct Relocation Proof of the Collatz Conjecture via Peano--Cantor Dimensional Embedding

Abstract (from harvested metadata, truncated):
Abstract The Collatz Conjecture (CC) has long been considered unreachable within existing mathematics, as noted by giants such as Erdős and Lagarias. Yet no published proof has structurally answered this limitation. Rather than recursively verifying mapping patterns in one dimension (Indirect Recursive Proof, IRP), we relocate the defined natural numbers themselves via Cantor’s pairing function. Peano’s successor structure is dimensionally extended from the base $0:(0,1)$, encompassing the simplified CC loop $(0,1 \to 2 \to 1)$ and the full trivial cycle $(0, 1 \to 4 \to 2 \to 1)$, utilizing the deductive freedom of initial values as a structural guarantee. This yields a Direct Relocation Pr...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.17600393
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_17600393

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Hamaji, Shinsuke, \"A Direct Relocation Proof of the Collatz Conjecture via Peano--Cantor Dimensional Embedding\", Zenodo, DOI:10.5281/zenodo.17600393 [2025]."

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

end Collatz.Papers.Journal_10_5281_zenodo_17600393
