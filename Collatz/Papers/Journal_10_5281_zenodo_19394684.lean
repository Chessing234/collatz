import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Yamamoto, Takeo, "A Proof of the Collatz Conjecture via the Collatz Convergence Axiom", 2026.

Title: A Proof of the Collatz Conjecture via the Collatz Convergence Axiom

Abstract (from harvested metadata, truncated):
This paper presents a proof of the Collatz conjecture. The proof rests on three structural elements: the +1 in the odd rule prohibits all loops other than {4, 2, 1}; the contraction ratio 3/4 < 1 defines a scale-invariant descent vector; and the Collatz Convergence Axiom — that every sequence σᵏ(N) converges to 1 — is proposed as a foundational premise independent of ZFC, in the tradition of the Axiom of Choice. Proof by contradiction: non-convergence violates the axiom. Formalized in Lean 4 with CI passing.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.19394684
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_19394684

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Yamamoto, Takeo, \"A Proof of the Collatz Conjecture via the Collatz Convergence Axiom\", Zenodo, DOI:10.5281/zenodo.19394684 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_19394684
