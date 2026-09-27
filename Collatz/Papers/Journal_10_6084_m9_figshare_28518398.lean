import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Cerdà Bennassar, Miquel, "Demonstration of the Uniqueness of the Loop in Collatz Sequences Based on Digital Roots and Graph Theory.", 2025.

Title: Demonstration of the Uniqueness of the Loop in Collatz Sequences Based on Digital Roots and Graph Theory.

Abstract (from harvested metadata, truncated):
This study demonstrates that the loop 4, 2, 1, 4 is the only possible loop in Collatz sequences, using adetailed analysis of the digital roots of the numbers involved and modeling the system as a directedgraph. Through this approach, it is shown that the mathematical properties of digital roots and therules of the Collatz conjecture make the existence of other loops impossible. It is concluded that,based on this analysis, no other loops can exist in Collatz sequences.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.6084/m9.figshare.28518398
-/

namespace Collatz.Papers.Journal_10_6084_m9_figshare_28518398

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Cerdà Bennassar, Miquel, \"Demonstration of the Uniqueness of the Loop in Collatz Sequences Based on Digital Roots and Graph Theory.\", figshare, DOI:10.6084/m9.figshare.28518398 [2025]."

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

end Collatz.Papers.Journal_10_6084_m9_figshare_28518398
