import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Eduardo Diedrich, "The Collatz Conjecture: A New Proof Using Algebraic Inverse Tree", 2024.

Title: The Collatz Conjecture: A New Proof Using Algebraic Inverse Tree

Abstract (from harvested metadata, truncated):
The Collatz Conjecture has intrigued mathematicians for decades.It proposes that iterating the function C(n) = n/2 for even n or C(n) = 3n + 1 for odd n on any natural number ultimately leads to the cycle 1, 2, 4. Despite its simplicity, the conjecture's unpredictable nature complicates proofs.Algebraic Inverse Trees (AITs) offer a novel approach by modeling Collatz sequences in reverse.AITs recursively track numeric pathways using C -1 , enabling global analysis, anomaly detection, and convergence estimation.They exhibit topological equivalence with Collatz sequences, allowing for the transfer of key properties.By establishing mappings between AITs and Collatz sequences, discrete systems can exchange cardinal attributes, facilitating convergence proofs.This multidimensional strategy...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.51483/ijpamr.4.1.2024.34-79
-/

namespace Collatz.Papers.Journal_10_51483_ijpamr_4_1_2024_34_79

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Eduardo Diedrich, \"The Collatz Conjecture: A New Proof Using Algebraic Inverse Tree\", International Journal of Pure and Applied Mathematics Research, DOI:10.51483/ijpamr.4.1.2024.34-79 [2024]."

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

end Collatz.Papers.Journal_10_51483_ijpamr_4_1_2024_34_79
