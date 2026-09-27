import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Feng, Jishe, "Binary Representation of Natural Numbers and Collatz Conjecture", 2025.

Title: Binary Representation of Natural Numbers and Collatz Conjecture

Abstract (from harvested metadata, truncated):
We propose a novel framework utilizing a full binary tree structure to systemati- 1 cally represent the set of natural numbers, which we classify into three subsets: pure odd 2 numbers, pure even numbers, and mixed numbers. Within this framework, we employ a 3 binary string representation for natural numbers and develop a comprehensive composite 4 methodology that integrate both odd- and even-number functions. Our investigation 5 centers on the iterative dynamics of the Collatz function and its reduced variant, which 6 effectively serves as a pruning mechanism for the full binary tree, enabling rigorous ex- 7 amination of the Collatz conjecture’s validity. To establish a robust foundation for this 8 conjecture, we ingeniously incorporate binary strings into an algebraic formulation that 9...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.2139/ssrn.5228418
-/

namespace Collatz.Papers.Journal_10_2139_ssrn_5228418

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Feng, Jishe, \"Binary Representation of Natural Numbers and Collatz Conjecture\", DOI:10.2139/ssrn.5228418 [2025]."

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

end Collatz.Papers.Journal_10_2139_ssrn_5228418
