import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Jishe Feng, "Using Binary and Bezout Identity to Prove Collatz Conjecture", arXiv:2502.01743 [2025].

Title: Using Binary and Bezout Identity to Prove Collatz Conjecture

Abstract (from OpenAlex metadata, truncated):
We propose a novel framework utilizing a full binary tree structure to systematically represent the set of natural numbers, which we classify into three subsets: pure odd numbers, pure even numbers, and mixed numbers. Within this framework, we employ a binary string representation for natural numbers and develop a comprehensive composite methodology that integrate both odd- and even-number functions. Our investigation centers on the itera- tive dynamics of the Collatz function and its reduced variant, which effectively serves as a pruning mechanism for the full binary tree, enabling rigorous exam- ination of the Collatz conjecture’s validity. To establish a robust foundation for this conjecture, we ingeniously incorporate binary strings into an algebraic formulation that fundamentally captures the intrinsic properties of the Col- latz sequence. Through this analytical framework, we demon

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2502.01743
-/

namespace Collatz.Papers.Arxiv2502_01743

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Jishe Feng, \"Using Binary and Bezout Identity to Prove Collatz Conjecture\", arXiv:2502.01743 [2025]."

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

end Collatz.Papers.Arxiv2502_01743
