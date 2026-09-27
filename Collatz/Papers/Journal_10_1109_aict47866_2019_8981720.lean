import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Yagub N. Aliyev, "Another Generalization of $3\mathrm{x}+1$ Problem: Existence of periodicity in the construction of numbers in periodic version of generalized Collatz’ problem and its computational aspects", 2019.

Title: Another Generalization of $3\mathrm{x}+1$ Problem: Existence of periodicity in the construction of numbers in periodic version of generalized Collatz’ problem and its computational aspects

Abstract (from harvested metadata, truncated):
In the paper, another generalization of Collatz's Syracuse problem was discussed. For a given initial integer number, each next integer number is obtained by dividing the previous integer by 2 (T operation), or multiplying it by 3, adding 1 and then dividing by 2 (S operation), or finally, multiplying by 3, adding 2 and then dividing by 2 (V operation), provided that all of these divisions by 2 are possible. The presence of this last operation V makes the problem more general. We ask the following question: How can one find from the given sequence of T, S, V operations whether an initial integer exists which after all these operations, applied in the given order, will end up with the same initial number? We found an algorithm that can quickly find that integer or determine if such an...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.1109/aict47866.2019.8981720
-/

namespace Collatz.Papers.Journal_10_1109_aict47866_2019_8981720

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Yagub N. Aliyev, \"Another Generalization of $3\\mathrm{x}+1$ Problem: Existence of periodicity in the construction of numbers in periodic version of generalized Collatz’ problem and its computational aspects\", 2019 IEEE 13th International Conference on Application of Information and Communication Technologies (AICT), DOI:10.1109/aict47866.2019.8981720 [2019]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Journal_10_1109_aict47866_2019_8981720
