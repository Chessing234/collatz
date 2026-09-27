import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Academic Institution in Zurich (ETH Zurich), Switzerland and Xinyi Zhou, "Proof of the Collatz Conjecture Using Logical and Probabilistic Approaches", 2024.

Title: Proof of the Collatz Conjecture Using Logical and Probabilistic Approaches

Abstract (from harvested metadata, truncated):
Almost 100 years ago, the Collatz problem was introduced by German mathematician Lothar Collatz in the 1930s. It provides a predefined transformation algorithm to deal with any starting numbers in the Collatz process which are positive odd or even integers: for odd numbers, multiple it by 3 and add 1 and for even integers, divide it by 2. The Collatz conjecture states that after enough times of repetition all the natural starting numbers would eventually decrease and converge to 1. Although the Collatz conjecture has been verified to be true below a very high numerical threshold, until this day, no rigorous mathematical proof could be made which is the main focus of this research paper. After we have shown that no infinite loop could exist besides the trivial loop of 1→4 →2→1 and that no...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.33140/jctcsr.03.03.07
-/

namespace Collatz.Papers.Journal_10_33140_jctcsr_03_03_07

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Academic Institution in Zurich (ETH Zurich), Switzerland and Xinyi Zhou, \"Proof of the Collatz Conjecture Using Logical and Probabilistic Approaches\", Journal of Current Trends in Computer Science Research, DOI:10.33140/jctcsr.03.03.07 [2024]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Journal_10_33140_jctcsr_03_03_07
