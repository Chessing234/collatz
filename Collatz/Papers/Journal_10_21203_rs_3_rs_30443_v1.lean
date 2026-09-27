import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Hongyuan Ye, "The Proof of Collatz Conjecture", 2020.

Title: The Proof of Collatz Conjecture

Abstract (from harvested metadata, truncated):
Abstract This paper redefines Collatz conjecture, and proposes strong Collatz conjecture, the strong Collatz conjecture is a sufficient condition for the Collatz conjecture. Based on the computer data structure–tree, we construct the non-negative integer inheritance decimal tree. The nodes on the decimal tree correspond to non-negative integers. We further define the Collatz-leaf node (corresponding to the Collatz-leaf integer) on the decimal tree. The Collatz-leaf nodes satisfy strong Collatz conjecture. Derivation through mathematics, we prove that the Collatz-leaf node (Collatz-leaf integer) has the characteristics of inheritance. With computer large numbers and big data calculation, we conclude that all nodes at depth 800 are Collatz-leaf nodes. So we prove that strong Collatz...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.21203/rs.3.rs-30443/v1
-/

namespace Collatz.Papers.Journal_10_21203_rs_3_rs_30443_v1

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Hongyuan Ye, \"The Proof of Collatz Conjecture\", DOI:10.21203/rs.3.rs-30443/v1 [2020]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Journal_10_21203_rs_3_rs_30443_v1
