import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Ling, Xie, "Collatz conjecture(3X+1)There is a hidden theorem ω1: If α Establishment, necessity (3α+ 1) Established", 2021.

Title: Collatz conjecture(3X+1)There is a hidden theorem ω1: If α Establishment, necessity (3α+ 1) Established

Abstract (from harvested metadata, truncated):
Abstract From a number theory “Collatz conjecture (3X+1)”, Human beings use a large amount of computer data, so far no counterexample has been found. Does mathematical logic support " Collatz conjecture (3X+1)? Collatz conjecture (3X+1) There is a hidden theorem ω1 : If x holds, it must be (3X+1). In reality, human beings will only (3X+1) deduce that x holds.Example: an integer a, and a = 3b +1, b∈N. If b→3x +1 holds. There must be: a→3x +1 is established.In this way, there is no need to deduce (3b + 1).

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.21203/rs.3.rs-952109/v1
-/

namespace Collatz.Papers.Journal_10_21203_rs_3_rs_952109_v1

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Ling, Xie, \"Collatz conjecture(3X+1)There is a hidden theorem ω1: If α Establishment, necessity (3α+ 1) Established\", DOI:10.21203/rs.3.rs-952109/v1 [2021]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Journal_10_21203_rs_3_rs_952109_v1
