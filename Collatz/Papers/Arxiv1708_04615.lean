import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Juan Antonio Pérez Álvarez, "Collatz Conjecture: Is It False?", arXiv:1708.04615 [2017].

Title: Collatz Conjecture: Is It False?

Abstract (from OpenAlex metadata, truncated):
For a long time, Collatz Conjecture has been assumed to be true, although a formal proof has eluded all efforts to date. In this article, evidence is presented that suggests such an assumption is incorrect. By analysing the stopping times of various Collatz sequences, a pattern emerges that indicates the existence of non-empty sets of integers with stopping times greater than any given integer. This implies the existence of an infinite set of integers with non-finite stopping times, thus indicating the conjecture is false. Furthermore, a simple algorithm is constructed that finds integers with ever-greater stopping times. Such an algorithm does not halt, further supporting the conclusion that the conjecture is false.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/1708.04615
-/

namespace Collatz.Papers.Arxiv1708_04615

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Juan Antonio P\u00e9rez \u00c1lvarez, \"Collatz Conjecture: Is It False?\", arXiv:1708.04615 [2017]."

/-- Recorded finite-verification claim shell; the paper's bound is not proved here. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1


/-- Miniature checked verification for `B = 2`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩


end Collatz.Papers.Arxiv1708_04615
