import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Eduardo Diedrich, "Resolution of the Collatz Conjecture: A Rigorous Analysis of Collatz Sequences and their Unique Cycle", 2024.

Title: Resolution of the Collatz Conjecture: A Rigorous Analysis of Collatz Sequences and their Unique Cycle

Abstract (from harvested metadata, truncated):
This article presents a rigorous approach to the Collatz Conjecture, focusing on fundamental properties of Collatz sequences. We establish key properties of the Collatz function and its inverse, including surjectivity and injectivity. The structure of Collatz sequences is analyzed in depth, proving important results such as the Bounded Subsequence Property and the uniqueness of cycles. Central theorems on the properties of Collatz sequences, including the boundedness of all sequences and the nature of the unique cycle, are presented and proved. These results culminate in a complete resolution of the Collatz Conjecture, demonstrating that all Collatz sequences eventually reach the cycle {1, 4, 2}. We provide a rigorous proof of the conjecture, while emphasizing the need for thorough peer...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.20944/preprints202406.0256.v6
-/

namespace Collatz.Papers.Journal_10_20944_preprints202406_0256_v6

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Eduardo Diedrich, \"Resolution of the Collatz Conjecture: A Rigorous Analysis of Collatz Sequences and their Unique Cycle\", Preprints.org, DOI:10.20944/preprints202406.0256.v6 [2024]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Journal_10_20944_preprints202406_0256_v6
