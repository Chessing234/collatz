import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Masashi Furuta, "Proof of Collatz Conjecture Using Division Sequence", 2022.

Title: Proof of Collatz Conjecture Using Division Sequence

Abstract (from harvested metadata, truncated):
The purpose of this study is to prove the Collatz conjecture using a theorem proving system. First, the division sequence is defined as an alignment of the number of times division by 2 is performed in the Collatz operation. Then, the star conversion is defined, which is a mapping from a specific division sequence to a division sequence. Here it is important to map to some division sequence, not which division sequence. The important point is that the finite length of the division sequence does not change before and after the star conversion. In theorem proving system, we considered two parallel methods: main-proof is a claim to a computer proposition that has the same meaning as the Collatz conjecture. Theorem proving support system “Idris” was used. Moreover, we sub-proved that the 12...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.4236/apm.2022.122009
-/

namespace Collatz.Papers.Journal_10_4236_apm_2022_122009

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Masashi Furuta, \"Proof of Collatz Conjecture Using Division Sequence\", Advances in Pure Mathematics, DOI:10.4236/apm.2022.122009 [2022]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Journal_10_4236_apm_2022_122009
