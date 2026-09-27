import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Bert-Willem Geesink, "The transformation of the sequence 2n-1 when applying the Collatz algorithm", 2024.

Title: The transformation of the sequence 2n-1 when applying the Collatz algorithm

Abstract (from harvested metadata, truncated):
The transformation of the sequence 2n-1 when applying the Collatz algorithm, is described in this document using modular arithmetic (mod 2, mod 3 and mod 6). As sequences of the form xn-y can either be odd number sequences, even number sequences or mixed parity sequences, a methodology to split these mixed parity sequences into odd and even sub sequences, is introduced as well. Only the transformation of the sequence 2n-1 is described because it represents all positive odd integers. Also, the proof that the conjecture's validity for odd numbers implies its validity for even numbers is given in this document.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.31219/osf.io/fg83e
-/

namespace Collatz.Papers.Journal_10_31219_osf_io_fg83e

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Bert-Willem Geesink, \"The transformation of the sequence 2n-1 when applying the Collatz algorithm\", DOI:10.31219/osf.io/fg83e [2024]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Journal_10_31219_osf_io_fg83e
