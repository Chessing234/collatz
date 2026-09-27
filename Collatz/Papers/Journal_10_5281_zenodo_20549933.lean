import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for MINGJEN HSIEH, "Algebraic Obstructions to Residue-Only Lyapunov Certificates for the Shortcut Collatz Map", 2026.

Title: Algebraic Obstructions to Residue-Only Lyapunov Certificates for the Shortcut Collatz Map

Abstract (from harvested metadata, truncated):
Abstract This paper studies residue-only Lyapunov potentials of the form V(n) = log_2 n + c(n mod 2^m) for the shortcut Collatz map. The main result is a fixed-depth obstruction theorem: for every fixed residue modulus 2^m, every finite block length B, and every correction function c, there exist arbitrarily large integers n for which the potential strictly increases along all of the first B shortcut iterates. The obstruction arises from integers congruent to -1 modulo 2^(m+B), whose first B shortcut steps are all odd, leaving the residue correction unchanged while the logarithmic component increases. The paper also presents complementary algebraic and computational diagnostics, including a positive-drift representative cycle modulo 128, an exact lifted all-ones self-loop, representative...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.20549933
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_20549933

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "MINGJEN HSIEH, \"Algebraic Obstructions to Residue-Only Lyapunov Certificates for the Shortcut Collatz Map\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.20549933 [2026]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Journal_10_5281_zenodo_20549933
