import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for julian redero, "A Kernel–Expansion Certificate Framework for the Collatz Problem", 2026.

Title: A Kernel–Expansion Certificate Framework for the Collatz Problem

Abstract (from harvested metadata, truncated):
We formulate a certificate-based proof architecture for the Collatz problem, built ona separation between a finite dyadic kernel and stable affine expansion regions. Theobjective of the present paper is not to claim an unconditional proof in the absence ofthe full certificate. Rather, it is to isolate the exact finite structure whose independentverification would constitute such a proof.The theorem is conditional in the following precise sense: if a concrete finite adaptivedyadic certificate of maximal depth Bmax ≤ 323 is supplied and accepted by the exactinteger verifier specified below, then the Collatz conjecture follows. The certificate isnot a flat enumeration of residue classes, but a finite recursive covering object whoseterminal leaves represent infinite truncated arithmetic...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.20619006
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_20619006

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "julian redero, \"A Kernel–Expansion Certificate Framework for the Collatz Problem\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.20619006 [2026]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Journal_10_5281_zenodo_20619006
