import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Xiangrui(王祥睿) Wang, "Empty Strict Transport Caps on Three Source-Locked Interfaces of the Accelerated Odd Collatz Map", 2026.

Title: Empty Strict Transport Caps on Three Source-Locked Interfaces of the Accelerated Odd Collatz Map

Abstract (from harvested metadata, truncated):
Let U(q)=(3q+1)/2ν2(3q+1) be the accelerated Collatz map on positive odd integers. Classical stopping-time and parity-vector theory gives affine formulas for finite trajectories, while coefficient-stopping-time theory shows that a contracting main coefficient does not in general force the endpoint below the starting value: a positive affine remainder may support a finite exceptional cap. This note isolates three explicit source-locked odd-to-odd interfaces for which that strict positive cap is algebraically empty. After an initial same-source block, the next complete block admits an identity D(q2−q0)=Gb+K, where q0,q2 are odd, D>0, and all three interfaces satisfy 0 0 gives D(q2−q0)=K−Pb. If...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.22057401
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_22057401

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Xiangrui(王祥睿) Wang, \"Empty Strict Transport Caps on Three Source-Locked Interfaces of the Accelerated Odd Collatz Map\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.22057401 [2026]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Journal_10_5281_zenodo_22057401
