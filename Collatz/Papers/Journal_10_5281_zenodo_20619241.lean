import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Ying-Chao Chen, "Deterministic Resolution of Generalized and Extended Collatz Dynamics: Arithmetic Chiral Topology and the Δ' Oracle", 2026.

Title: Deterministic Resolution of Generalized and Extended Collatz Dynamics: Arithmetic Chiral Topology and the Δ' Oracle

Abstract (from harvested metadata, truncated):
[Update: June 10, 2026 - Addition of Supplementary Companion Letter] A highly condensed supplementary document titled "Supplementary: Exact Numerical Settlement" has been added to this repository. This companion letter systematically dismantles the illusion of random walks by presenting the exact, deterministic numerical settlement for the complete 64-cell dynamic space spanning multipliers N ∈ {3, 5, 7, 9}. Key additions in the supplement include: Topological Translational Invariance: Proof that the 64-cell discrete matrix maps flawlessly onto 64 infinite isomorphic affine families (p = 4k ± 1). The Standard Affine Limit: Geometric proof that convergence strictly dictates N² < 16, inherentl...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.20619241
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_20619241

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Ying-Chao Chen, \"Deterministic Resolution of Generalized and Extended Collatz Dynamics: Arithmetic Chiral Topology and the Δ' Oracle\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.20619241 [2026]."

/-- Recorded generalization-style claim shell; the paper's theorem is not proved here.
This placeholder is the standard Collatz conjecture proposition. -/
def mainStatement : Prop := Collatz.CollatzConjecture

/-- Checked bridge facts only. -/
theorem step_one_eq : Collatz.step 1 = 4 := Collatz.step_one

theorem step_two_eq : Collatz.step 2 = 1 := Collatz.step_two

/-- Checked: every power of two reaches `1` (Mathlib-copied parity/division facts). -/
theorem powers_of_two_reach_one (k : Nat) :
    ∃ t : Nat, Collatz.orbit t (2 ^ k) = 1 :=
  Collatz.Papers.MathlibCopied.orbit_pow_two_reaches_one k

end Collatz.Papers.Journal_10_5281_zenodo_20619241
