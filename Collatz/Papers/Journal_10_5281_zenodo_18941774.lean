import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Miguel Cerdá Bennassar, "2-adic Structure and the Rigid Regime in Collatz Dynamics", 2026.

Title: 2-adic Structure and the Rigid Regime in Collatz Dynamics

Abstract (from harvested metadata, truncated):
This article develops a structural framework for the study of the Collatz dynamics based on its 2-adic structure. The approach introduces cylindrical constraints on the initial parameter, a binary budget describing the irreversible consumption of bits along dynamical excursions, and an autonomous return map governing the rigid regime. It is shown that any infinite orbit must eventually enter this regime, reducing the Collatz problem to a regularity condition on the parametrization of the entry map. The paper consolidates and reorganizes several results previously developed by the author in a series of related works into a single self-contained exposition. Version 1.1 introduces minor corrections and improvements in the exposition. In particular, several statements concerning the rigid...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.18941774
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_18941774

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Miguel Cerdá Bennassar, \"2-adic Structure and the Rigid Regime in Collatz Dynamics\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.18941774 [2026]."

/-- Recorded main claim shell (structural); the paper's theorem is not proved here.
This placeholder is the standard Collatz conjecture proposition. -/
def mainStatement : Prop := Collatz.CollatzConjecture

/-- Checked bridge facts only. -/
theorem step_one_eq : Collatz.step 1 = 4 := Collatz.step_one

theorem step_two_eq : Collatz.step 2 = 1 := Collatz.step_two

/-- Checked: every power of two reaches `1` (Mathlib-copied parity/division facts). -/
theorem powers_of_two_reach_one (k : Nat) :
    ∃ t : Nat, Collatz.orbit t (2 ^ k) = 1 :=
  Collatz.Papers.MathlibCopied.orbit_pow_two_reaches_one k

end Collatz.Papers.Journal_10_5281_zenodo_18941774
