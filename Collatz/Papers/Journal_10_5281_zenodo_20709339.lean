import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for K. Rottbrand, "On an Elementary Solution of the Collatz Problem", 2014.

Title: On an Elementary Solution of the Collatz Problem

Abstract (from harvested metadata, truncated):
This is a posthumous publication of a manuscript originally written in December 22, 2014 by Dr. Klaus Rottbrand, a mathematician and physicist who passed away on December 17, 2015. Please do not use the email address provided in the manuscript, as it is no longer valid. SHA256 checksum of main_collatz_0.pdf: c1fcf1bbef824c83617a0b116a0498a5d8316c55eb9b2c1c09cafac9ed1129f0 Proof of ownership (from December 21, 2022) on Ethereum blockchain (SHA256 checksum in transaction's input data): https://etherscan.io/tx/0x62745747f8f69421dfc984ebbcead10f31c56ba062f6d3af5c3061aba4416bef Copyright (C) 2026 Torben Rottbrand, Jana Rottbrand (Heirs of Dr. Klaus Rottbrand)

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.20709339
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_20709339

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "K. Rottbrand, \"On an Elementary Solution of the Collatz Problem\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.20709339 [2014]."

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

end Collatz.Papers.Journal_10_5281_zenodo_20709339
