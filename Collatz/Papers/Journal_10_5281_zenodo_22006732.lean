import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Andrew Stewart Caldin, "Collatz Conjecture: Topological Reformulation Yields No New Proof or Constants — E8 Intelligence Research", 2026.

Title: Collatz Conjecture: Topological Reformulation Yields No New Proof or Constants — E8 Intelligence Research

Abstract (from harvested metadata, truncated):
FINDING: No new proof or breakthrough for Collatz conjecture; recent work focuses on topological/ergodic reformulation and thermodynamic formalism. | MATH: Collatz map: \( T(n) = n/2 \) if \( n \) even, \( (3n+1)/2 \) if \( n \) odd. No new constants or ratios derived. | CONNECTION: None identified — no geometric ratios, base-60, or crystallographic symmetries appear in the findings. | DEPTH: 2 — The topological/ergodic approach (arXiv:2601.03297) is a methodological shift but yields no new equations or constants; the other sources are expository or personal progress logs. No fundamental mathematical structure revealed. Author: Andrew Stewart Caldin, Independent Researcher, UK. Part of the E...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.22006732
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_22006732

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Andrew Stewart Caldin, \"Collatz Conjecture: Topological Reformulation Yields No New Proof or Constants — E8 Intelligence Research\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.22006732 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_22006732
