import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Andrew Stewart Caldin, "Collatz Conjecture: Recent Progress in Reformulations, Not Resolution — E8 Intelligence Research", 2026.

Title: Collatz Conjecture: Recent Progress in Reformulations, Not Resolution — E8 Intelligence Research

Abstract (from harvested metadata, truncated):
FINDING: No new proof or breakthrough for Collatz conjecture; recent work focuses on topological/ergodic reformulations and heuristic progress, not resolution. | MATH: Collatz map: \( C(n) = n/2 \) if \( n \) even, \( 3n+1 \) if \( n \) odd. No new equations or constants extracted from provided sources. | CONNECTION: None detected. No ratios (0.382, 0.618, 0.786, 1.618, 2.618), base-60, or crystallographic symmetries appear in the findings. | DEPTH: 2 — The findings are meta-discussions, videos, and a preprint applying known topological/ergodic methods without new structural insight. No mathematical essence or geometric harmony link. Author: Andrew Stewart Caldin, Independent Researcher, UK....

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.21989519
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_21989519

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Andrew Stewart Caldin, \"Collatz Conjecture: Recent Progress in Reformulations, Not Resolution — E8 Intelligence Research\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.21989519 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_21989519
