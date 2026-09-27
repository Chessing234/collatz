import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Andrew Stewart Caldin, "Collatz Conjecture Unresolved: No New Insights from Non-Technical Summaries — E8 Intelligence Research", 2026.

Title: Collatz Conjecture Unresolved: No New Insights from Non-Technical Summaries — E8 Intelligence Research

Abstract (from harvested metadata, truncated):
FINDING: Collatz Conjecture remains unsolved; no new mathematical insight or equation extracted from search results. | MATH: Collatz function: f(n) = n/2 if n even, 3n+1 if n odd. No constants or ratios derived. | CONNECTION: None identified. The problem involves integer dynamics, not geometric ratios or symmetries. | DEPTH: 1 — The search results are popular science summaries, not original research. No mathematical essence or geometric harmony found. Author: Andrew Stewart Caldin, Independent Researcher, UK. Part of the E8 Intelligence Research series. Platform: e8intelligence.com

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.21674682
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_21674682

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Andrew Stewart Caldin, \"Collatz Conjecture Unresolved: No New Insights from Non-Technical Summaries — E8 Intelligence Research\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.21674682 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_21674682
