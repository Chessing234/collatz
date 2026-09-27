import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Caldin, Andrew Stewart, "Collatz Conjecture Unresolved: No New Insights from General-Audience Sources — E8 Intelligence Research", 2026.

Title: Collatz Conjecture Unresolved: No New Insights from General-Audience Sources — E8 Intelligence Research

Abstract (from harvested metadata, truncated):
FINDING: Collatz Conjecture remains unsolved; no new mathematical insight extracted from search results. | MATH: No equations, constants, or ratios provided. | CONNECTION: None identified. | DEPTH: 1 — The search results are general-audience videos, not original research. No mathematical essence to extract. Author: Andrew Stewart Caldin, Independent Researcher, UK. Part of the E8 Intelligence Research series. Platform: e8intelligence.com

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.21674760
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_21674760

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Caldin, Andrew Stewart, \"Collatz Conjecture Unresolved: No New Insights from General-Audience Sources — E8 Intelligence Research\", Zenodo, DOI:10.5281/zenodo.21674760 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_21674760
