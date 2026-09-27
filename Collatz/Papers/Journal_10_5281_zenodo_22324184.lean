import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Andrew Stewart Caldin, "Search Results Lack Novel Competition Problem; Only Collatz and MATH Dataset — E8 Intelligence Research", 2026.

Title: Search Results Lack Novel Competition Problem; Only Collatz and MATH Dataset — E8 Intelligence Research

Abstract (from harvested metadata, truncated):
FINDING: The search results are a mix of YouTube competition videos and one academic dataset paper; the only substantive mathematical content is the Collatz Conjecture (unsolved) and the MATH dataset (12,500 competition problems for AI benchmarking). No new solved or unsolved competition problem with novel mathematical structure is presented. MATH: - Collatz Conjecture: \( f(n) = \begin{cases} n/2 & \text{if } n \equiv 0 \pmod{2} \\ 3n+1 & \text{if } n \equiv 1 \pmod{2} \end{cases} \) — conjectured to reach 1 for all \( n \in \mathbb{N} \). No closed-form solution; no constants derived. - MATH dataset: 12,500 problems, 7 subjects (algebra, counting, geometry, etc.), full step-by-step solutio...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.22324184
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_22324184

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Andrew Stewart Caldin, \"Search Results Lack Novel Competition Problem; Only Collatz and MATH Dataset — E8 Intelligence Research\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.22324184 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_22324184
