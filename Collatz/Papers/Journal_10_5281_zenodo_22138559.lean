import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Andrew Stewart Caldin, "Collatz Conjecture: The Simplest Unsolved Math Problem — E8 Intelligence Research", 2026.

Title: Collatz Conjecture: The Simplest Unsolved Math Problem — E8 Intelligence Research

Abstract (from harvested metadata, truncated):
FINDING: The search results are predominantly clickbait YouTube titles and a dataset paper — no actual unsolved competition problem with mathematical content is presented. The only substantive mathematical object is the Collatz Conjecture, referenced as "the simplest math problem no one can solve." MATH: Collatz map: \( T(n) = \begin{cases} n/2 & \text{if } n \equiv 0 \pmod{2} \\ 3n+1 & \text{if } n \equiv 1 \pmod{2} \end{cases} \). Conjecture: for all \( n \in \mathbb{N} \), iterating \( T \) eventually reaches 1. No closed-form, no known invariant, no proven bound on stopping time. The MATH dataset (arXiv:2103.03874) contains 12,500 competition problems — but no specific unsolved problem i...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.22138559
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_22138559

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Andrew Stewart Caldin, \"Collatz Conjecture: The Simplest Unsolved Math Problem — E8 Intelligence Research\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.22138559 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_22138559
