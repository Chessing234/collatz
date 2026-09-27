import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Andrew Stewart Caldin, "Collatz Conjecture: Simple Rule, No Invariant, Still Unsolved — E8 Intelligence Research", 2026.

Title: Collatz Conjecture: Simple Rule, No Invariant, Still Unsolved — E8 Intelligence Research

Abstract (from harvested metadata, truncated):
FINDING: Collatz Conjecture remains unsolved; no closed-form equation or constant governs its iteration. | MATH: Iteration rule: f(n) = n/2 if n even, 3n+1 if n odd. No known invariant or conserved quantity. | CONNECTION: None. No geometric ratio, base-60, or crystallographic symmetry appears. | DEPTH: 2 — A simple rule with no discovered harmonic structure; purely number-theoretic. FINDING: The oldest unsolved problem (likely Goldbach's Conjecture or twin primes) shows no progress toward a geometric or harmonic resolution. | MATH: Goldbach: every even integer > 2 is sum of two primes. Twin primes: p, p+2 both prime. | CONNECTION: None. No ratio or symmetry emerges from prime distribution. |...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.22022618
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_22022618

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Andrew Stewart Caldin, \"Collatz Conjecture: Simple Rule, No Invariant, Still Unsolved — E8 Intelligence Research\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.22022618 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_22022618
