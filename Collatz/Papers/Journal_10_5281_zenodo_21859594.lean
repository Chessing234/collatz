import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Zhu, Fucheng, "A Proof of the Collatz Conjecture via Modulo‑4 Congruence Classification", 2026.

Title: A Proof of the Collatz Conjecture via Modulo‑4 Congruence Classification

Abstract (from harvested metadata, truncated):
The Collatz conjecture, also known as the Hailstone conjecture, states that for any positive integer n, define the iterative transformation rule: divide an even number by 2 directly; if n is odd, calculate 3n+1. All positive integers will converge to 1 after finite iterations.This paper classifies positive integers by modulo‑4 congruence, analyzes the iteration law when odd numbers trigger the formula 3n+1. With the infinite descent method in number theory, we prove iteration values strictly decrease finitely. Restricted by the minimum positive integer 1, iterations converge to 1 ultimately, which completes the proof of Collatz conjecture.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.21859594
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_21859594

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Zhu, Fucheng, \"A Proof of the Collatz Conjecture via Modulo‑4 Congruence Classification\", Zenodo, DOI:10.5281/zenodo.21859594 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_21859594
