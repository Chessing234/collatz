import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Andrew Stewart Caldin, "The Undecidable Simplicity of the Collatz Conjecture — E8 Intelligence Research", 2026.

Title: The Undecidable Simplicity of the Collatz Conjecture — E8 Intelligence Research

Abstract (from harvested metadata, truncated):
FINDING: The Collatz Conjecture (3n+1) is the simplest undecidable-looking problem; Hilbert's Entscheidungsproblem and Turing's halting theorem prove some problems are fundamentally non-computable. | MATH: Collatz map: T(n) = n/2 if n even, (3n+1)/2 if n odd. No closed-form solution; no known invariant. Turing: no algorithm can decide halting for all programs — equivalent to undecidability of Diophantine equations (Matiyasevich–Robinson–Davis–Putnam). | CONNECTION: Collatz dynamics exhibit no obvious ratio — but the 3n+1 operation introduces a factor of 3 (odd) vs 2 (even), a 3:2 ratio — the same ratio found in perfect fifth musical intervals and in the Pythagorean tuning (3/2 = 1.5). The ha...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.22065238
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_22065238

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Andrew Stewart Caldin, \"The Undecidable Simplicity of the Collatz Conjecture — E8 Intelligence Research\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.22065238 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_22065238
