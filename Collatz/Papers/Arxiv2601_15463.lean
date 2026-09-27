import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Karras, Achilleas, de Weger, Benne, "Determinants of modular Collatz graphs and variants", arXiv:2601.15463 [2026].

Title: Determinants of modular Collatz graphs and variants

Abstract (from OpenAlex metadata, truncated):
The determinants of modular Collatz graphs and the modular Conway amusical permutation graph are determined, and some interesting number theoretic properties are described.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2601.15463
-/

namespace Collatz.Papers.Arxiv2601_15463

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Karras, Achilleas and de Weger, Benne, \"Determinants of modular Collatz graphs and variants\", arXiv:2601.15463 [2026]."

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

end Collatz.Papers.Arxiv2601_15463
