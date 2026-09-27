import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Liu, Xingming, "An Unconditional Proof of the Collatz Conjecture under the Modulo-6 Framework", 2026.

Title: An Unconditional Proof of the Collatz Conjecture under the Modulo-6 Framework

Abstract (from harvested metadata, truncated):
This paper presents an unconditional proof of the Collatz conjecture. The proof is based on the "modulo-6 framework"—every positive integer can be uniquely expressed as N = 2ᵃ·3ᵇ·M, where M = 1, or M = 6n−1 (yin number), or M = 6n+1 (yang number) with n ∈ ℕ ⁺ . This framework automatically strips away the factors 2 and 3 in the Collatz iteration, reducing the conjecture to the convergence of yin and yang numbers. By introducing a classification of the parameter n modulo 2ˢ, we construct a deterministic finite automaton whose state set is = (ℤ /2ˢℤ ) × {−, +}. Furthermore, we prove that all odd numbers generated along any orbit belong to a uniform algebraic form X = K·3ᵃ·m + B, where K ∈ {1,2,4}, a ≥ 0, m satisfies certain modulo conditions, and B belongs to a finite constant set. Based on...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.19709214
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_19709214

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Liu, Xingming, \"An Unconditional Proof of the Collatz Conjecture under the Modulo-6 Framework\", DOI:10.5281/zenodo.19709214 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_19709214
