import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Hamaji, Shinsuke, "Resolution of the Collatz Conjecture via Normalization of Natural Numbers through Type Coercion in Lean 4", 2026.

Title: Resolution of the Collatz Conjecture via Normalization of Natural Numbers through Type Coercion in Lean 4

Abstract (from harvested metadata, truncated):
Abstract This paper presents a formalized framework for constructive natural numbers and Collatz-family trees within the Lean 4 proof assistant, bridging dynamic causal local systems and traditional static mathematics. Classical mathematics, anchored by Frege and Russell's empty-set foundations, is akin to using uninitialized variables without explicit type declarations in early programming languages (such as BASIC); it relies on static accumulation while largely lacking both a causal bridge between quantum-level fluctuation causes and macroscopic results, and any mechanism to eliminate ambiguous paths or "ghost natural numbers" drifting outside the system. Inspired by Einstein's transition...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.21513968
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_21513968

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Hamaji, Shinsuke, \"Resolution of the Collatz Conjecture via Normalization of Natural Numbers through Type Coercion in Lean 4\", Zenodo, DOI:10.5281/zenodo.21513968 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_21513968
