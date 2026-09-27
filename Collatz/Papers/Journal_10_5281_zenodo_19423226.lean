import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Huber, Karl, "Odd-Run Acceleration and the Verification of the Collatz Conjecture", 2026.

Title: Odd-Run Acceleration and the Verification of the Collatz Conjecture

Abstract (from harvested metadata, truncated):
This article refines and restructures the proof of the Collatz Conjecture established in Article 6 by introducing a new, depth‑oriented perspective on odd‑run dynamics. The work reorganizes the core argument into a modular framework based on odd‑depth transformations, k/d‑indexed acceleration maps, and genomics‑style structural decomposition. The central contribution is a clarified operator architecture that isolates the contraction mechanisms already proven in Article 6 and expresses them through a unified odd‑run calculus. This perspective reveals a more transparent hierarchy of transformation depths, enabling a cleaner separation between local acceleration behavior and global trajectory c...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.19423226
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_19423226

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Huber, Karl, \"Odd-Run Acceleration and the Verification of the Collatz Conjecture\", Zenodo, DOI:10.5281/zenodo.19423226 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_19423226
