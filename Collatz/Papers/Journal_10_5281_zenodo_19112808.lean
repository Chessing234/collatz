import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Dai, Yixian, "Proof of the Necessity of the Even-Even-Odd Structure in the Collatz Conjecture", 2026.

Title: Proof of the Necessity of the Even-Even-Odd Structure in the Collatz Conjecture

Abstract (from harvested metadata, truncated):
This paper proves that for any positive odd integer n, in the Collatz iteration, a parity structure of the form “even → even → odd” (EEO) must necessarily appear. The proof is based on modulo 4 classification and a parameter recursion method. We first address the case n ≡ 1 (mod 4). Then, for numbers n ≡ 3 (mod 4), by introducing parameters A, W, t, … and employing the method of infinite descent, we prove that such numbers will eventually transform into either n ≡ 1 (mod 4) numbers or directly enter a trajectory of multiples of 4. This result provides a structural foundation for the eventual proof of the Collatz Conjecture.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.19112808
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_19112808

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Dai, Yixian, \"Proof of the Necessity of the Even-Even-Odd Structure in the Collatz Conjecture\", Zenodo, DOI:10.5281/zenodo.19112808 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_19112808
