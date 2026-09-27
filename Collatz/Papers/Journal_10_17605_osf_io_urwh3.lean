import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Motohiro Hamaguchi, "Redefinition of Even Numbers as a * 2^n - 2 and Proof of Hierarchical Locks and Universal Fractal Convergence in Collatz Space", 2026.

Title: Redefinition of Even Numbers as a * 2^n - 2 and Proof of Hierarchical Locks and Universal Fractal Convergence in Collatz Space

Abstract (from harvested metadata, truncated):
This project provides a deterministic proof of Collatz conjecture convergence using a novel binary topology representation (a * 2^n - 2) and large-scale empirical simulations (n=150, n=320).

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.17605/osf.io/urwh3
-/

namespace Collatz.Papers.Journal_10_17605_osf_io_urwh3

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Motohiro Hamaguchi, \"Redefinition of Even Numbers as a * 2^n - 2 and Proof of Hierarchical Locks and Universal Fractal Convergence in Collatz Space\", DOI:10.17605/osf.io/urwh3 [2026]."

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

end Collatz.Papers.Journal_10_17605_osf_io_urwh3
