import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Motohiro Hamaguchi, "Mathematical Proof of Non-Divergence in the 3n+3 Model and Local Control of Parity Interference in 3n+d Modified Collatz Space", 2026.

Title: Mathematical Proof of Non-Divergence in the 3n+3 Model and Local Control of Parity Interference in 3n+d Modified Collatz Space

Abstract (from harvested metadata, truncated):
This paper systematically elucidates the dynamics of parity interference in the generalized Collatz problem (the 3n+d problem, where d is an odd constant) based on the structure of binary bitstreams and Kummer's theorem, with the primary objective of formalizing the convergence properties (the condition for reaching a value strictly less than the initial value) within each respective space. First, by examining the peripheral models for d = -1, 5, 7, 9, 11, and 13, this study presents a three-stage algorithm that stratifies an infinite set of initial values into distinct layers (mod-classifications) based on their lower bit patterns. The results demonstrate that the vast majority of these per...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.17605/osf.io/my2n5
-/

namespace Collatz.Papers.Journal_10_17605_osf_io_my2n5

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Motohiro Hamaguchi, \"Mathematical Proof of Non-Divergence in the 3n+3 Model and Local Control of Parity Interference in 3n+d Modified Collatz Space\", DOI:10.17605/osf.io/my2n5 [2026]."

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

end Collatz.Papers.Journal_10_17605_osf_io_my2n5
