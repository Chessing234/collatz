import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Anthony P. Walker et al., "Multi‐hypothesis comparison of Farquhar and Collatz photosynthesis models reveals the unexpected influence of empirical assumptions at leaf and global scales", 2020.

Title: Multi‐hypothesis comparison of Farquhar and Collatz photosynthesis models reveals the unexpected influence of empirical assumptions at leaf and global scales

Abstract (from harvested metadata, truncated):
concentration. Two predominant photosynthesis models are in common usage: Farquhar (FvCB) and Collatz (CBGB). However, a detailed quantitative comparison of these two models has never been undertaken. In this study, we unify the FvCB and CBGB models to a common parameter set and use novel multi-hypothesis methods (that account for both hypothesis and parameter variability) for process-level sensitivity analysis. These models represent three key biological processes: carboxylation, electron transport, triose phosphate use (TPU) and an additional model process: limiting-rate selection. Each of the four processes comprises 1-3 alternative hypotheses giving 12 possible individual models with a total of 14 parameters. To broaden inference, TBM simulations were run and novel, high-resolution...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.1111/gcb.15366
-/

namespace Collatz.Papers.Journal_10_1111_gcb_15366

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Anthony P. Walker et al., \"Multi‐hypothesis comparison of Farquhar and Collatz photosynthesis models reveals the unexpected influence of empirical assumptions at leaf and global scales\", Global Change Biology, DOI:10.1111/gcb.15366 [2020]."

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

end Collatz.Papers.Journal_10_1111_gcb_15366
