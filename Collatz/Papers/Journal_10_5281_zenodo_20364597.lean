import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Hamaji, Shinsuke, "Normalization of Natural Numbers: The Collatz Conjecture as a Case Study", 2026.

Title: Normalization of Natural Numbers: The Collatz Conjecture as a Case Study

Abstract (from harvested metadata, truncated):
Classical mathematics treats natural numbers as \emph{static results} -- pre-existingobjects detached from the \emph{generative causes} that produce them. This staticviewpoint underlies the emergence of nonstandard models, halting-typeindeterminacies, and the persistent difficulty of discrete dynamical problems such asthe Collatz conjecture. This paper introduces \emph{Natural Mathematics}, a generative framework in whichnatural numbers arise as \emph{normalized natural numbers}: execution logs generatedstep by step by local causal rules. Reconstructing the Collatz process through threelinear generative maps $2n$, $4n+3$, and $4n+1$, we show that the inverse structurebecomes bijective, the a...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.20364597
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_20364597

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Hamaji, Shinsuke, \"Normalization of Natural Numbers: The Collatz Conjecture as a Case Study\", Zenodo, DOI:10.5281/zenodo.20364597 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_20364597
