import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Chen, Ying-Chao, "The AACC Theory(Absolute Asymptotic Convergence Condition): A Novel Computational Framework and Topological Invariant for the Global Decidability of Extended Collatz Mappings", 2026.

Title: The AACC Theory(Absolute Asymptotic Convergence Condition): A Novel Computational Framework and Topological Invariant for the Global Decidability of Extended Collatz Mappings

Abstract (from harvested metadata, truncated):
===================================================================== CORE SCIENTIFIC MANUSCRIPTS & COMPUTATIONAL ARCHITECTURE This repository serves as the definitive open-science archive containing the complete theoretical framework, the condensed theorem preprint, and the arbitrary-precision computational suite deployed to formally resolve the deterministic structure and global decidability of generalized affine mappings. By transitioning from stochastic heuristics to a pure topological physics paradigm, this repository provides both the rigorous algebraic proofs and the extreme-scale empirical engines required to bypass Gödel's incompleteness, formally reducing Collatz-like discrete dyna...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.21251537
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_21251537

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Chen, Ying-Chao, \"The AACC Theory(Absolute Asymptotic Convergence Condition): A Novel Computational Framework and Topological Invariant for the Global Decidability of Extended Collatz Mappings\", Zenodo, DOI:10.5281/zenodo.21251537 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_21251537
