import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Nathan Humphrey, "A Symbolic Prefix Decomposition of the Collatz Map and Its Empirical Determination of Per Class Statistics", 2026.

Title: A Symbolic Prefix Decomposition of the Collatz Map and Its Empirical Determination of Per Class Statistics

Abstract (from harvested metadata, truncated):
This paper establishes properties of the prefix decomposition and presents empirical evidence that thedecomposition’s terminal value afinal determines per-class statistics of the total stopping time σ on oddintegers in residue class r mod 2k. The contribution has two parts. The algebraic part, presented in §3,establishes properties of the prefix iteration that are deductive consequences of the symbolic state’s paritydynamics. The principal algebraic results are: the termination theorem (§3.2; the prefix iteration consumesexactly k even-step applications and at most k odd-step applications, with terminal afinal ∈ {3j : 1 ≤ j ≤ k});the binomial j-distribution lemma (§3.5; the count of odd classes mod 2k with j odd-step applications isk−1j−1 , proven via the classical Syracuse parity-vector...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.20299733
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_20299733

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Nathan Humphrey, \"A Symbolic Prefix Decomposition of the Collatz Map and Its Empirical Determination of Per Class Statistics\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.20299733 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_20299733
