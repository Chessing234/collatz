import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for KyungUp Moon, "Automaton Termination and Language Restriction: From Galois Theory to Collatz Dynamics", 2026.

Title: Automaton Termination and Language Restriction: From Galois Theory to Collatz Dynamics

Abstract (from harvested metadata, truncated):
We propose a unifying viewpoint: classical unsolvability results can be interpreted as failures of termination for automata operating under restricted transition languages. This framework is developed in two parallel settings. First, Galois-theoretic solvability by radicals is reinterpreted as termination of a branch automaton constrained to a radical-only language. Second, the odd-only Collatz dynamics is formalized as a labeled automaton governed by a Δ-update language. The paper isolates a general termination template separating structural properties (determinism, injectivity/irreversibility) from a single remaining arithmetic requirement (forced decrease). In the Collatz setting, this reduces the completion of termination to one explicitly stated quantitative collision principle. This...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.18115609
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_18115609

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "KyungUp Moon, \"Automaton Termination and Language Restriction: From Galois Theory to Collatz Dynamics\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.18115609 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_18115609
