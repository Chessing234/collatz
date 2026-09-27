import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Moon, Kyung-Up, "A 2-Adic State Automaton Reduction Framework for the Collatz Conjecture", 2026.

Title: A 2-Adic State Automaton Reduction Framework for the Collatz Conjecture

Abstract (from harvested metadata, truncated):
This work introduces a structural reduction framework for the Collatz conjecture based on a 2-adic state automaton. We establish several results independent of orbit convergence, including:- residue-determined valuation structure,- reduction of periodic orbits to state cycles,- a one-step shadowing bound,- and exclusion of resonance classes. These eliminate all sources of periodic behavior within the framework. The Collatz conjecture is reduced to a single remaining obstruction:the boundedness of the sibling-rank spread across refined state fibers. This work does not claim a complete proof. It provides a structural decomposition that transforms the global problem into a local boundedness que...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.19650191
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_19650191

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Moon, Kyung-Up, \"A 2-Adic State Automaton Reduction Framework for the Collatz Conjecture\", Zenodo, DOI:10.5281/zenodo.19650191 [2026]."

/-- Recorded nontrivial-cycle exclusion shell; the paper's theorem is not proved. -/
def mainStatement : Prop :=
  ∀ n : Nat, 1 < n → ∀ k : Nat, 0 < k → Collatz.orbit k n = n →
    ∃ j : Nat, j ≤ k ∧ Collatz.orbit j n = 1

/-- Checked: the trivial cycle through `1` returns after three steps. -/
theorem orbit_one_returns : Collatz.orbit 3 1 = 1 :=
  (Collatz.Papers.MathlibCopied.trivial_cycle).1

theorem step_branches_on_cycle :
    Collatz.step 1 = 4 ∧ Collatz.step 4 = 2 ∧ Collatz.step 2 = 1 := by
  have h := Collatz.Papers.MathlibCopied.trivial_cycle
  exact ⟨h.2.1, h.2.2.1, h.2.2.2⟩

end Collatz.Papers.Journal_10_5281_zenodo_19650191
