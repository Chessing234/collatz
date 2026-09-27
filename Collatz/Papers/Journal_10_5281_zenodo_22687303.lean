import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for KyungUP Moon, "Critical Survivor Capacity and Integer Realizability in Accelerated Collatz Dynamics", 2026.

Title: Critical Survivor Capacity and Integer Realizability in Accelerated Collatz Dynamics

Abstract (from harvested metadata, truncated):
A persistent obstruction in the Collatz problem is the gap between finite-depth compatibility and realization by one fixed positive integer. For nested nonempty positive-integer source fibres, this preprint proves an exact realization criterion: a common positive integer exists if and only if the least source remains bounded, equivalently eventually stabilizes. It also proves an abstract critical-survivor capacity theorem. If a survivor family has entropy rate H, arithmetic scale rate Xi/2, independent information saving alpha, and state-window exponent mu, then linear survivor demand is impossible whenever mu * 2(H - alpha log 2) / Xi < 1. Under one explicitly stated dense-periodic calibrat...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.22687303
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_22687303

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "KyungUP Moon, \"Critical Survivor Capacity and Integer Realizability in Accelerated Collatz Dynamics\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.22687303 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_22687303
