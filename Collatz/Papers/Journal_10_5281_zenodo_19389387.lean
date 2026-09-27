import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Dillip Kumar Mahapatra, "Computational Verification of the Dissolution of the Collatz Conjecture: Spiral Strap Topology, Falsification Protocols, and the Emergence of Geometry from the Primordial Invariant ∆ = 4 ln 99", 2026.

Title: Computational Verification of the Dissolution of the Collatz Conjecture: Spiral Strap Topology, Falsification Protocols, and the Emergence of Geometry from the Primordial Invariant ∆ = 4 ln 99

Abstract (from harvested metadata, truncated):
The Collatz conjecture – the statement that repeated iteration of the map C(n) = n/2for even n and C(n) = 3n + 1 for odd n always reaches the cycle 1 → 4 → 2 → 1 – hasresisted proof for nearly a century. Paper-39 of the KUTE-DCEOS series provided CollatzConjecture dissolution by showing that divergence is topologically impossible. That proofrests on the ergodic dissipation E[X] = ln(3/4), the Dalvi Dictact (topological completionto the integer base B = 99), the self-born law (Swayambhu Niyam) generating the infinitesequence 9, 99, 999, . . . and the universal constant 1 − e−1, and the quadratic regulatorQ(x) = (x − 99)(396 − x) from which π and √π emerge as kernel integrals.This paper presen...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.19389387
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_19389387

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Dillip Kumar Mahapatra, \"Computational Verification of the Dissolution of the Collatz Conjecture: Spiral Strap Topology, Falsification Protocols, and the Emergence of Geometry from the Primordial Invariant ∆ = 4 ln 99\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.19389387 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_19389387
