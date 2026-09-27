import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Weilong Wu, "Generalized 3n+k Collatz Map: Cycle‑Equation and Symbol‑Dichotomy Theorem", 2026.

Title: Generalized 3n+k Collatz Map: Cycle‑Equation and Symbol‑Dichotomy Theorem

Abstract (from harvested metadata, truncated):
This paper investigates generalized 3n+k Collatz maps for odd integer values of k . A unified algebraic framework is constructed to characterise periodic orbits. We prove a general cycle existence condition and a symbol‑dichotomy principle that accounts for the different dynamical behaviour observed for positive and negative shift parameters. The recursive structure of cycle‑related combinatorial invariants is discussed. Numerical exploration for the case k=5 validates our framework, revealing that long‑cycle parameters correspond to intermediate continued‑fraction approximations. This work offers new structural insight into arithmetic dynamics associated with Collatz‑type iterations.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.21845276
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_21845276

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Weilong Wu, \"Generalized 3n+k Collatz Map: Cycle‑Equation and Symbol‑Dichotomy Theorem\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.21845276 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_21845276
