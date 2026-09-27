import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Rolando Zucchini, "Syracuse Conjecture Quadrature (SCQ)", 2026.

Title: Syracuse Conjecture Quadrature (SCQ)

Abstract (from harvested metadata, truncated):
After circa 2300 years (Circle Quadrature, Archimedes, Syracuse 287 - 212 BC) the history of mathematics repeats itself in a different problem. This paper presents an original research on the Syracuse Conjecture (3x+1 problem). It proposes a theoretical development aimed at solving the conjecture through a systematic approach. Theorem 2n+1 subdivides the set of odd numbers into seven subsets which have different behaviors applying algorithm of Collatz. It allows to replace the Collatz’s cycles with the cycles of links, transforming oscillating sequences into monotone decreasing sequences. Theorem of Independence allows to manage the cycles of links to our liking to reach very high main horizons and, when we decide, go back to lower horizons. In this article it’s proved that Collatz...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.19029055
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_19029055

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Rolando Zucchini, \"Syracuse Conjecture Quadrature (SCQ)\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.19029055 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_19029055
