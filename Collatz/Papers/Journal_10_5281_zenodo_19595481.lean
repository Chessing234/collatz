import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Fogliato Matteo, "Structural Proof of the Collatz Conjecture: Cycle Exclusion and Global Stability", 2026.

Title: Structural Proof of the Collatz Conjecture: Cycle Exclusion and Global Stability

Abstract (from harvested metadata, truncated):
This paper presents a formal structural derivation demonstrating the absence of non-trivial cycles in the Collatz ($3x+1$) function. By unifying the Fogliato Inversion Formula (Diophantine integrity filter) with the Metric Amputation Theorem (phase space contraction) and Baker’s Theorem on linear forms in logarithms, we establish a finite complexity horizon ($k \approx 10^{15}$). Beyond this horizon, non-trivial cycles are analytically excluded due to the incompatibility between phase precision and arithmetic distance. For the sub-horizon domain, we provide an exhaustive computational audit of the 29 critical resonant nodes. This framework transitions the Collatz problem from a heuristic sea...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.19595481
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_19595481

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Fogliato Matteo, \"Structural Proof of the Collatz Conjecture: Cycle Exclusion and Global Stability\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.19595481 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_19595481
