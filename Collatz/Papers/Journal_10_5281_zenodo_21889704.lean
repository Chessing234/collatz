import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Elias De Jesus, "The Least-Realizer Minimum for Confined Words: An Erratum to the Terras–Everett Residue Class in A Global Occupation Conjecture for the Accelerated 3x + 1 Map, and the Record-Chronology Reformulation of the Single-Window Realizer Floor", 2026.

Title: The Least-Realizer Minimum for Confined Words: An Erratum to the Terras–Everett Residue Class in A Global Occupation Conjecture for the Accelerated 3x + 1 Map, and the Record-Chronology Reformulation of the Single-Window Realizer Floor

Abstract (from harvested metadata, truncated):
This technical note studies the least positive realizers of confined valuation words in the accelerated odd Collatz map and provides a partial erratum to A Global Occupation Conjecture for the Accelerated 3x+1 Map. Re-deriving the Terras–Everett realizer construction shows that exact realization requires one additional parity bit: the exact realizers of a length-N valuation word with total valuation S_N form a single residue class modulo 2^{S_N+1}, rather than modulo 2^{S_N} alone. Using the corrected construction, the note introduces the minimum realizerr_{\min}(N,c)=\min_{D\in\mathcal C_N(c)} r(D)for c-confined words and proves two exact structural results: r_{\min}(N,c) is nondecreasing i...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.21889704
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_21889704

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Elias De Jesus, \"The Least-Realizer Minimum for Confined Words: An Erratum to the Terras–Everett Residue Class in A Global Occupation Conjecture for the Accelerated 3x + 1 Map, and the Record-Chronology Reformulation of the Single-Window Realizer Floor\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.21889704 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_21889704
