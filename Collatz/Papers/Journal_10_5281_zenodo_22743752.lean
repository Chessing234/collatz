import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Mingbo Li, "A Sieve Method for Non‑Trivial Cycles of the Collatz Conjecture Based on a Ratio Inequality", 2026.

Title: A Sieve Method for Non‑Trivial Cycles of the Collatz Conjecture Based on a Ratio Inequality

Abstract (from harvested metadata, truncated):
We present a sieve criterion for hypothetical non-trivial cycles of the Collatz iteration, based on the classical ratio inequality of Eliahou (1993) and the computational lower bound a_1 ≥ 2^71 of Barina (2023). For a given number of odd steps S, we prove that any candidate cycle must have total even-division count M = ceil(S log_2 3), subject to a size restriction on S. This yields an explicit arithmetic condition on the fractional part of S log_2 3 that rules out certain values of S. We also prove an improved ratio upper bound via the pigeonhole principle, sharpening the bound on 2^M from (3 + 1/a_1)^S to (3 + 1/(1.16 a_1))^S, which effectively raises the lower bound on a_1 to approximatel...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.22743752
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_22743752

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Mingbo Li, \"A Sieve Method for Non‑Trivial Cycles of the Collatz Conjecture Based on a Ratio Inequality\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.22743752 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_22743752
