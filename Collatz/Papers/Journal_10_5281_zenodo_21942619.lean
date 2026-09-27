import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Andrew Stewart Caldin, "The Collatz Conjecture: A Simple Arithmetic Rule with No Closed Form — E8 Intelligence Research", 2026.

Title: The Collatz Conjecture: A Simple Arithmetic Rule with No Closed Form — E8 Intelligence Research

Abstract (from harvested metadata, truncated):
FINDING: Collatz Conjecture is the simplest unsolved problem; no equations, only iterative rule. | MATH: f(n) = n/2 if n even, 3n+1 if n odd; no closed form, no proven cycle length. | CONNECTION: None to geometric ratios or symmetries; purely arithmetic. | DEPTH: 2 (low mathematical structure, no constants or geometry). FINDING: Riemann Hypothesis is the oldest unsolved problem; zeros of zeta function on critical line. | MATH: ζ(s) = Σ n^{-s} for Re(s)>1; analytic continuation; non-trivial zeros at s=1/2+it. | CONNECTION: 0.5 critical line relates to 1/2 ratio, but not 0.382/0.618/1.618; no crystallographic link. | DEPTH: 7 (profound for prime distribution, but no direct geometric harmony)....

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.21942619
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_21942619

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Andrew Stewart Caldin, \"The Collatz Conjecture: A Simple Arithmetic Rule with No Closed Form — E8 Intelligence Research\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.21942619 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_21942619
