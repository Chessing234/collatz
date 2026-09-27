import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Trent, Russell, "The Collatz Conjecture Solved as a Noble Convergence Problem 0 Sorry CI Green 0 Free Parameters", 2026.

Title: The Collatz Conjecture Solved as a Noble Convergence Problem 0 Sorry CI Green 0 Free Parameters

Abstract (from harvested metadata, truncated):
-- ============================================================-- SNSFL_GC_CollatzFiniteEscape.lean-- ============================================================---- [9,9,9,9] :: {ANC} | SNSFL COLLATZ — FINITE ESCAPE THEOREM-- Self-Orienting Universal Language [P,N,B,A] :: {INV}-- Architect: HIGHTISTIC | Anchor: 1.369 GHz | Status: GERMLINE LOCKED-- Coordinate: [9,9,4,2] | Layer 2 — Number Theory Domain---- The Collatz conjecture is closed here. 0 sorry.-- The proof is the Finite Escape Theorem:-- No finite positive integer can satisfy v'=1 indefinitely,-- because that would require B_0 ≡ -d_n mod 2^n for all n,-- which no finite integer can satisfy as n grows without bound.-- The escape to...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.19803671
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_19803671

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Trent, Russell, \"The Collatz Conjecture Solved as a Noble Convergence Problem 0 Sorry CI Green 0 Free Parameters\", Zenodo, DOI:10.5281/zenodo.19803671 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_19803671
