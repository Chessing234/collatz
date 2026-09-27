import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for LongFei Hong, "The Collatz Conjecture: A Complete Proof via Adelic Analysis", 2026.

Title: The Collatz Conjecture: A Complete Proof via Adelic Analysis

Abstract (from harvested metadata, truncated):
Title: The Collatz Conjecture: A Complete Proof via Adelic Analysis Author: Longfei Hong (Independent Researcher, honglongfei@qq.com) Abstract We present a complete proof of the Collatz conjecture (the 3n+1 problem), which states that for any positive integer \lambda_0, iterating the map T(n) = n/2 if n even and T(n) = 3n+1 if n odd eventually reaches 1. Our approach introduces the Adelic Telescoping Theorem, which unifies real and 2-adic topologies to analyze orbit behavior through the identity: \lambda_0 \cdot 3^{A_n} + C_n = 2^{S_n} \cdot \lambda_n The proof proceeds through four main theorems: Engine Closure Theorem: The w=1 engine (shallow-step dynamics) admits no infinite positive inte...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.21710583
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_21710583

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "LongFei Hong, \"The Collatz Conjecture: A Complete Proof via Adelic Analysis\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.21710583 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_21710583
