import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for McKoy, Caitlin, "The Collatz Conjecture as a Consequence of the 720/360 Degree Regime Incommensurability", 2026.

Title: The Collatz Conjecture as a Consequence of the 720/360 Degree Regime Incommensurability

Abstract (from harvested metadata, truncated):
We prove that every positive integer reaches 1 under the Collatz iteration T(n) = n/2 if n is even, 3n+1 if n is odd. The proof proceeds in three steps, each exact. First, the gap ratio (4n+2)/n between odd and even Collatz steps converges to 4 as n grows and exceeds 4 for all finite n; since 4 exceeds log2(3) = 1.585, the angular displacement of each odd step always exceeds the convergence threshold. Second, the 2-adic valuation v2(3n+1) for odd n follows the geometric distribution P(v2 = k) = 1/2^k, giving expected value E[v2] = 2 by the exact algebraic identity sum k/2^k = 2. Third, the residue arithmetic of 3n+1 modulo 8 is self-correcting: the only dangerous configuration, a run of step...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.19424832
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_19424832

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "McKoy, Caitlin, \"The Collatz Conjecture as a Consequence of the 720/360 Degree Regime Incommensurability\", Zenodo, DOI:10.5281/zenodo.19424832 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_19424832
