import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Bhagavath, Sriram, "A Structural Proof of the Collatz Conjecture via the 1/8 Reduction, Borel-Cantelli, and the Mersenne Snipe", 2026.

Title: A Structural Proof of the Collatz Conjecture via the 1/8 Reduction, Borel-Cantelli, and the Mersenne Snipe

Abstract (from harvested metadata, truncated):
We prove the Collatz conjecture via four interlocking arguments. (1) A residue automaton on odd integers mod 8 reduces the problem to proving convergence of the set S_1/8 = {n odd : 3|n, n ≢ 5 mod 8}, comprising exactly 1/8 of all integers. (2) Borel-Cantelli with geometric decay rate Λ = 0.055 shows P(T=∞) = 0 for S_1/8. (3) The Mersenne snipe proves worst-case all-1s binary trajectories are dominated: surplus grows as t, while chain deficit is only 0.585t. (4) The Cantor diagonal argument confirms that no divergent sequence can be bijected with the naturals. The single cited external result is Tao (2019), Acta Math. Note: This is not a "proof" proof. It's a proof of concept to stress-test....

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.21230308
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_21230308

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Bhagavath, Sriram, \"A Structural Proof of the Collatz Conjecture via the 1/8 Reduction, Borel-Cantelli, and the Mersenne Snipe\", Zenodo, DOI:10.5281/zenodo.21230308 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_21230308
