import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Eduard Dyachenko, "Topology of Vanishing Sums in the Collatz Problem:\\ 2-adic Reduction, 3-adic Scales, and Dynamic Incompatibility", 2026.

Title: Topology of Vanishing Sums in the Collatz Problem:\\ 2-adic Reduction, 3-adic Scales, and Dynamic Incompatibility

Abstract (from harvested metadata, truncated):
A deterministic framework is developed for excluding the existence of non-trivialcycles in the Collatz map $3n+1$ on $\mathbb{N}$. The trajectory is interpreted not asa pseudo-random process, but as an evolution through a hierarchy of $3$-adic scalelevels: each odd step necessarily increases the $3$-adic denominator depth, forcing thesystem into a finer representational layer. This mechanism is combined with the local$2$-adic structure, which uniquely determines the sequence of divisions by $2$, and withthe global Diophantine constraint given by the cycle equation. A dynamic top-levelcontribution arising at each odd step is identified. Under normalization to depth $3^K$,the final transition produces a non-removable residue $2^{A_{K-1}} \bmod 3$, whereas allpreceding contributions are...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.18466601
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_18466601

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Eduard Dyachenko, \"Topology of Vanishing Sums in the Collatz Problem:\\\\ 2-adic Reduction, 3-adic Scales, and Dynamic Incompatibility\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.18466601 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_18466601
