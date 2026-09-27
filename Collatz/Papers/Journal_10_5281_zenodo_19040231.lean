import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for M. Wurm, "Counting backwards from infinity: contraction geometry of Collatz-type maps", 2026.

Title: Counting backwards from infinity: contraction geometry of Collatz-type maps

Abstract (from harvested metadata, truncated):
We study iterated non-injective maps on residue classes modulo~$2^M$. Two map-intrinsic quantities capture the relevant structure: the contraction defect $D_M = |S_M|/|f(S_M)|$ and the drift~$\gamma_M$ (average multiplicative growth per step, defined via the $v_2$-sum). Our results are: Drift closed form$\gamma_\infty(f) = q/4$ for every single-step map$f(n) = \mathrm{odd}(qn+c)$ with $q, c$ odd (independentof~$c$). Exact finite-$M$ behaviour for $q=3$, single-step.$V_M = \sum_{x\in S_M} v_2(3x+1)$ satisfies $V_M = 2^M$ for odd $M$ and $V_M = 2^M - 1$ for even~$M$, so $\gamma_M = 3/4$ exactly for every odd~$M$.The contraction defect obeys $D_M = 4/3$ exactly for every odd~$M$, and $D_M = 12\...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.19040231
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_19040231

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "M. Wurm, \"Counting backwards from infinity: contraction geometry of Collatz-type maps\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.19040231 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_19040231
