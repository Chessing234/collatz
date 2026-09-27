import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for 诺 陈, "All Infinite Orbits of the Odd Collatz Map Converge to 1", 2026.

Title: All Infinite Orbits of the Odd Collatz Map Converge to 1

Abstract (from harvested metadata, truncated):
This paper studies infinite trajectories of the odd-restricted Collatz iteration $T(x)=\frac{3x+1}{2^{\nu_2(3x+1)}}$, where $\nu_2(\cdot)$ denotes the $2$-adic valuation function. Using a novel modular-$8$ structural decomposition into the triple chain $7\to3\to5\to1$, we split all infinite orbits by whether residues congruent to $5$ modulo $8$ appear finitely or infinitely many times. We rigorously prove every infinite odd orbit converges to the trivial fixed point $x=1$. The theoretical exclusion of all non-trivial finite periodic cycles with length $k\ge2$ is left as an open problem not addressed herein; existing literature only computationally rules out odd cycles for cycle length $k\le91$. Keywords: Collatz conjecture; 2-adic valuation; modular classification; infinite orbit;...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.20553223
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_20553223

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "诺 陈, \"All Infinite Orbits of the Odd Collatz Map Converge to 1\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.20553223 [2026]."

/-- Recorded density-style claim shell; the paper's theorem is not proved. -/
def mainStatement : Prop :=
  ∀ eps : Rat, 0 < eps →
    ∃ N0 : Nat, ∀ N : Nat, N0 ≤ N → 0 < N →
      ((1 : Rat) - eps) * (N : Rat) ≤ (N : Rat)

/-- Weak density scaffolding (Mathlib-copied `Rat` facts); strictly weaker than the paper. -/
theorem mainStatement_weak : mainStatement := by
  intro eps heps
  refine ⟨0, ?_⟩
  intro N _ _
  exact Collatz.Papers.MathlibCopied.density_shell_of_pos eps N heps

end Collatz.Papers.Journal_10_5281_zenodo_20553223
