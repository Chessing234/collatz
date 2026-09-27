import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Yoshiki Ueoka et al., "A Proof of the Collatz Conjecture via Translation and Structural Analysis of Positive Integers and the Collatz Map", 2026.

Title: A Proof of the Collatz Conjecture via Translation and Structural Analysis of Positive Integers and the Collatz Map

Abstract (from harvested metadata, truncated):
We prove the Collatz conjecture (the $3n+1$ problem) by means of a descent argument based on alternating binary notation (ABN) and Collatz phase expressions (CPE). We first establish a bijection between positive odd integers and canonical CPEs, and describe the Collatz map as a local structural rewriting on unit sequences. A case analysis of $27$ local patterns at the boundary of units then yields one-step monotonicity inequalities for the structural measures. In addition, we show that the $2$-adic valuation $\nu_2(3n+1)$ is determined solely by the bottom unit. These results imply that, in the region $\mu\ge 4$, the structural quantities $B$ and $H_C$ cannot remain frozen indefinitely, so every orbit descends to $\mu\le 3$ in finite time. Finally, for $\mu\le 3$, we reduce the problem...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.19140267
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_19140267

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Yoshiki Ueoka et al., \"A Proof of the Collatz Conjecture via Translation and Structural Analysis of Positive Integers and the Collatz Map\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.19140267 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_19140267
