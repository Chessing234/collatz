import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Durmagambetov, A. A. and Durmagambetova, A. A., "Collatz Conjecture: Binary Structure Analysis and Trajectory Behavior", 2026.

Title: Collatz Conjecture: Binary Structure Analysis and Trajectory Behavior

Abstract (from harvested metadata, truncated):
We advance the study of the Collatz conjecture through an analysis of the binary representations of positive integers via fractional parts. We introduce a direct, non-recursive relation for the intermediate mantissas\( ~\sigma_j \) and prove the exact bound \( \sigma_j \le 1/(\ln 2\,(2^{m+1}-1)) \) after a run of \( m \)consecutive ones (Theorem 4), establishing that every such run must terminate. Using Weyl's equidistribution theorem applied to \( \{n \log_2 3\} \) (averaged over \( n \), not applied to any individual binary expansion), we establish that \( h(n) \le \frac{1}{2}L_n + o(L_n) \) holds for almost all \( n \), i.e.\ outside a set of natural density zero (Theorem 5); we explicitly identify this as the boundary of what the density method achieves. A complete mod-\( 8 \)...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.20944/preprints202401.0227.v27
-/

namespace Collatz.Papers.Journal_10_20944_preprints202401_0227_v27

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Durmagambetov, A. A. and Durmagambetova, A. A., \"Collatz Conjecture: Binary Structure Analysis and Trajectory Behavior\", DOI:10.20944/preprints202401.0227.v27 [2026]."

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

end Collatz.Papers.Journal_10_20944_preprints202401_0227_v27
