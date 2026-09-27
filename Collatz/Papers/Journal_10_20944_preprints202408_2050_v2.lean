import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Gaurav Goyal, "Generalized Dynamics and Generation Mapping for Collatz-type Sequences", 2024.

Title: Generalized Dynamics and Generation Mapping for Collatz-type Sequences

Abstract (from harvested metadata, truncated):
Let an odd integer $\mathcal{X}$ be represented as $\sum \limits_{M &amp;gt; m} 2^M + 2^m - 1$ for $m \geq 1$, where $2^m - 1$ is called the Governor. The general dynamics is such that applying the Collatz-type function iteratively lead to $\sum \limits_{N &amp;gt; 1} 2^N + 2^{\mathcal{T}} - 1$, where $2^{\mathcal{T}} - 1$ is referred to as the Trivial Governor. For the $3\mathcal{Z} + 1$ sequence, the Trivial Governor is $2^1 - 1$, while for the $5\mathcal{Z} + 1$ sequence, the Trivial Governors are $2^2 - 1$ and $2^1 - 1$. It is demonstrated that for $\mathcal{X}$ to reappear in a Collatz-type sequence, its Governor must be the Trivial Governor. Specifically, in the $3\mathcal{Z} + 1$ sequ...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.20944/preprints202408.2050.v2
-/

namespace Collatz.Papers.Journal_10_20944_preprints202408_2050_v2

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Gaurav Goyal, \"Generalized Dynamics and Generation Mapping for Collatz-type Sequences\", DOI:10.20944/preprints202408.2050.v2 [2024]."

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

end Collatz.Papers.Journal_10_20944_preprints202408_2050_v2
