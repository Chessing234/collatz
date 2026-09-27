import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for SUTTHIPONG SINDEE et al., "Periodic cycles for an extension of generalized $3x + 1$ functions", 2024.

Title: Periodic cycles for an extension of generalized $3x + 1$ functions

Abstract (from harvested metadata, truncated):
The Collatz conjecture is an open problem involving the $3x + 1$ function. The function belongs to a class of generalized $3x + 1$ functions of relatively prime type. This paper focuses on exploring periodic cycles for an extension of a generalized $3x + 1$ function of relatively prime type. By extending its domain to $\mathbb{R}$, the result shows that every integer periodic point is isolated in the usual topology on $\mathbb{R}$. Moreover, every positive integer periodic cycle for the extension is attracting if the generalized $3x + 1$ function is specified by parameters under some conditions.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.37193/cjm.2024.03.12
-/

namespace Collatz.Papers.Journal_10_37193_cjm_2024_03_12

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "SUTTHIPONG SINDEE et al., \"Periodic cycles for an extension of generalized $3x + 1$ functions\", Carpathian Journal of Mathematics, DOI:10.37193/cjm.2024.03.12 [2024]."

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

end Collatz.Papers.Journal_10_37193_cjm_2024_03_12
