import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Yi Ni and Xinyi Yang, "The 3-adic limit of the Krasikov-Lagarias inequalities, and an improved lower bound for the 3x+1 problem", 2026.

Title: The 3-adic limit of the Krasikov-Lagarias inequalities, and an improved lower bound for the 3x+1 problem

Abstract (from harvested metadata, truncated):
Let T(n) = n/2 for n even and (3n+1)/2 for n odd, and for a not congruent to 0(mod 3) let pi_a(x) be the number of integers 1 <= n <= x whose forward orbitunder T reaches a. Krasikov and Lagarias bounded pi_a(x) from below byexhibiting a feasible solution of a linear program L^NT_k(lambda), the exponentobtained being gamma = log_2 lambda; their Theorem 2.2 is uniform in the levelk. Whether the method reaches the exponent 1 - equivalently, whether thecritical values lambda_k tend to 2 - has been open since Applegate and Lagariasposed it in 1995. Our main result reduces that question to a statement about a single operator.The substitution m = 3v + 2 collapses the whole k-indexed family into on...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.22160967
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_22160967

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Yi Ni and Xinyi Yang, \"The 3-adic limit of the Krasikov-Lagarias inequalities, and an improved lower bound for the 3x+1 problem\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.22160967 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_22160967
