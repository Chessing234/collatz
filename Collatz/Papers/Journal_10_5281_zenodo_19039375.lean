import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Michael Ross, "Spike Structures and 2-adic Transition Laws in the Accelerated Collatz Map", 2026.

Title: Spike Structures and 2-adic Transition Laws in the Accelerated Collatz Map

Abstract (from harvested metadata, truncated):
We study an accelerated Collatz map through a 2-adic structural framework. The odd positive integers partition into three families B = {8n+1}, D = {4n+3}, C = {8n+5} whose division exponents under the map are respectively constant at 2, constant at 1, and always ≥ 3. Within C, a decomposition modulo 24 into subfamilies C_1, C_2, G with associated linear forms L_2, L_8, L_5 exhibits a cyclic 2-adic lifting: deep powers of 2 rotate systematically among the three forms. We call this phenomenon spike structures, and we develop the half-rotation, rotation, and tower lemmas that govern it. We then prove the complete one-step transition law for the exponent: for any odd x with a(x) = a, the class o...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.19039375
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_19039375

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Michael Ross, \"Spike Structures and 2-adic Transition Laws in the Accelerated Collatz Map\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.19039375 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_19039375
