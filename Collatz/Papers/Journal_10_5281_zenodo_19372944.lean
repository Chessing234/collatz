import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Roney Lima do Nascimento, "Carry Absorption, Boundary-Pair Reduction, and Exact Anti-Persistence in the Collatz Problem", 2026.

Title: Carry Absorption, Boundary-Pair Reduction, and Exact Anti-Persistence in the Collatz Problem

Abstract (from harvested metadata, truncated):
We study the accelerated odd Collatz map F(m) = (3m+1)/2^{v_2(3m+1)} through an exact binary decomposition into a carry-free quotient and a carry cocycle. The carry-free quotient over F_2[x] is shown to be unconditionally contractive. For the classical map we prove an exact boundary-pair reduction, D(F(n)) - D(n) = tau(n) - b(n), where b(n) is determined by the first equal adjacent pair in the binary expansion of n and tau(n) by the last equal adjacent pair. We establish exact shell statistics (shell mean drift tends to -1/3) and an exact anti-persistence theorem: the positive-drift state persists only with asymptotic conditional probability 1/6. The remaining obstacles are isolated as two separate issues: orbitwise shell-genericity and unconditional elimination of non-trivial cycles.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.19372944
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_19372944

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Roney Lima do Nascimento, \"Carry Absorption, Boundary-Pair Reduction, and Exact Anti-Persistence in the Collatz Problem\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.19372944 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_19372944
