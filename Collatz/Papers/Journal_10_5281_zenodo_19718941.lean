import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Liu, ⅩingMing, "An Unconditional Proof of the Collatz Conjecture under the Modulo-6 Framework —— 模6框架下考拉兹猜想的无条件证明", 2026.

Title: An Unconditional Proof of the Collatz Conjecture under the Modulo-6 Framework —— 模6框架下考拉兹猜想的无条件证明

Abstract (from harvested metadata, truncated):
This paper presents an unconditional proof of the Collatz conjecture. The proof is based on the "modulo-6 framework"—every positive integer can be uniquely expressed as N = 2ᵃ·3ᵇ·M, where M = 1, or M = 6n−1 (yin number), or M = 6n+1 (yang number) with n ∈ ℕ ⁺ . This framework automatically strips away the factors 2 and 3 in the Collatz iteration, reducing the conjecture to the convergence of yin and yang numbers. By introducing a classification of the parameter n modulo 2ˢ, we construct a deterministic finite automaton whose state set is = (ℤ /2ˢℤ ) × {−, +}. Furthermore, we prove that all odd numbers generated along any orbit belong to a uniform algebraic form X = K·3ᵃ·m + B, where K ∈ {1,2...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.19718941
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_19718941

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Liu, ⅩingMing, \"An Unconditional Proof of the Collatz Conjecture under the Modulo-6 Framework —— 模6框架下考拉兹猜想的无条件证明\", Zenodo, DOI:10.5281/zenodo.19718941 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_19718941
