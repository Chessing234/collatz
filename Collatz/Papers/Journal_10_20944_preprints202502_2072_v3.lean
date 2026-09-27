import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Amarachukwu Nwankpa, "A Proof of the Collatz Conjecture via Boundedness and Cycle Uniqueness", 2025.

Title: A Proof of the Collatz Conjecture via Boundedness and Cycle Uniqueness

Abstract (from harvested metadata, truncated):
We prove the Collatz Conjecture by demonstrating that all Collatz sequences are bounded and converge to the 4→2→1 cycle. Our proof employs a two-step approach: first, we establish boundedness through novel \textbf{asymptotic analysis} and refined congruence restrictions modulo 4 and modulo 12, revealing deterministic residue class transitions that preclude unbounded growth. Second, cycle uniqueness is rigorously demonstrated through two independent number-theoretic proofs: one utilizing a novel product equation and prime factorization analysis, and the other employing a minimality argument. These complementary approaches provide a definitive characterization of Collatz cycles.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.20944/preprints202502.2072.v3
-/

namespace Collatz.Papers.Journal_10_20944_preprints202502_2072_v3

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Amarachukwu Nwankpa, \"A Proof of the Collatz Conjecture via Boundedness and Cycle Uniqueness\", Preprints.org, DOI:10.20944/preprints202502.2072.v3 [2025]."

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

end Collatz.Papers.Journal_10_20944_preprints202502_2072_v3
