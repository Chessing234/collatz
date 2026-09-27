import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Nobuki Fujimoto, "Alphabet Reduction and Path-Dependent F-Entropy for the Collatz Conjecture: A Finite-Behind-Infinite Approach", 2026.

Title: Alphabet Reduction and Path-Dependent F-Entropy for the Collatz Conjecture: A Finite-Behind-Infinite Approach

Abstract (from harvested metadata, truncated):
Four novel contributions to the Collatz conjecture, unified under Fujimoto's Finite-Behind-Infinite (FBI) Hypothesis. (1) Alphabet Reduction Theorem (Lean4 zero sorry): the theoretical 16-symbol Syracuse block alphabet collapses to EXACTLY 6 realizable symbols via algebraic case analysis on n mod 4, proving (t1=1) XOR (v=1). Ten combinations are structurally impossible. (2) Path-Dependent F-Entropy (first Perelman-style analog for Collatz): F(orbit_k) := log2(n_k) - U_k where U_k counts v=1 blocks, strictly decreases by at least log2(3)-2 ~= -0.415 per Syracuse step. Formalized as integer inequalities: n=3 mod 4 gives 2*syracuse(n) = 3n+1, n=1 mod 4 gives 4*syracuse(n) <= 3n+1. (3) Emptiness...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.19504641
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_19504641

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Nobuki Fujimoto, \"Alphabet Reduction and Path-Dependent F-Entropy for the Collatz Conjecture: A Finite-Behind-Infinite Approach\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.19504641 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_19504641
