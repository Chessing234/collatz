import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Robert Polak, "Analysis of the Collatz Conjecture: Excluding Infinite Growth.", 2026.

Title: Analysis of the Collatz Conjecture: Excluding Infinite Growth.

Abstract (from harvested metadata, truncated):
Part 2 of a two‑paper program toward an analytical proof of the Collatz conjecture. Using the modulo‑3 “One‑Way Gate”, the 3‑adic contraction of T(n)=(3n+1)/2^{v2(3n+1)}, and an exact Diophantine reduction with a telescoping identity, we exclude infinite growth of Collatz trajectories. Every trajectory must enter the target set S={n | 3n+1=2^k} and thus reach 1. The integer fixed‑point condition is D|S(σ) with n=S(σ)/D, where D=2^b−3^a and S(σ)=2^b C(σ). Orders with any p_i≥3 are excluded by inequalities; for mixtures p∈{1,2} a gcd argument forces the trivial class p_i=2, yielding n=1. Modular invariants (Bang–Zsigmondy) and a finite congruence check close remaining borderline cases. This pa...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.21760570
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_21760570

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Robert Polak, \"Analysis of the Collatz Conjecture: Excluding Infinite Growth.\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.21760570 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_21760570
