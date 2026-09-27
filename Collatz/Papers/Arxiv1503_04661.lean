import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Michael A. Idowu, "Canonical Valuation-Block Stratification, Periodic Seed Geometry and Affine Stability in the Collatz Problem", arXiv:1503.04661 [2015].

Title: Canonical Valuation-Block Stratification, Periodic Seed Geometry and Affine Stability in the Collatz Problem

Abstract (from OpenAlex metadata, truncated):
Set out here are some fundamental theories that may be regarded as newly discovered metamathematics of the odd integers in relation to the Collatz conjecture (also called the 3x+1 problem). Originally motivated by the requirement to invent a new optimised integer factorisation method, this foundational paper primarily focuses on the foundation, formalisation and presentation of a new theoretical framework (schema or blueprint) of a Collatz based number system. The proposed framework is based on metamathematical theories meticulously derived through iterative analyses and reverse engineering (i.e., by hand and mathematical computations) of many large subsets of integers. A collation of the fundamental results from these analytical attempts has led to the establishment of a completely deterministic model of a generalised Collatz based number system that is fundamentally and strangely assoc

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/1503.04661
-/

namespace Collatz.Papers.Arxiv1503_04661

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Michael A. Idowu, \"Canonical Valuation-Block Stratification, Periodic Seed Geometry and Affine Stability in the Collatz Problem\", arXiv:1503.04661 [2015]."

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

end Collatz.Papers.Arxiv1503_04661
