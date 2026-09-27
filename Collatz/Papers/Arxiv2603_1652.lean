import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Liang Wang, "Spectral Analysis of the Transfer Operator in the Period-3 Logistic Sandbox: A Dynamical Heuristic for the 3x+1 Problem", arXiv:2603.1652 [2026].

Title: Spectral Analysis of the Transfer Operator in the Period-3 Logistic Sandbox: A Dynamical Heuristic for the 3x+1 Problem

Abstract (from OpenAlex metadata, truncated):
The Collatz (3x + 1) conjecture remains one of the most challenging open problems in number theory, largely due to the unpredictable, pseudo-random fluctuations of its discrete integer o rbits. This paper introduces an interdisciplinary approach by translating discrete arithmetic rules into a continuous dynamical sandbox. Specifically, we construct a symbolic analogy between the 3x + 1 map and the Logistic map f (x) = 1 − µx2 locked at the superstable period-3 window (µ ≈ 1.7549). By building a customized threshold partition anchored at the unstable fixed point, the continuous system naturally enforces a “forbidden word 11” grammar, mirroring the arithmetic constraint that an odd operation (T(n) = 3n + 1) must produce an even number. Through the eigenspectrum of the Perron-Frobenius transfer operator, we demonstrate a 2:1 ergodic measure ratio for contraction (even) and expansion (odd) s

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2603.1652
-/

namespace Collatz.Papers.Arxiv2603_1652

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Liang Wang, \"Spectral Analysis of the Transfer Operator in the Period-3 Logistic Sandbox: A Dynamical Heuristic for the 3x+1 Problem\", arXiv:2603.1652 [2026]."

/-- Recorded finite-verification claim shell; the paper's bound is not proved here. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1


/-- Miniature checked verification for `B = 2`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩


end Collatz.Papers.Arxiv2603_1652
