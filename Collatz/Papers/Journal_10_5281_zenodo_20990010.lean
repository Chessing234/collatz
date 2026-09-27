import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Sun, Hechun, "基于 2-adic 测度与局部单调性的考拉兹猜想收敛性证明 Proof of Convergence for the Collatz Conjecture Based on 2-adic Measure and Local Monotonicity", 2026.

Title: 基于 2-adic 测度与局部单调性的考拉兹猜想收敛性证明 Proof of Convergence for the Collatz Conjecture Based on 2-adic Measure and Local Monotonicity

Abstract (from harvested metadata, truncated):
考拉兹猜想是数论中著名的悬而未决的问题。本文沿袭并修正了基于算法信息论与势能函数的证明思路,通过引入 2-adic 测度,构建了全新的局部单调递减势能函数。利用良序原则与反证法,我们证明在考拉兹映射下,任何非平凡循环或发散序列都会导致势能函数的矛盾,从而推出所有正整数最终都将收敛于标准循环 4, 2, 1。 The Collatz conjecture is a famous unsolved problem in number theory. This paper follows and corrects the proof approach based on algorithmic information theory and potential functions. By introducing the 2-adic measure, a new locally monotonically decreasing potential function is constructed. Using the well-ordering principle and proof by contradiction, we show that under the Collatz map, any non-trivial cycle or divergent sequence leads to a contradiction in the potential function, thereby proving that all positive integers eventually co...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.20990010
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_20990010

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Sun, Hechun, \"基于 2-adic 测度与局部单调性的考拉兹猜想收敛性证明 Proof of Convergence for the Collatz Conjecture Based on 2-adic Measure and Local Monotonicity\", Zenodo, DOI:10.5281/zenodo.20990010 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_20990010
