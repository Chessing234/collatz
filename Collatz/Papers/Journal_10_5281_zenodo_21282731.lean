import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for 李建, "An Elementary Proof of the Collatz Conjecture via Emission-Braking Counting", 2026.

Title: An Elementary Proof of the Collatz Conjecture via Emission-Braking Counting

Abstract (from harvested metadata, truncated):
本文提出了Collatz猜想的基本证明。我们将奇数迭代过程抽象为原子运算 X → (3X+1)/2^k,并引入“发射”和“制动”的计数框架。利用模4分类,我们推导出两种奇数类型之间的盈亏差异。我们证明,对于任意给定起始值,连续的3型段具有有限长度上界,从而获得1型数剩余步长的线性下界,进而产生指数数值压缩。结合排除非平凡循环和无界轨迹的矛盾论证,我们最终证明所有正整数在Collatz迭代下必然收敛于1。

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.21282731
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_21282731

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "李建, \"An Elementary Proof of the Collatz Conjecture via Emission-Braking Counting\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.21282731 [2026]."

/-- Recorded main claim shell (structural); the paper's theorem is not proved here.
This placeholder is the standard Collatz conjecture proposition. -/
def mainStatement : Prop := Collatz.CollatzConjecture

/-- Checked bridge facts only. -/
theorem step_one_eq : Collatz.step 1 = 4 := Collatz.step_one

theorem step_two_eq : Collatz.step 2 = 1 := Collatz.step_two

/-- Checked: every power of two reaches `1` (Mathlib-copied parity/division facts). -/
theorem powers_of_two_reach_one (k : Nat) :
    ∃ t : Nat, Collatz.orbit t (2 ^ k) = 1 :=
  Collatz.Papers.MathlibCopied.orbit_pow_two_reaches_one k

end Collatz.Papers.Journal_10_5281_zenodo_21282731
