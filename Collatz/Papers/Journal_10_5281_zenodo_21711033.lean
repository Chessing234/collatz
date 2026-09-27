import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for yan huang, "Global Convergence of the Collatz Map: 2-adic Valuation and Fractional Compression", 2026.

Title: Global Convergence of the Collatz Map: 2-adic Valuation and Fractional Compression

Abstract (from harvested metadata, truncated):
我们通过将 $(3X+1)/2$ 分类为具有确定性转换的四种模 8 类型来证明 Collatz 猜想。 唯一扩展循环具有复合函数 $F(X)=(27X+19)/16$ 和不动点 $-19/11 \notin \mathbb{N}^+$,仅允许通过位长度界限进行有限次重复。 弱压缩段的串联受到一致性条件的限制,这些条件通过偶数 $\equiv$ 奇数矛盾迫使断裂。 B 型段由独立的复合约束处理。 宏观单位分析表明,每个复合块的净乘数 $<1$,产生 $\sum K/N > 0。585$ 和 $\bar{k} > \log_2 3$。 因此,所有轨迹都是有界的,不存在非平凡循环,并且收敛到 $(1,4,2)$。

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.21711033
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_21711033

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "yan huang, \"Global Convergence of the Collatz Map: 2-adic Valuation and Fractional Compression\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.21711033 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_21711033
