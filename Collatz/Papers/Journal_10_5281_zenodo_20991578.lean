import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Sun, Hechun, "利用二进制末尾连续1个数的严格有限递减证明考拉兹猜想 Proving the Collatz Conjecture via the Strict Finite Reduction of Consecutive Trailing 1s in Binary Representation", 2026.

Title: 利用二进制末尾连续1个数的严格有限递减证明考拉兹猜想 Proving the Collatz Conjecture via the Strict Finite Reduction of Consecutive Trailing 1s in Binary Representation

Abstract (from harvested metadata, truncated):
考拉兹猜想作为数论中的著名难题,其难点在于奇数在经历 3x+1 操作后数值往往产生膨胀,破坏了传统势能函数的单调递减性。本文修正了该逻辑盲点,引入了一个不受数值大小影响的全局递减指标:数字二进制表达中末尾连续 1 的个数。通过严格的代数推导,证明了在任何反例链条中,每经历一次 (3x+1)/2 的运算,新的奇数末尾连续 1 的个数必将严格减少。当该递减序列降为 1(即数字满足 1 (模 4))时,必然触发强代数不等式 0.75 * n + 0.25 < n,序列发生绝对跌落。结合自然数集的良序原则,证明不存在能够永久规避跌落的反例链条。本证明完全基于初等数论,逻辑严密。 The Collatz conjecture is a famous difficult problem in number theory, primarily because odd numbers often expand in value after the 3x+1 operation, disrupting the monotonic decrease of traditional potential functions. This paper corrects this logical blind spot by introducing a globally decreasing metric independent of numerical magnitude: the number of consecutive trailing 1s in the binary representation of a number. Through rigorous algebraic derivations, it is proven that in any counterexample chain,...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.20991578
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_20991578

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Sun, Hechun, \"利用二进制末尾连续1个数的严格有限递减证明考拉兹猜想 Proving the Collatz Conjecture via the Strict Finite Reduction of Consecutive Trailing 1s in Binary Representation\", DOI:10.5281/zenodo.20991578 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_20991578
