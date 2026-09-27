import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for 陈, 文正, "科拉茨猜想的路径结构证明框架A Path-Structural Proof Framework for the Collatz Conjecture", 2026.

Title: 科拉茨猜想的路径结构证明框架A Path-Structural Proof Framework for the Collatz Conjecture

Abstract (from harvested metadata, truncated):
【中文摘要】 本文基于陈文正(2026)提出的「自然数路径大一统理论」(N = 90M + R),构建了科拉茨猜想的完整路径结构证明框架。核心思路是将全体自然数分解为90条等差路径,在路径跳转图上建立三个核心引理:(1)无纯膨胀闭环定理:45条奇数路径的膨胀子图中不存在有向闭环,最长纯膨胀链≤8步;(2)累积收缩定理:所有22条膨胀路径在至多8步内累积收缩系数降至1以下;(3)M坐标严格递减定理:当 N > N₀ 时,收缩步骤使 N 严格减小。三条引理联立,证明了任意奇数 N > N₀ 经有限步必然进入已验证范围(≤ 2⁶⁸),从而建立科拉茨猜想的完整证明框架。整体几何平均收缩率精确计算为 0.7272,与Gemini独立发现的 0.75 系数高度吻合。此结论强于陶哲轩(2019)的「几乎所有数收缩」结论,在结构上实现了从「概率性」到「确定性」的跨越。[Abstract] Based on the Unified Path Theory of Natural Numbers (N = 90M+R) proposed by Chen Wenzheng (2026), this paper constructs a complete path-structural proof framework for the Collatz Conjecture. The core approach decomposes all natural numbers into 90 arithmetic progression paths, and establishes three key lemm...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.21262926
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_21262926

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "陈, 文正, \"科拉茨猜想的路径结构证明框架A Path-Structural Proof Framework for the Collatz Conjecture\", Zenodo, DOI:10.5281/zenodo.21262926 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_21262926
