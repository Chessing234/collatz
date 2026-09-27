import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for zhongming xiong, "A Reduction Framework for the Collatz Conjecture: Dual-Phase Structure, Criticality, and Quantitative Targets for Per-Orbit Mixing", 2026.

Title: A Reduction Framework for the Collatz Conjecture: Dual-Phase Structure, Criticality, and Quantitative Targets for Per-Orbit Mixing

Abstract (from harvested metadata, truncated):
# Collatz 猜想的简化框架:双相结构、临界性及每轨道混合的定量目标 **日期:** 2026-07-14 **作者:**熊中明 **隶属:** 中国武汉工业大学 --- **本版本的主要特点:**- 完全自成一体:无交叉引用未发表作品或伴随论文——附录D中的所有谱系结果均为证据证明——仅有相关工作发表的参考:Zenodo完整记录(DOI:10.5281/zenodo.21350247) --- --- ## 论文摘要 ### 无条件结构性结果 1. **临界性修正**(命题3.1):预期的一步收缩因子是$\mathbb{E}[\rho] = 1$(临界),而非$e^{\mathbb{E}[\lambda]} = 9/16$,解决了詹森不等式的混淆。 2. **双相结构**(引理5.1):对于$n_0 = 2^E + 1$,$E \ge 3$(即$n_0 \等值1 \pmod{4}$),第一阶段允许闭式 $n_k = 3^k \cdot 2^{E-2k} + 1$,其中$s_k = v_k = 1$,对应$0 \le k \le \lfloor(E-3)/2\rfloor$,得到 $r_{\mathrm{eff}} = 2$。**第一阶段仅对$n_0 \等值1 \pmod{4}$;扩展到一般 $n_0$ 是 Gap D.** 3. **经验性$\alpha$-混合**(定义6.1):通过单符号块频率度量对确定性序列的严格定义,使McLeish SLLN在没有概率空间或平稳性的情况下实现。 ### 无条件概率结果(附录D) 4. **光谱半径界限**(提案D.1):$\|M...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.21331127
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_21331127

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "zhongming xiong, \"A Reduction Framework for the Collatz Conjecture: Dual-Phase Structure, Criticality, and Quantitative Targets for Per-Orbit Mixing\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.21331127 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_21331127
