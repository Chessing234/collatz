# doi-10-5281-zenodo-21331127-a-reduction-framework-for-the-collatz-co

Citation: zhongming xiong, "A Reduction Framework for the Collatz Conjecture: Dual-Phase Structure, Criticality, and Quantitative Targets for Per-Orbit Mixing", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.21331127 [2026].

Authors: zhongming xiong

DOI: [10.5281/zenodo.21331127](https://doi.org/10.5281/zenodo.21331127)

Year: 2026

Venue: Zenodo (CERN European Organization for Nuclear Research)

Classification: cycle

Abstract:

# Collatz 猜想的简化框架:双相结构、临界性及每轨道混合的定量目标 **日期:** 2026-07-14 **作者:**熊中明 **隶属:** 中国武汉工业大学 --- **本版本的主要特点:**- 完全自成一体:无交叉引用未发表作品或伴随论文——附录D中的所有谱系结果均为证据证明——仅有相关工作发表的参考:Zenodo完整记录(DOI:10.5281/zenodo.21350247) --- --- ## 论文摘要 ### 无条件结构性结果 1. **临界性修正**(命题3.1):预期的一步收缩因子是$\mathbb{E}[\rho] = 1$(临界),而非$e^{\mathbb{E}[\lambda]} = 9/16$,解决了詹森不等式的混淆。 2. **双相结构**(引理5.1):对于$n_0 = 2^E + 1$,$E \ge 3$(即$n_0 \等值1 \pmod{4}$),第一阶段允许闭式 $n_k = 3^k \cdot 2^{E-2k} + 1$,其中$s_k = v_k = 1$,对应$0 \le k \le \lfloor(E-3)/2\rfloor$,得到 $r_{\mathrm{eff}} = 2$。**第一阶段仅对$n_0 \等值1 \pmod{4}$;扩展到一般 $n_0$ 是 Gap D.** 3. **经验性$\alpha$-混合**(定义6.1):通过单符号块频率度量对确定性序列的严格定义,使McLeish SLLN在没有概率空间或平稳性的情况下实现。 ### 无条件概率结果(附录D) 4. **光谱半径界限**(提案D.1):$\|M...

Lean file: `Collatz/Papers/Journal_10_5281_zenodo_21331127.lean`.

Formalization status: statement recorded as `mainStatement`; only weak bridge lemmas are checked. The paper's main theorem is not proved in Lean.

Batch: journal100-n (2026-09-16)
