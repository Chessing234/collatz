# doi-10-5281-zenodo-21770642-8-a-discrete-dissipative-framework-for-t

Citation: yang, taonuo, "考拉兹猜想的离散耗散模型: 模8状态机、位宽剪刀差与四阶段演化框架 (A Discrete Dissipative Framework for the Collatz Conjecture: Mod-8 State Machine, Bit-Width Scissors Gap, and a Four-Stage Evolution Model)", DOI:10.5281/zenodo.21770642 [2026].

Authors: yang, taonuo

DOI: [10.5281/zenodo.21770642](https://doi.org/10.5281/zenodo.21770642)

Year: 2026

Venue: (unknown)

Classification: structural

Abstract:

摘要:本文系统整合三阶段推导,构建了一个分析考拉兹(3x+1)猜想的新框架。核心由五层结构组成:(1) 精确展开层——导出奇核变换的 n 步迭代封闭式 x_n = (3^n x_0 + C_n)/2^{S_n},将系统分解为"主干项 3^n x_0"(膨胀势能)与"尾巴项 C_n"(+1诱导的累积扰动);(2) 动态比率层——构造 R_n = 2^{S_n}/C_n 及其一维递推 R_n = 2^{k_n} R_{n-1}/(3 + R_{n-1}),把猜想等价转化为"R_n 是否永不趋于零"的纯序列问题;(3) 模8状态机层——证明剥皮次数 k_n 由奇核的模8余数完全决定(余1 \to k=2,余3/7 \to k=1,余5 \to k\geq3),并建立"三阶梯强制转轨"结构,任何连续暴涨链在有限步内必然转入暴跌区;(4) 位宽剪刀差层——引入信息位宽势能 P(m) = \log_2 m,推导单步熵变 \Delta P = \log_2 3 - k(m),在均匀余数测度下得到期望漂移 \mathbb{E}[\Delta P] = -0.415 位/步(与经典对数增长常数一致),并证明边界抵消不等式 (8/3)(2/3)^L < 1 在 L\geq3 时成立——暴涨块(长度 L 的 k=1 链)被单次暴跌或两次震荡完全抵消;(5) 逻辑剪裁机层——从有限位宽判定视角,说明"是否有界"与"是否停机"可由有限比特的模8判定递归实现,揭示逃逸者若存在必为2-进数意义下的"无限位宽奇异点" -1 \in \mathbb{Z}_2 \setminus \mathbb{N}^+。在此基础上提出四阶段离散耗散模型(上涨 \to 震荡 \to 暴跌 \to 稳定),并给出统一演化方程。最后明确列出三个尚未填补的严格性缺口,以诚实标注框架的边界。...

Lean file: `Collatz/Papers/Journal_10_5281_zenodo_21770642.lean`.

Formalization status: statement recorded as `mainStatement`; only weak bridge lemmas are checked. The paper's main theorem is not proved in Lean.

Batch: journal100-j (2026-09-15)
