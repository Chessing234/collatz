# doi-10-5281-zenodo-20619752-1-a-binary-proof-of-the-collatz-conjectu

Citation: 王, 江祁, "科拉茨猜想的二进制证明:连续1消耗机制与结构性收缩(新版) A Binary Proof of the Collatz Conjecture: Trailing-Ones Consumption Mechanism and Structural Contraction", DOI:10.5281/zenodo.20619752 [2026].

Authors: 王, 江祁

DOI: [10.5281/zenodo.20619752](https://doi.org/10.5281/zenodo.20619752)

Year: 2026

Venue: (unknown)

Classification: verification

Abstract:

本文通过二进制分析给出了科拉茨猜想的严格证明。核心洞察在于将奇数操作重写为 (3N+1)/2 = N + ⌊N/2⌋ + 1,由此揭示了一个严格的尾部连续1消耗机制:每次奇数操作确定性地消耗二进制末尾恰好一个连续1。这保证了每个数在有限步内必然跳出“顽固”的4k+3阶段。 证明进一步通过目标结构反推,确立了所有连续1生成器服从统一的代数形式(定理5.1)。随后证明了一个根本性的生成-消耗不对称性:生成L个连续1需要数值规模达到约2^L量级,而由此产生的膨胀至多达到约1.5^L——对于L≥5,这是一道不可逾越的鸿沟(定理5.2)。此外,三相窗口锁定定理(定理5.3)证明,消耗窗口(4k+3阶段)、生成窗口(4k+1阶段)和膨胀需求窗口因二进制相位互斥而在结构上无法兼容。 证明由独立的涨跌比分析加以完善,表明序列1:1的结构性上限远低于1.71:1的盈亏平衡阈值(第6节)。三个附录分别提供了所有可能的尾部结构与补充情形的穷举、非尾部连续1为何无法维持膨胀的详细分析,以及完整论证的精炼总结。 全部论证仅依赖二进制加法和进位传播的确定性性质,无需任何概率假设、统计论证或数值验证。 本版本新增附录D(16k+5雪崩定理)和附录E(0的产生与致命对齐),从0的累积与致命对齐角度提供独立于正文的收敛验证路径,进一步加固证明的完备性。 --- This paper presents a rigorous proof of the Collatz conjecture through binary analysis. The key insight is rewriting the odd-step operation as (3N+1)/2 = N + ⌊N/2⌋ + 1, which reveals a strict trailing-ones consumption...

Lean file: `Collatz/Papers/Journal_10_5281_zenodo_20619752.lean`.

Formalization status: statement recorded as `mainStatement`; only weak bridge lemmas are checked. The paper's main theorem is not proved in Lean.

Batch: journal100-j (2026-09-15)
