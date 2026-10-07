# NEXT.md —— 下一步需求提案（计算系统发生学 · 未形式化的知名定理与算法）

> **生成**：2026-10-07 ｜ **最后更新**：2026-10-07 13:45（老师重排优先级 + 文献已下载）
> **用途**：给老师挑下一批形式化目标。**不是执行计划**（执行计划见 `HANDOVER.md` §4）。
> **原则**：只列**还没有**的；已形式化的见 §0 对照表。
> **评级**：★ 数量 = 学术分量；**难度** = Lean 形式化工作量（不是数学难度）。

---

## ★ 2026-10-07 13:45 优先级重排（老师指示）

### 降级 / 暂缓

| 原编号 | 内容 | 处置 | 理由（老师） |
|---|---|---|---|
| **P1** | Felsenstein 1978 长枝吸引反例 | ⬇️ **降级** | 「构造反例……对 lean4phylo 再开发的收益不大」 |
| **M3** | 异常基因树（anomalous gene trees）反例 | ⬇️ **降级** | 同上 |
| **Q1 / P4 / T-3 / T-5** | quartet 相容 NP-complete、MP NP-hard、SPR NP-hard、MAST/MAF | ⬇️ **降级** | 「证明 NP-hard……收益不大」（且 mathlib 复杂度框架薄） |
| **L2 / L3 / L4** | Felsenstein 剪枝、ML 一致性、K2P/GTR | ⏸️ **暂缓** | 「似然和贝叶斯也暂缓」 |

### 升级（本轮重点）

| 编号 | 内容 | 处置 |
|---|---|---|
| **I 组全组** | **系统发生不变量**（Cavender–Felsenstein / Lake / Evans–Speed / Sturmfels–Sullivant / Allman–Rhodes / Casanellas） | ⬆️⬆️ **最感兴趣** → **P0** |
| **C 组全组** | **supertree 与共识**（Day / Adams / Bryant / Semple–Steel MinCut / 公理化） | ⬆️⬆️ **也很感兴趣** → **P0** |
| **M1 / M2** | **溯祖理论基座**（Kingman 合并过程、等待时间、ILS 概率） | ⬆️⬆️ **基座必须建立** → **P0** |
| **低垂果实** | Q5 字符相容性定理、C1 严格共识、T-1 KF 距离、I2 Lake 不变量、L1 JC 距离 | ⬆️ **全都要**（含「复现论文方便的」） → **P0/P1** |

### 📚 文献已下载（老师指示「先把论文证明部分的 pdf 下载下来，然后 pdf 也留一份转化出的可读文本」）

**已完成**：`references/` 现有 **18 篇**（PDF + 可读 Markdown 各一份）。
本轮新增 **10 篇**，全部为不变量 / 溯祖 / supertree 三个方向。
**下载失败的见 `references/README.md` §5.1**（附完整链接，老师可自行下载）。

---

## 0. 已形式化对照（避免重复提案）

| 主题 | 状态 | 文件 |
|---|---|---|
| 树 ⟺ split 两两相容（Splits-Equivalence 方向一） | ✅ | `Split.lean` `pairwiseCompatible` |
| 相容 ⟹ 存在树（Aho–Buneman） | ✅ | `Aho.lean` `compatible_exists_rootedTree` |
| 多数共识树（Margush–McMorris） | ✅ | `Consensus.lean` `majority_consensus_exists` |
| UPGMA 结构定理（超度量 ⟹ 球族 ⟹ 树） | ✅ | `Dendrogram.lean` |
| cherry 存在性 | ✅ | `Algorithm/Cherry.lean` `exists_isCherry` |
| Robinson–Foulds 度量性 | ✅ | `Algorithm/RF.lean` |
| 四点条件（作为定义）、Q-判据代数层 | ✅ | `Algorithm/NJ.lean` |
| 二叉树计数、binary 专门层 | ✅ | `Algorithm/BinaryCount.lean`、`Binary.lean` |
| 二叉树 quartet 唯一性（`q_T` 良定义） | ✅ | `QuartetUnique.lean` |
| Colonius–Schultze 推理规则（**一条**：`ab\|ce ∧ ab\|de ⟹ ab\|cd`） | ✅ | `Quartet.lean` |
| 不兼容 split ⟹ 不同 quartet | ✅ | `Binary.lean` |
| ASTRAL 得分理论 + 统计一致性 | ✅ | `Stat/ASTRAL.lean`、`Stat/Stability.lean` |
| CASTER、parsimony 统计一致性 | ✅ | `Stat/CASTER.lean`、`Stat/Parsimony.lean` |
| SVDQuartets **正确性**（无条件） | ✅ | `Stat/SVDQuartets.lean` |
| Fitch 代价（**仅 4 元集**，48 情形枚举） | ⚠️ 部分 | `Stat/Parsimony.lean` `Pattern.fitchCost_eq` |
| NNI 分解（split 层定义） | ⚠️ 部分 | `Algorithm/NNI.lean` |
| MSC 公理化（含 4 元集 ILS 不等式） | ⚠️ **公理** | `Stat/MSC.lean` `majorizes` |
| NJ 樱桃引理 | ⚠️ 缺口 | `Algorithm/NJ.lean` `MaxZCherryCore` |

---

## P0 —— 本轮重点（老师明确点名）

### P0-A ★★★★ 系统发生不变量（I 组）—— 老师「很感兴趣」

**为什么这一组特别值钱**：
1. **与现有基础设施高度复用** —— `Stat/SVDQuartets.lean` 里已有 `Matrix.rank`、
   展平矩阵（flattening）、`rank_le_of_row_symm` 等。**I4（秩/子式刻画）几乎是同一工具箱的另一个定理**。
2. **方向互补** —— 库里现有全是「数据 ⟹ 树」（推断）；不变量是「**树 ⟹ 数据分布**」（正向），
   补上这一半，库才完整。
3. **公式漂亮、可读性强** —— 四点不变量就是一条多项式恒等式，适合做库的「门面」。
4. **文献已下载**（4 篇，见下）。

| # | 定理 | 陈述 | 文献 | ★ | 难度 | 文献状态 |
|---|---|---|---|---|---|---|
| **I1** ⭐ | **四点不变量（Cavender–Felsenstein）** | JC 模型下四元树 `12\|34` 的**多项式恒等式**（与枝长无关）：`(1−4p₁₃/3)(1−4p₂₄/3) − (1−4p₁₄/3)(1−4p₂₃/3) = 0`（`p` = 差异概率）；**另两个拓扑上该式不恒为零** | Cavender & Felsenstein (1987) | ★★★★ | **低–中** | ⚠️ 付费墙；**公式在 `Sturmfels2004_*.md` / `AllmanRhodes2006_*.md` 有完整转述** |
| **I2** ⭐ | **Lake 线性不变量** | JC 下两条**线性**不变量（四项和 = 0），用于进化简约法 | Lake (1987) | ★★★ | **低** | ⚠️ 付费墙；**`CasanellasFernandezSanchez2011_*.md` §5.5 有完整转述** |
| **I3** | **Evans–Speed / Hadamard 变换** | 群基模型的 Fourier 变换把不变量理想变成**二项式**（toric 理想） | Evans & Speed (1993)；Sturmfels & Sullivant (2005) | ★★★ | 中高 | ✅ **Sturmfels–Sullivant PDF 已下载** |
| **I4** ⭐ | **边缘化 ⟹ `rank ≤ 4` ⟹ 子式为零** | 树上过一条边的条件独立性 ⟹ 展平矩阵 `rank ≤ 4` ⟹ 所有 `5×5` 子式为 0（=`binom(16,5)²` 条五阶不变量） | Allman & Rhodes (2003/2006) | ★★★ | **中（与 SVDQuartets 复用）** | ✅ **Allman–Rhodes 2006 PDF 已下载** |
| **I5** | **不变量决定拓扑** | 不变量理想 `I(T)` 唯一决定 `T` | Allman & Rhodes (2003) | ★★★ | 高 | ⚠️ 付费墙 |
| **I6** ⭐ | **edge invariants 足够** | 「对系统发生重建而言，只需**边不变量**」—— 这是 **Buneman Splits-Equivalence 的代数类比** | Casanellas & Fernández-Sánchez (2011) | ★★★★ | 中高 | ✅ **PDF 已下载** |
| **I7** | **Toric 理想的 Gröbner 基** | JC / Kimura 模型的不变量理想在 Fourier 坐标下是 toric 理想，生成元次数 ≤ 4 | Sturmfels & Sullivant (2005) | ★★★ | 高 | ✅ **PDF 已下载** |

> **建议起步顺序**：**I1 → I2 → I4**（三个都是「低–中」难度且文献在手），
> I1/I2 甚至可以先在 `Fin 4 → Bool` 的 16 情形上**穷举验证**（与 `fitchCost_eq` 同一套路），
> 再抽象成一般陈述。**I4 直接复用 `SVDQuartets` 的 rank 层。**

---

### P0-B ★★★ supertree 与共识（C 组）—— 老师「也是」

**为什么值钱**：库里已有 `Consensus.lean`（多数共识）+ `Aho.lean`（相容 ⟹ 树），
**C1（严格共识）几乎是已有的直接收口**；C6（MinCut supertree）则复用 `Aho` 的算法骨架。

| # | 定理 / 算法 | 陈述 | 文献 | ★ | 难度 | 文献状态 |
|---|---|---|---|---|---|---|
| **C1** ⭐ | **严格共识 / 半严格共识** | 严格共识 = **所有树共有的 split**（= split 集求交）；半严格共识 = 只保留在**每棵树中都不冲突**的 split | Day (1985) | ★★ | **低**（复用 `Consensus` + `Aho`） | ⚠️ 付费墙 |
| **C2** | **Adams 共识** | 基于**嵌套**（nesting）的共识，比多数共识更精细（只对有根树） | Adams (1972) | ★★ | 中 | ⚠️ 付费墙 |
| **C3** | **R\* 共识** | 「局部」多数共识；R\* 是多数共识的**精化** | Bryant (2003) | ★★ | 中高 | ⚠️ 付费墙（Bryant 2003 是综述，章节清晰） |
| **C4** | **贪心共识** | 反复合并支持度最高的簇 | Bryant (2003) | ★★ | 中 | 同上（同一篇） |
| **C5** | **共识的公理化刻画** | 一致性 / 匿名性 / 中立性等公理 ⟹ 唯一共识函数 | McMorris & Neumann；Steel et al. | ★★★ | 高 | ⚠️ 付费墙 |
| **C6** ⭐ | **MinCut Supertree** | 修改 Aho 算法：图不连通时删**最小割边集**，得到 rooted supertree；**相容时输出展示所有输入树** | **Semple & Steel (2000)** | ★★★ | 中高 | ⚠️ 付费墙；**UC 仓储有全文**（链接见 `references/README.md`） |
| **C7** | **Supertree 不存在性（一般情形）** | 无根情形下**不存在**「合理」的 supertree 方法 | Steel, Dress & Böcker (2000) | ★★★ | 中 | ⚠️ 付费墙 |

> **建议起步**：**C1**（低垂果实，直接收口）→ **C6**（MinCut，复用 Aho；且它同时是「supertree」的代表）。

---

### P0-C ★★★★ 溯祖理论基座（M 组）—— 老师「基座得建立起来」

**为什么是「基座」**：这一组是 `Stat/` 整个 MSC 层的**公理来源**。
现在 `MSCFreq.majorizes` 是**假设**；做了 M1 之后它变成**定理**，
库从「公理化 MSC」升级为「**推导出的 MSC**」。

| # | 定理 / 算法 | 陈述 | 文献 | ★ | 难度 | 文献状态 |
|---|---|---|---|---|---|---|
| **M1** ⭐⭐ | **4 元集 ILS 公式** | `P(ab\|cd) = 1 − ⅔e^{−t}`，`P(ac\|bd) = P(ad\|bc) = ⅓e^{−t}`（`t` = 内部枝长，**溯祖单位**） | Kingman (1982)；Tajima (1983)；Hudson (1983)；Pamilo & Nei (1988) | ★★★★★ | 中高 | ⚠️ 原文付费墙；**`ChifmanKubatko2015_*.md` / `AllmanRhodes2006_*.md` 有完整推导** |
| **M2** ⭐ | **溯祖等待时间（Kingman 合并过程）** | `k` 个谱系合并到 `k−1` 的等待时间 ~ `Exp(C(k,2))`；故 `E[T_k] = 2/(k(k−1))`（`N` 单位下 `1/C(k,2)`）；`E[T_MRCA] = 2(1−1/n)` | Kingman (1982) | ★★★★ | 中高 | ⚠️ 付费墙；**`StadlerDegnan2012_*.md` / `AllmanDegnanRhodes2017_*.md` 有转述** |
| **M3** | 异常基因树（anomalous gene trees）**反例** | 存在物种树 + 枝长，使**最可能的基因树拓扑 ≠ 物种树拓扑** | Degnan & Salter (2005)；Degnan & Rosenberg (2006) | ★★★ | 中 | ⬇️ **本轮降级** |
| **M4** ⭐ | **site pattern 概率（MSC + JC）** | 4 元集上所有 site pattern 的**显式概率** | Chifman & Kubatko (2015) | ★★★ | 中高 | ✅ **PDF 已下载** |
| **M5** | **ASTRAL 的局部性 / 分支长度估计** | 由 quartet 频率算**局部后验概率**与**溯祖单位枝长**（`t = −ln(1 − 1.5·(1−p̂))` 形式） | Sayyari & Mirarab (2016) | ★★★ | 中 | ✅ **PDF 已下载** |
| **M6** | **STAR / NJst 归约与一致性** | STAR 与推广是统计一致的；NJst 归约到 generalized STAR；**用到的只是 split 分布** | ADR (2013) STAR；ADR (2016) NJst；ADR (2017) split probabilities | ★★★ | 中高 | ✅ **三篇 PDF 均已下载** |
| **M7** | **基因树分布可算（COAL）** | 给定物种树，基因树拓扑的分布可**显式递推** | Degnan & Salter (2005) | ★★★ | 中高 | ⚠️ 付费墙 |
| **M8** | **unrooted 基因树决定有根物种树** | ≥5 物种时，**无根**基因树分布可识别有根的物种树拓扑与全部内部枝长 | ADR (2011) | ★★★ | 中高 | ✅ **PDF 已下载** |

> **建议起步顺序**：
> **M2**（等待时间：只需指数分布 `Exp(λ)` 的期望/方差，**是整组里最轻的**）
> → **M1**（ILS 公式：可由 M2 + 「3 谱系随机合并」推）
> → 之后 M4/M5/M8 都是 M1 的下游。
>
> **⚠️ 关键设计判断**：M1 可以走**有限化**路线 —— 把「溯祖等待时间」的分布作为
> **已有定理 M2** 接入，而不必先建完整的随机过程框架。这样 M1 就不需要
> 概率空间 + 大数定律，只需**有限概率模型**（与 `fitchCost_eq` 的 16 情形枚举同一档次）。
> **`MSCSampling.converges`（大数定律）建议长期保持公理化。**

---

### P0-D ★★★ 低垂果实包（老师「都要」）+ 论文复现友好

「低垂果实」= 与库内已有设施**直接对接**、且**证明本身短**的目标。

| # | 定理 | 陈述 | 文献 | ★ | 难度 | 文献状态 |
|---|---|---|---|---|---|---|
| **F1** ⭐ | **字符相容性定理**（pairwise compatibility theorem） | **两两相容 ⟹ 全局相容**（对「真分化」字符）；形式化为：一族字符两两相容 ⟺ 存在一棵树使全体无同塑性 | Estabrook, Johnson & McMorris (1976)；Meacham (1981) | ★★★ | **低–中** | ⚠️ 付费墙；**密歇根 Deep Blue 有全文**（链接见 README） |
| **F2** ⭐ | **严格/半严格共识** | 见 **C1** | Day (1985) | ★★ | **低** | — |
| **F3** ⭐ | **KF 距离（branch score）** | `KF(T,T') = √( Σ_e (w_e − w'_e)² )`（缺边算 0）；对称、非负、零 ⟺ 同树同权 | Kuhner & Felsenstein (1994) | ★★ | **低** | ⚠️ 付费墙；**公式清楚**（`references/README.md` 有转述） |
| **F4** ⭐ | **Jukes–Cantor 距离校正** | `d = −¾·ln(1 − (4/3)p)`（`p` = 差异比例）；`p < ¾` 时良定义 | Jukes & Cantor (1969) | ★★ | **低** | ⚠️ 书章，付费墙；**公式在 `Sturmfels2004_*.md` 有** |
| **F5** ⭐ | **Lake 线性不变量** | 见 **I2** | Lake (1987) | ★★★ | **低** | 同上 |
| **F6** | **Buneman 树 / split 分解** | Buneman 指数 `μ_σ(δ) > 0` 的 split 集必**相容** ⟹ 给出「保留树」`B(δ)` | Buneman (1971)；Bandelt & Dress (1986) | ★★★ | 中 | ✅ **Buneman 1971/1974 已下载**；Bandelt–Dress 付费墙 |
| **F7** | **rooted triplet 的一致性（Aho 的有根版）** | 相容 rooted triple 集 ⟹ 存在展示它的有根树 | Aho et al. (1981)；Bryant & Steel (1995) | ★★★ | 中 | ⚠️ 付费墙 |
| **F8** | **Fitch 一般树推广 / Sankoff** | 把现有 4 元集 Fitch 推广到任意树 + 任意状态数；Sankoff 允许任意代价矩阵 | Fitch (1971)；Sankoff (1975) | ★★★ | 中高 | ⚠️ 付费墙 |
| **F9** | **严格共识的「树空间」性质** | 严格共识 = split 交；与 RF 距离的关系 | Day (1985) | ★★ | 低 | ⚠️ 付费墙 |

> **建议起步**：**F2（=C1）** → **F3（KF）** → **F4（JC 距离）** → **F5（=I2）** → **F1（字符相容性）**。
> 前四个**全都是「低」难度**，可快速把库的「距离 + 共识 + 代数」三块填满。

---

## P1 —— 排在其后（老师未点名，但有分量且能接）

| # | 定理 | 陈述 | 文献 | ★ | 难度 |
|---|---|---|---|---|---|
| **D1** | **Atteson 安全半径 1/2** | 距离估计误差 < ½·最小内部边长 ⟹ NJ 输出正确拓扑 | Atteson (1999) | ★★★ | 中 |
| **D2** | **Pauplin 公式** | NJ 贪心最小化的是树长的 Pauplin 估计 `L(T) = Σ_{i<j} 2^{1−n_ij} d_ij` | Pauplin (2000)；Gascuel & Steel (2006) | ★★ | 中 |
| **D3** | **BME 与 NJ 的关系** | 平衡最小演化；BME 的 `l∞` 安全半径也是 1/2 | Desper & Gascuel (2004)；Pardi et al. (2010) | ★★ | 中高 |
| **Q2** | **quartet 距离** | `d_Q(T,T')` 的度量性质、与 RF 的不等式；最大 quartet 距离（flag algebra 的 2/3·C(n,4)） | Estabrook et al. (1985)；Alon–Snir–Yuster (2008) | ★★ | 中 |
| **N3** ⭐ | **level-1 网络由 quarnet 决定** | quarnet 推理规则（C–S 的网络版） | Huber, Moulton, Semple, Wu (2018) | ★★★★ | 高 |
| **T-1** | **KF（见 F3）** | — | — | — | — |
| **T-6** | **Buneman 图（见 F6）** | split 系统相容 ⟺ Buneman 图是树 | Buneman (1971) | ★★★ | 中高 |
| **T-4** | **NNI 图连通 / NNI 距离** | NNI 邻域连通树空间；线性时间估计 | Robinson (1971)；Sleator et al. (1992) | ★★ | 中高 |

---

## P2 —— 降级 / 暂缓（老师指示）

| # | 定理 | 处置 | 理由 |
|---|---|---|---|
| **P1** | Felsenstein 1978 长枝吸引反例 | ⬇️ 降级 | 「构造反例……收益不大」 |
| **M3** | 异常基因树反例 | ⬇️ 降级 | 同上 |
| **Q1** | quartet 相容性 NP-complete | ⬇️ 降级 | 「证明 NP-hard……收益不大」 |
| **P4** | 最大简约 NP-hard（Foulds–Graham） | ⬇️ 降级 | 同上 |
| **T-3** | SPR 距离 NP-hard | ⬇️ 降级 | 同上 |
| **T-5** | MAST / MAF NP-hard | ⬇️ 降级 | 同上 |
| **Q3** | MQC 近似算法 | ⬇️ 降级 | 依赖 Q1 |
| **L2** | Felsenstein 剪枝算法 | ⏸️ 暂缓 | 「似然和贝叶斯也暂缓」 |
| **L3** | 最大似然统计一致性 | ⏸️ 暂缓 | 同上 |
| **L4** | Kimura 2 参数 / GTR | ⏸️ 暂缓 | 同上 |
| **T-2** | BHV 是 CAT(0) | ⏸️ 暂缓 | 极难（数学分量最高，但工作量极大） |
| **N5** | 杂交数 | ⏸️ 暂缓 | 极高难度 |

---

## 3. 推荐执行序列（本轮重排后）

```
第 0 批（现役，dsh 在做）：T2 → T0.1（QuartetDecidesTree）   ← 见 HANDOVER.md §4

第 1 批 ★ 低垂果实（难度全「低」，快速见效）
   F2 严格共识（=C1）→ F3 KF 距离 → F4 JC 距离校正 → F5 Lake 不变量（=I2）

第 2 批 ★★ 不变量组（老师最感兴趣）
   I1 四点不变量 → I4 秩/子式刻画（复用 SVDQuartets 的 Matrix/rank 层）
   → I6 edge invariants 足够（Buneman 定理的代数类比）→ I3/I7 toric 理想

第 3 批 ★★★★ 溯祖基座（老师要求「基座得建立起来」）
   M2 等待时间（最轻）→ M1 4 元集 ILS 公式（可选有限化路线）
   → M4 site pattern 概率 / M5 ASTRAL 局部支持 / M8 unrooted ⟹ rooted

第 4 批 ★★ supertree（老师「也是」）
   C6 MinCut Supertree（复用 Aho）→ C2 Adams → C3/C4 R*/贪心

后续：F1 字符相容性 → F6 Buneman 树 → P1 组（Atteson / Pauplin / 距离族）
余力：N3 level-1 网络、T-4 NNI 图、Q2 quartet 距离
```

---

## 4. 备注

### 4.1 文献状态总览

**已下载（18 篇，PDF + MD）**：见 `references/README.md`。本轮新增 10 篇：

| 方向 | 新增 |
|---|---|
| **不变量** | Sturmfels–Sullivant 2005（toric 理想）、Allman–Rhodes 2006（一般 Markov 理想）、**Casanellas–Fernández-Sánchez 2011（edge invariants）**、Sturmfels 2004（代数几何综述）、Allman–Rhodes 2011（tripod 两状态） |
| **溯祖** | Sayyari–Mirarab 2016（ASTRAL 局部支持）、ADR 2013（STAR 推广）、ADR 2017（split 概率）、ADR 2011（unrooted ⟹ rooted）、Stadler–Degnan 2012（ranked 基因树概率） |

**下载失败（附链接，老师可自行下载）**：见 `references/README.md` **§5.1**。
关键几条：Cavender–Felsenstein 1987、Lake 1987、Evans–Speed 1993、Allman–Rhodes 2003、
Day 1985、Adams 1972、Bryant 2003、Semple–Steel 2000、Kingman 1982、Tajima 1983、
Hudson 1983、Degnan–Salter 2005、Estabrook et al. 1976、Meacham 1981、Kuhner–Felsenstein 1994。

> ⭐ **好消息**：**多数失败条目的关键公式/证明已在上表「已下载」的文献里有完整转述** ——
> 例如 I1/I2（四点不变量、Lake 不变量）在 `Sturmfels2004` 与 `AllmanRhodes2006` 中，
> M1（ILS 公式）在 `ChifmanKubatko2015` 中。**故不阻塞推进**。

### 4.2 关于复杂度类定理（已降级，此处仅存档理由）

Mathlib 的**计算复杂度理论很薄**（无图灵机/归约的成熟框架），自建框架本身是大工程
（数万行量级）。⇒ 已按老师指示降级。若将来要做，建议**只形式化归约的组合内核**，
把「NP-hard」这层显式声明为 `def … : Prop` 缺口（本库既有惯例）。

### 4.3 关于「复现论文方便的」

老师点名要「包括复现论文方便的」。已识别的高复现友好目标：
- **I1/I4** —— 公式显式、可在 `Fin 4 → Bool`（16 情形）上**穷举验证**，与 `fitchCost_eq` 同套路。
- **M1** —— 4 元集、有限概率空间、可数值验证（`ChifmanKubatko2015` 给了完整推导）。
- **F3/F4** —— 单个闭式公式，几乎无结构。
- **C1/F2** —— 直接复用 `Consensus.lean` + `Aho.lean`，收口即可。

### 4.4 去公理化路线图

| 现有公理 | 位置 | 对应命题 | 本清单编号 |
|---|---|---|---|
| `MSCFreq.majorizes` | `Stat/MSC.lean` | 4 元集 ILS 公式 | **M1** |
| `MSCSampling.converges` | `Stat/MSC.lean` | 大数定律 | （长期保留公理化） |
| `MSCSite.majorizes` | `Stat/Parsimony.lean` | ISM 支持数唯一最大 | （需 ISM 概率模型） |
| `SiteSampling.converges` | `Stat/Parsimony.lean` | 位点大数定律 | （长期保留公理化） |
| `NJstData.fourPoint` | `Stat/NJst.lean` | ADR 2016 的四点条件 | **M6** |
| `NJstData.core` | `Stat/NJst.lean` | NJ 樱桃引理 | T0.3（已在 HANDOVER） |
| `MaxZCherryCore` | `Algorithm/NJ.lean` | NJ 樱桃引理 | T0.3（已在 HANDOVER） |
| `QuartetDecidesTree` | `Stat/QuartetDecides.lean` | C–S 定理 | T0.1（已在 HANDOVER） |

---

## 5. 一句话总览

> **本轮重心**：**不变量（I 组）** —— 老师最感兴趣，且与 `SVDQuartets` 的
> `Matrix`/rank 工具箱高度复用；
> **溯祖基座（M 组）** —— 把 `majorizes` 从公理变成定理；
> **supertree（C 组）** —— MinCut 复用 Aho；
> **低垂果实包（F 组）** —— 全「低」难度，快速填满距离/共识/代数三块。
> **已降级**：NP-hard 复杂度类与反例型构造；**已暂缓**：似然与贝叶斯。
