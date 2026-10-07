# NEXT.md —— 下一步需求提案（计算系统发生学 · 未形式化的知名定理与算法）

> **生成**：2026-10-07
> **用途**：给老师挑下一批形式化目标。**不是执行计划**（执行计划见 `HANDOVER.md` §4）。
> **原则**：只列**还没有**的；已形式化的见 §0 对照表。
> **评级**：★ 数量 = 学术分量；**难度** = Lean 形式化工作量（不是数学难度）。

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

## 1. ⭐ 特别推荐：两类「高性价比」目标

在列清单之前，先点出**两类型式化性价比极高**的目标 —— 它们往往被忽视，但对定理库价值很大。

### 类型 I：**反例型定理**（有限、具体、可判定）

「某方法不一致 / 某命题不成立」的**具体反例**。特点是：**全有限、可 `decide`、无需无穷渐近或概率空间**，
但学术分量极高（Felsenstein 1978 是系统发生学最重要的论文之一，就因为它是一个反例）。

### 类型 II：**去公理化**（把 `structure` 字段变成 `theorem`）

本库现在有 5 处**公理化假设**（`MSCFreq.majorizes`、`MSCSampling.converges`、
`MSCSite.majorizes`、`SiteSampling.converges`、`NJstData.{fourPoint, core}`）。
每去掉一条，库的「无条件定理」计数就 +1。这是**最有可见度**的进展方向。

---

## 2. 候选清单（按主题）

### 2.1 距离法 / NJ 家族

| # | 定理 / 算法 | 陈述 | 文献 | ★ | 难度 | 依赖 |
|---|---|---|---|---|---|---|
| **D1** | **Atteson 安全半径定理** | NJ 的 `l∞` 安全半径 = 1/2：若估计距离与真树度量的 `l∞` 偏差 < ½·(最小内部边长)，NJ 输出正确拓扑 | Atteson (1999) | ★★★ | 中 | NJ 硬核（T0.3）+ 距离扰动层 |
| **D2** | **Pauplin 公式 / 树长估计** | NJ 贪心最小化的是**整棵树长**的 Pauplin 估计 `L(T) = Σ_{i<j} 2^{1-n_ij} d_ij`；Gascuel–Steel 的「NJ 到底在优化什么」的答案 | Pauplin (2000)；Gascuel & Steel (2006) | ★★ | 中 | 已有 `NJ.z` 层 |
| **D3** | **平衡最小演化（BME）** | BME 的解在 `l∞` 下安全半径 1/2（Pardi–Guillemot–Gascuel）；BME 与 NJ 的关系 | Desper & Gascuel (2004)；Pardi et al. (2010) | ★★ | 中高 | D2 |
| **D4** | **Buneman 树 / split 分解** | Buneman 指数 `μ_σ(δ) > 0` 的 split 集必相容 ⟹ 给出「保留树」`B(δ)` | Buneman (1971)；Bandelt & Dress (1986) | ★★★ | 中 | T0.2 |
| **D5** | **四分点条件 ⟺ 树度量（构造方向）** | = T0.2，此处仅登记 | Buneman (1971/74) | ★★★ | 中 | — |

> **D1 的价值**：Atteson 定理是「NJ 为什么在实践中管用」的**官方答案**。
> 有了 T0.3 之后它是自然的下一步，且把库从「拓扑正确」推进到「**抗噪正确**」。

---

### 2.2 特征法 / 简约法

| # | 定理 / 算法 | 陈述 | 文献 | ★ | 难度 | 依赖 |
|---|---|---|---|---|---|---|
| **P1** ⭐ | **Felsenstein 1978：简约法可被正向误导（长枝吸引）** | **具体的 4 元树 + 具体参数**，使简约法在数据量 → ∞ 时**收敛到错误拓扑** | Felsenstein (1978) | ★★★★ | **中**（反例型！） | 已有 Fitch（4 元集） |
| **P2** | **Sankoff 算法（广义简约）** | 任意代价矩阵下的加权简约，DP 递推；Fitch 是其特例 | Sankoff (1975) | ★★★ | 中 | 已有 Fitch 4 元集 |
| **P3** | **Fitch 算法正确性（一般树）** | 把现有的 48 情形枚举**推广到任意树**：DP 递推的代价 = 最小替换数 | Fitch (1971) | ★★★ | 中高 | `Pattern.fitchCost_eq` |
| **P4** | **最大简约是 NP-hard** | Foulds–Graham 归约（小简约 ⟹ 顶点覆盖） | Foulds & Graham (1982) | ★★★ | 高（需复杂度框架） | — |
| **P5** | **ML ⟺ MP 等价（Tuffley–Steel）** | 在「无共同机制 / Poisson 模型」下，最大似然树 = 最大简约树 | Tuffley & Steel (1997) | ★★ | 中高 | P1–P3 |

> **P1 是整份清单里我最想推的一格**：它**全有限、可判定**（一棵 5 顶点树 + 4 个参数），
> 但结论是「**某著名方法不一致**」—— 学术分量极高，形式化却不需要概率空间。
> 而且库内**已有 Fitch 的 4 元集计算**，直接接得上。

---

### 2.3 似然 / 替换模型

| # | 定理 / 算法 | 陈述 | 文献 | ★ | 难度 | 依赖 |
|---|---|---|---|---|---|---|
| **L1** | **Jukes–Cantor 距离校正公式** | `d = −¾·ln(1 − (4/3)·p)`（`p` = 差异比例） | Jukes & Cantor (1969) | ★★★ | **低** | 纯代数 |
| **L2** | **Felsenstein 剪枝算法** | 树上的似然计算：叶→根 DP，把 `O(4^n)` 降到 `O(n·4^2)` | Felsenstein (1981) | ★★★★ | 中高 | 需替换模型层 |
| **L3** | **最大似然的统计一致性** | 模型正确 ⟹ ML 树在数据量 → ∞ 时收敛到真树 | Wald (1949)；Felsenstein (1981)；Steel (2016) | ★★★ | 高 | L2 + 概率层 |
| **L4** | **Kimura 2 参数 / GTR 模型** | 更一般的替换模型及其可识别性 | Kimura (1980)；Tavaré (1986) | ★★ | 中 | L1 |

---

### 2.4 代数统计 / 系统发生不变量 ⭐（我认为最被低估的一类）

| # | 定理 / 算法 | 陈述 | 文献 | ★ | 难度 | 依赖 |
|---|---|---|---|---|---|---|
| **I1** ⭐ | **四点不变量（Cavender–Felsenstein）** | JC 模型下，四元树 `12\|34` 的**多项式恒等式**（与枝长无关）：`(1−4p₁₃/3)(1−4p₂₄/3) − (1−4p₁₄/3)(1−4p₂₃/3) = 0` | Cavender & Felsenstein (1987) | ★★★★ | **低–中** | L1 + 已有 `Matrix` 层 |
| **I2** | **Lake 线性不变量** | JC 下的两条**线性**不变量（四项和 = 0） | Lake (1987) | ★★★ | **低** | 纯代数 |
| **I3** | **Evans–Speed / Hadamard 变换** | 群基模型的 Fourier 变换把不变量理想变成**二项式**（toric 理想） | Evans & Speed (1993)；Sturmfels & Sullivant (2005) | ★★★ | 中高 | I1 |
| **I4** | **边缘化 ⟹ 秩 ≤ 4 / 子式为零** | 树上「过一条边的条件独立性」⟹ 展平矩阵 `rank ≤ 4` ⟹ 所有 `5×5` 子式为 0 | Allman & Rhodes (2003/2007) | ★★★ | 中 | **已有 `SVDQuartets` 的 rank 层！** |
| **I5** | **不变量决定拓扑** | 不变量理想 `I(T)` 唯一决定 `T`（一般情况下） | Allman & Rhodes (2003) | ★★★ | 高 | I1–I4 |

> **I1 / I4 与本库的契合度极高**：`Stat/SVDQuartets.lean` 里已经有 `Matrix.rank`、
> 展平矩阵、`rank_le_of_row_symm` 等基础设施 —— **I4 几乎是同一个工具箱的另一个定理**。
> 而且「不变量」是**「树 ⟹ 数据分布」的正向定理**，与库里现有的「数据 ⟹ 树」方向互补。

---

### 2.5 Quartet / triplet 组合

| # | 定理 / 算法 | 陈述 | 文献 | ★ | 难度 | 依赖 |
|---|---|---|---|---|---|---|
| **Q1** | **Quartet 相容性是 NP-complete** | 判断给定 quartet 集能否被某棵树展示 | Steel (1992) | ★★★★ | 高（需复杂度框架） | — |
| **Q2** | **Four-point / quartet 距离** | `d_Q(T,T')` 的度量性质、与 RF 的不等式关系、最大 quartet 距离（flag algebra 结果 2/3·C(n,4)） | Estabrook et al. (1985)；Alon–Snir–Yuster (2008) | ★★ | 中 | 已有 `Quartet.lean` |
| **Q3** | **最大 quartet 相容性（MQC）近似** | `O(n²)` 4-近似（或更好的 0.5-近似） | Jiang et al. (2001) | ★★ | 高 | Q1 |
| **Q4** | **Triplet 一致性（Aho 的 rooted 版）** | 相容 rooted triple 集 ⟹ 存在展示它的有根树；`DAG` 构造 | Aho et al. (1981)；Bryant & Steel (1995) | ★★★ | 中 | **已有 `Aho.lean`（无根版）** |
| **Q5** | **字符相容性定理（perfect phylogeny）** | 两两相容 ⟺ 全局相容（Estabrook–Johnson–McMorris / Meacham 的「pairwise compatibility theorem」） | Estabrook et al. (1976)；Meacham (1981) | ★★★ | 中 | **已有 `Split.Compatible`** |

> **Q5 是「低垂果实」**：库内已有 `Split.Compatible` 与 `pairwiseCompatible`，
> 而 pairwise compatibility theorem 正是「**两两 ⟹ 全局**」 —— 与已有的
> `pairwiseCompatible`（树 ⟹ 两两）方向互补，收口很自然。

---

### 2.6 树比较 / 重排 / 树空间

| # | 定理 / 算法 | 陈述 | 文献 | ★ | 难度 | 依赖 |
|---|---|---|---|---|---|---|
| **T-1** | **KF 距离（branch score）** | `Σ (w_e − w'_e)²`；对称、非负、零 ⟺ 同树同权 | Kuhner & Felsenstein (1994) | ★★ | **低** | 已有 `RF.lean` |
| **T-2** | **BHV 树空间是 CAT(0) 度量空间** | 加权树的空间（split 权重向量 + 树长）带 BHV 度量，是 CAT(0)（Hadamard） | Billera, Holmes & Vogtmann (2001) | ★★★★★ | 极高 | T-1 |
| **T-3** | **SPR 距离是 NP-hard** | 计算两树的 SPR 距离 | Bordewich & Semple (2005) | ★★★ | 高 | — |
| **T-4** | **NNI 距离 / NNI 图连通** | NNI 邻域连通树空间（Sleator–Tarjan–Thurston：线性时间估计） | Robinson (1971)；Sleator et al. (1992) | ★★ | 中高 | 已有 `NNI.lean` |
| **T-5** | **MAST / MAF 是 NP-hard** | 最大一致子树（MAST）、最大一致森林（MAF） | Amir & Keselman (1997)；Hein et al. (1996) | ★★★ | 高 | — |
| **T-6** | **Buneman 图** | 由 split 系统构造的图；split 系统相容 ⟺ Buneman 图是树 | Buneman (1971)；Bandelt & Dress (1986) | ★★★ | 中高 | `Split.lean` |

---

### 2.7 共识与 supertree

| # | 定理 / 算法 | 陈述 | 文献 | ★ | 难度 | 依赖 |
|---|---|---|---|---|---|---|
| **C1** | **严格共识 / 半严格共识** | 严格共识 = 所有树共有的 split；正规性 | Day (1985) | ★★ | **低** | **已有 `Consensus.lean`** |
| **C2** | **Adams 共识** | 基于嵌套（nesting）的共识，比多数共识更精细 | Adams (1972) | ★★ | 中 | C1 |
| **C3** | **R\* 共识** | 「局部」多数共识；R* 是多数共识的精化 | Bryant (2003) | ★★ | 中高 | C1 |
| **C4** | **贪心共识** | 反复合并最多支持的簇 | Bryant (2003) | ★★ | 中 | C1 |
| **C5** | **共识的公理化刻画** | 一致性/匿名性/中立性等公理 ⟹ 唯一共识函数 | McMorris & Neumann；Steel et al. | ★★★ | 高 | C1–C4 |
| **C6** | **MinCut Supertree** | 最小割启发式超树 | Semple & Steel (2000) | ★★ | 中高 | — |

> **C1 是本表最便宜的一格**：库里已有 `majority_consensus_exists`，
> 严格共识只需在 **已有的 split 交集**上再走一遍 `Aho.lean`。

---

### 2.8 网络

| # | 定理 / 算法 | 陈述 | 文献 | ★ | 难度 | 依赖 |
|---|---|---|---|---|---|---|
| **N1** | **Split decomposition / Buneman 图** | 见 T-6 | Bandelt & Dress (1992) | ★★★ | 中高 | T-6 |
| **N2** | **NeighborNet** | 基于距离的网络构造（split graph 的贪心实现） | Bryant & Moulton (2004) | ★★ | 高 | N1 |
| **N3** | **Level-1 网络由 quarnet 决定** | quarnet 推理规则（C–S 的网络版） | Huber, Moulton, Semple, Wu (2018) | ★★★★ | 高 | **已有 C–S 树版 + 该文 PDF！** |
| **N4** | **Trinet / 有根网络** | 有根 trinet 决定 level-1 网络 | Huber & Moulton 等 | ★★★ | 高 | N3 |
| **N5** | **杂交数（hybridization number）** | 计算最小杂交数；FPT 算法 | Bordewich & Semple | ★★★ | 极高 | — |

> **N3 有个现成优势**：Huber 2018 的 PDF 已经躺在 `references/pdf/` 里了（为 T0.1 抓的）。
> 它的 Theorem 2 就是「quarnet 系统 ⟺ level-1 网络」，与 T0.1 同一篇论文 —— **读完不用另找文献**。

---

### 2.9 溯祖 / 种群遗传 ⭐（去公理化主战场）

| # | 定理 / 算法 | 陈述 | 文献 | ★ | 难度 | 依赖 |
|---|---|---|---|---|---|---|
| **M1** ⭐ | **4 元集 ILS 公式** | `P(ab\|cd) = 1 − ⅔·e^{−t}`，`P(ac\|bd) = P(ad\|bc) = ⅓·e^{−t}`（`t` = 内部枝长，溯祖单位） | Kingman (1982)；Tajima (1983)；Hudson (1983) | ★★★★★ | 中高 | 概率层 |
| **M2** | **溯祖的等待时间** | `k` 谱系合并到 `k−1` 的等待时间 ~ Exp(`C(k,2)`)；`E[T] = 1/C(k,2)` | Kingman (1982) | ★★★★ | 中高 | 概率层 |
| **M3** | **异常基因树（anomalous gene trees）** | 存在物种树 + 枝长，使**最可能的基因树拓扑 ≠ 物种树拓扑**（具体反例） | Degnan & Salter (2005) | ★★★★ | **中**（反例型！） | M1 |
| **M4** | **ILS 下 site pattern 的概率** | 4 元集上所有 site pattern 的显式概率（MSC + JC） | Chifman & Kubatko (2015) | ★★★ | 中高 | M1 |
| **M5** | **ASTRAL 的局部性** | ASTRAL 得分可分解到四元集（`Σ` 形式的正确性） | Sayyari & Mirarab (2016) | ★★★ | 中 | **已有 `Stat/ASTRAL.lean`** |
| **M6** | **STAR / NJst 归约** | NJst 一致性归约到 generalized STAR | ADR (2016) | ★★★ | 中高 | T0.4 |

> **M1 是整份清单的「皇冠」**：它是系统发生学**引用最多**的公式，而且形式化它
> **直接把 `Stat/MSC.lean` 的 `majorizes` 从公理变成定理** —— 库的无条件定理数立刻 +1，
> 且从「公理化 MSC」升级为「**推导出的 MSC**」。
> **M3 是它的「便宜版」**：同样是反例型，只需 4 元集 + 具体参数，**可判定**。

---

## 3. 推荐 top-5（若只做五件）

| 顺序 | 目标 | 为什么 | 难度 |
|---|---|---|---|
| **1** | **P1 Felsenstein 1978 长枝吸引反例** | **反例型**：全有限、可判定、不需概率空间；学术分量最大（系统发生学最著名论文之一）；库内已有 Fitch 4 元集，直接接得上 | 中 |
| **2** | **I1 + I4 系统发生不变量（Cavender–Felsenstein 四点不变量 + 秩/子式刻画）** | 与现有 `SVDQuartets` 的 `Matrix`/rank 工具箱**高度复用**；「树 ⟹ 分布」正向视角，与库里反向（分布 ⟹ 树）互补；公式漂亮、可读性强 | 低–中 |
| **3** | **Q5 + C1 低垂果实包**（字符相容性定理 + 严格共识） | 已有 `Compatible` / `pairwiseCompatible` / `majority_consensus_exists`，**收口最省力**，能快速把「共识 + 相容」两块补完整 | 低 |
| **4** | **M1 4 元集 ILS 公式** | 形式化系统发生学最著名公式；**去公理化**（`majorizes` → 定理）；解锁 M3/M4/M6 | 中高 |
| **5** | **D1 Atteson 安全半径** | 回答「NJ 为什么管用」；把库从「拓扑正确」推到「**抗噪正确**」；T0.3 后自然衔接 | 中 |

**若按「学术分量」单排**：M1 ≈ T-2 > P1 > Q1 > N3 > D1。
**若按「性价比」（分量 ÷ 工作量）单排**：**P1 > I1 > Q5 ≈ C1 > T-1 > L1 > I2**。

---

## 4. 三条备注

### 4.1 关于「复杂度类定理」（Q1 / P4 / T-3 / T-5）

它们都是**著名 NP-hard 结果**，学术分量很高，但需要**复杂度理论框架**（图灵机、归约的定义）。
Mathlib 在计算复杂度上很薄，自建框架本身就是一个大工程。
⇒ **建议**：**不作为近期目标**。若真要做，先做 **P4（Foulds–Graham）** ——
它的归约最具体（小简约 ⟹ 顶点覆盖），可以只形式化「**归约的正确性**」这个组合内核，
把「NP-hard」这层复杂度包装**显式声明为** `def … : Prop` 缺口（**本库既有惯例**）。

### 4.2 关于「需要概率空间」的（L3 / M1 / M2）

真概率层需要：概率空间 + 随机变量 + 大数定律 + 条件期望。
Mathlib 有较完整的测度论（`MeasureTheory`），但 Kingman 溯祖要从**随机过程**建起（数万行量级）。
⇒ **建议**：
- **M1 可以先做「有限化」版本** —— 4 元集 ILS 公式**可以从「随机选择拓扑」的有限概率模型推**，
  不必先建完整溯祖过程（把溯祖的等待时间分布作为假设）。
- **M2 的期望值部分**（`E[T_k] = 1/C(k,2)`）只要指数分布，相对轻。
- **`MSCSampling.converges`（大数定律）** 建议长期保持公理化。

### 4.3 关于 `references/`

新目标**先查 `references/README.md`** 里有没有现成 PDF。已抓的 8 篇里：
Huber 2018 还覆盖 **N3**（quarnet/level-1 网络）、Mihaescu 2006 覆盖 **D1/Atteson**
（其 Theorem 2 就是 Atteson 定理）、Chifman–Kubatko 2015 覆盖 **M4**。
⇒ **N3、D1、M4 的文献已在手**，无需重新找。

---

## 5. 与本库现有「公理化」的对应（去公理化路线图）

| 现有公理 | 位置 | 对应命题 | 本清单编号 |
|---|---|---|---|
| `MSCFreq.majorizes` | `Stat/MSC.lean` | 4 元集 ILS 公式 | **M1** |
| `MSCSampling.converges` | `Stat/MSC.lean` | 大数定律 | （长期保留公理化） |
| `MSCSite.majorizes` | `Stat/Parsimony.lean` | ISM 支持数唯一最大 | 未列（需 ISM 概率模型） |
| `SiteSampling.converges` | `Stat/Parsimony.lean` | 位点大数定律 | （长期保留公理化） |
| `NJstData.fourPoint` | `Stat/NJst.lean` | ADR 2016 的四点条件 | **M6** |
| `NJstData.core` | `Stat/NJst.lean` | NJ 樱桃引理 | T0.3（已在 HANDOVER） |
| `MaxZCherryCore` | `Algorithm/NJ.lean` | NJ 樱桃引理 | T0.3（已在 HANDOVER） |
| `QuartetDecidesTree` | `Stat/QuartetDecides.lean` | C–S 定理 | T0.1（已在 HANDOVER） |

⇒ **去公理化清单**：`majorizes` → **M1**；`fourPoint` → **M6**；
其余三条（大数定律 ×2、ISM）建议长期保持公理化。

---

## 6. 一句话总览

> **近期最想做的三件**：**P1（长枝吸引反例）**、**I1+I4（系统发生不变量）**、
> **Q5+C1（相容性定理 + 严格共识，低垂果实）**。
> **最有分量的长期目标**：**M1（4 元集 ILS 公式，去公理化）** 与 **T-2（BHV 是 CAT(0)）**。
