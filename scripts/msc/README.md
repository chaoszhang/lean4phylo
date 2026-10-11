# `scripts/msc/` —— W9 / 缺口 G5′（MSC 溯祖层）的独立复核脚本

## `kingman_check.py`

**协调侧（dsh 主会话）写的独立数值复核**，用于在相信 `Phylo/Stat/MSCKingman.lean`
的构造之前，先把它的**数学内容**从 4 叶 Kingman 溯祖的**历史穷举**里算出来
（**精确穷举**，不是 Monte Carlo，也不是重跑 Lean）。

模型：物种树 `((a,b),(c,d))`，根把无根内部边切成 `a`（`{a,b}` 侧）与 `b`（`{c,d}` 侧），
`t = a + b`（溯祖单位）。`{a,b}` 在根以下合并的概率 `1 − e^{−a}`，`{c,d}` 同理 `1 − e^{−b}`；
进入根种群的谱系按 Kingman 溯祖（每步在所有现存谱系里**等概率**挑一对合并）。

抽查与结论：

| 主张 | 方法 | 实测 |
|---|---|---|
| 整体拓扑分布 = `1 − (2/3)e^{−t}` / 各 `(1/3)e^{−t}` | 9 个 `t` × 5 个 `a/t` 的精确穷举 | 最大残差 **2.22e-16** |
| (A1) 两侧都没在根以下合并 ⇒ 三拓扑**等概率** | 条件分布 | **精确** `(1/3, 1/3, 1/3)`（含 `a=b=0` 星形） |
| (A2) 只有一侧成樱桃 ⇒ 拓扑**被逼成** `ab|cd` | 两个方向的穷举 | `{ab|cd: 1.0, 其余: 0}` |
| (A3) `C(4,2)=6` 个首次合并对 → **3 类、每类 2 个** | 枚举首次合并对诱导的拓扑 | `{a,b}/{c,d}`、`{a,c}/{b,d}`、`{a,d}/{b,c}` 各 2 个 |
| 与 `Coalescent.pConcordant` 的代数对账 | `(1−e^{−t}) + (1/3)e^{−t} = 1 − (2/3)e^{−t}` | 残差 **1.11e-16** |

`VERDICT: PASS`。

**(A3) 独立复现了库里的 `Coalescent.root_quartet_classes`** —— 即 ADR2011 Lemma 4
「重标号对称性」在 4 叶下的组合核心；`MSCKingman.AllSameShape` 的证明就取自它。

### 这个脚本本身修过的 4 个实现 bug（记下来免得后人重踩）
1. 无根树的**根结点方向搞反**（`history[-1]` 才是根，不是 `history[0]`）；
2. 让「簇结点」把自己携带的叶集算进**连通分量**的叶集（分量只覆盖该簇的一部分 ⇒ 叶集被算成 4）；
   正解是**按图论叶子（字母结点）**取；
3. `edges` 是集合 ⇒ 每条无向边只试了**一个方向**，另一方向的叶集被漏掉；
4. `topo_of_split(hist)` **漏写 `split_of`**，把「历史」当「split」传进去。

⇒ 教训：**「我的推导通过了数值复核」这句话，只有在我先确认复核脚本自身正确之后才有意义。**

## 运行

```
python kingman_check.py
```

无第三方依赖（只用标准库 `itertools` / `math`）。

---

# W10（溯祖理论本体）的复核脚本 —— **全部 14 个**

> 全部**精确**运算（`fractions.Fraction` / 符号多项式 / 穷举 / `decimal` 高精度），
> **没有 Monte Carlo**，也**不是**重跑 Lean。每个脚本对应一个 Lean 模块，
> 用来在「相信 Lean 里的定理」之前先把它的**数学内容**独立算一遍。
>
> **一键跑全部**：`bash scripts/msc/run_all.sh` —— 它**动态扫描** `*.py`
> （曾经硬编码清单，漏跑了后来新增的 4 个脚本却照样打印「全绿」⇒ **假绿**），
> 判据是「脚本 exit 0」＋「输出里出现 `PASS`/`通过`/`OK`」。

| 脚本 | 对应模块 | 复核什么 | 结果 |
|---|---|---|---|
| `kingman_check.py` | `MSCKingman.lean`（**W9**） | 4 叶 Kingman 溯祖的历史穷举：拓扑分布 `1 − ⅔e^{−t}` / `⅓e^{−t}`（最大残差 `2.22e-16`）、(A1)(A2)(A3) | **PASS** |
| `msc_quartet_prob.py` | `MSCProof.lean`（**W10c**） | ① `Fin 4` 的 14 个有向 split 分类（`2\|2` 恰 6、`1\|3` 恰 8；一致 2、不一致 `2\|2` 4）；② 概率和 `pConc + 2·pDisc ≡ 1`（`x = e^{−t}` 当自由符号，**误差恰 0**）；③ `majorizes` 的严格不等式；④ **测度层**划分 `P(≤t) + P(>t) ≡ 1` 与 `P(≤t)·1 + P(>t)·(1/3) ≡ pConc`（对应 `MSCMeasure`） | **PASS** |
| `coalescent_stats.py` | `CoalescentStats.lean`（**W10k**） | ① `k·E[τ_k] = 2/(k−1)`；② `E[L_n] = 2H_{n−1}`；③ `Σ E[τ_{j+2}]·d_{j+2} = m`；④ `Σ θ/i = θH_{n−1}`；⑤ `θ_W` 无偏（`n ≤ 12`，`Fraction`） | **PASS**（误差恒 0） |
| `kingman_jumpchain.py` | `KingmanJumpChain.lean`（**W10a**） | (2.2) 归一化、层间一致性递归（`n ≤ 7` 共 **1148** 个三元组）、单块分裂恒等式（有序和 `= \|B\|!(\|B\|−1)`）、以及与**新证定理逐条对应**的断言 | **PASS**（`n ≤ 7`） |
| `kingman_coalescent.py` | `KingmanCoalescent.lean`（**W10b**） | (1.7) 密度积分、`E[τ_k] = 1/d_k`、`Σ 1/d_k = 2(1−1/n)`、联合归一化与逐坐标边缘化、**Theorem 1 的定律层**（对任意归一化 pmf 可分离 ⇒ 独立） | **PASS**（21 项） |
| `degnansalter_puv.py` | `DegnanSalter.lean`（**W10e**） | (C0)–(C7)：部分分式系数 vs 闭乘积形式、**独立 Sylvester 谱分解**（含 `Σ_k P_k = I`）、`ODE` 特征关系、`Σ_v p_{uv} = 1`（`300` 位 `Decimal`，`max\|Σ−1\| = 1.0e−299`） | **PASS** |
| `adr2011_identifiability.py` | `Identifiability.lean`（**W10g**） | ADR2011 原式 `t = −log((3/2)(1−p))` 复算（`decimal` **50 位**，最大误差 **1.45e−46**）、无 `log` 形式、51 点网格**无碰撞**、`p(0) = 1/3` | **PASS** |
| `adr2017_split.py` | `SplitProbabilities.lean`（**W10f**） | **零浮点判定**（全 `Fraction`，`exp` 用交错级数做**有理上下界**的严格区间算术）：穷举 `n = 4/5/6` 的全部无根 binary 树（`3/15/105`），每条恰展示 `2n−3` 个互异 split、平凡恰 `n`、非平凡恰 `n−3` | **PASS**（51/51） |
| `zds2011_monophyly.py` | `ReciprocalMonophyly.lean`（**W10h**） | 精确有理数、独立实现 YHK 生成过程，`n ≤ 6` **穷举** `n!·(n−1)!` 条路径；核对 Lemma 4.2/4.3/4.4、Thm 6.3/6.4 的闭形式与论文数值锚点（`q₆(2,2) = 7/225` 等）；**发现 Lemma 4.4 的印刷范围在 `k = n` 时不成立** | **ALL OK** |
| `empirical_convergence.py` | `EmpiricalConvergence.lean`（**W10d**） | **零浮点**（全 `Fraction`）：无偏性逐点恒等、`E[(ΣX)²] = np + n(n−1)p²`、方差**两条独立路线**（双重和 vs `ΣVar + 2ΣCov`）逐字相等、权重和 `(1/n)·n = 1` | **ALL PASS**（195 项） |
| `trivial_split_count.py` | `TrivialSplitCount.lean`（**缺口 G1**） | 「有向 split ↔ 非空真子集」代理上穷举 `n = 2…12`：总数 `2^n − 2`、`\|A\| = 1` 与 `\|Aᶜ\| = 1` 各恰 `n`、`n ≥ 3` 两支不交 ⇒ 平凡恰 `2n`、`n = 4` 的 `1\|3 = 8` 与 `2\|2 = 6` 交叉核对 `MSCProof.card_splits_two` | **PASS** |
| `stadler_degnan_ranked.py` | `RankedGeneTree.lean`（**W10i**） | 式 (2) `H_ℓ = ∏ C(k,2) = ℓ!(ℓ−1)!/2^{ℓ−1}`；穷举 `n = 2..7` 的合并序列数 `1, 3, 18, 180, 2700, 56700`；**穷举证伪任务书的 `(n−1)!` 断言**（`n = 3` 反例）并采信论文 Remark 6；论文自算式 (4) 的实例 | **全部核对通过** |
| `coalescent_history_count.py` | `CoalescentHistoryCount.lean`（**一般 `n` 计数**） | 纯整数穷举：`H_n` 的两个闭形式（`n ≤ 14`）、库内编码的合并史数（`n ≤ 7`）、**任意子集版**在 `N ≤ 6` 的**全部** `2^N` 个子集上成立、递推、与库内 `card_mergeHistories_two/three/four` 对齐 | **全部核对通过** |
| `w10_lemma4_five.py` | `FiveTaxonLemma4.lean`（**ADR2011 Lemma 4**） | 逐字复刻库内编码与 `topoOf`：`H_5 = 180`；`n = 5` 的 **180 条历史 / 15 个无根拓扑 / 每个纤维恰 12 / 每个概率 1/15 / 概率和 1**；`n = 4` 无根纤维全 6（对照**有根** 1/2）；`n = 6` 纤维分布 `{24: 90, 36: 15}` ⇒ **Lemma 4 只对 5 taxa 成立** | **ALL CHECKS PASSED**（47 项） |

## `W10Probe.lean` —— W10 **全批**的**反空真探针**（协调侧自写）

**不是**数值脚本，是**能被 Lean 编译**的探针（**23 个 `example`**）：证明本批的构造与定理
**不是空真** —— 实例可居留、真树 quartet 概率**严格为正**、`1/3` **真的是求和**、
四处采样结构（`MSCSampling` / `USTARSampling` / `CASTERSampling` / `SiteSampling`）
**修正后都有居民**（曾是**空类型**，2026-10-09 已治本）、`emp` **依赖真实律/模型的形状护栏**、
树层谓词 `StatisticallyConsistent` **非自动成立**、
M1 的测度层划分、一般 `n` 的计数、ADR2011 Lemma 4、以及**根部 `1/3` = 跳链质量的等式**。
运行方式（**必须先 build 根模块**，否则 `import Phylo` 读到的是旧 olean）：

```
# 在镜像里（正本不能跑 lake）
cp -r <正本>/Phylo/. <镜像>/Phylo/ && cp <正本>/Phylo.lean <镜像>/
~/w10/withlock.sh <镜像> ~/.elan/bin/lake build Phylo
~/w10/withlock.sh <镜像> ~/.elan/bin/lake env lean scripts/msc/W10Probe.lean
```

实测 **exit 0 / 输出 0 字节**（22/22 通过）。

### 本目录脚本自身踩过的坑（W10）
* **`msc_quartet_prob.py`：f-string 里不能直接写 `{14 ...}`** —— `{` 会被当表达式，需写成 `{{…}}`。
* **数值「复核」必须先自证**：`degnansalter_puv.py` 的 (C7)/(C8) 交叉核对立刻把
  「`p_{uv}` 的公式抄错」暴露出来 —— 这正是「**脚本先跑通再相信定理**」的价值
  （后来 agent 改走 **Sylvester 谱分解**才全 PASS）。
* `kingman_jumpchain.py` 顺带查出**协调侧规格**里的一处算术笔误：
  §1.7 (★) 的 `|B| = 4` 写了 `36`，但那是**无序**和；**有序**和是 `72 = 4!·3`。
* `stadler_degnan_ranked.py` **穷举证伪了派单规格 §11.3 举的例子**「给定拓扑的 ranked 树数 `= (n−1)!`」
  （`n = 3` 即反例），并改用论文 **Remark 6** 的 `(n−1)!/∏(c_i−1)`。
* `trivial_split_count.py` 第一版把 `n = 4` 的 `1|3` 数成「`|A| = 1`」（4 个）而漏了
  `|Aᶜ| = 1`（另 4 个）—— 被脚本自己的 (E) 交叉核对当场抓住（`4 ≠ 8`）。
  教训：**「有向口径下平凡 = 某一侧单点」必须两侧都数**。
* **判据的措辞是坑**：`run_all.sh` **三次**漏判（`VERDICT: ALL PASS` / `总判定： ALL OK` /
  `ALL CHECKS PASSED`）⇒ 最终改成**正向白名单 `PASS|通过|OK`**；
  **教训：不要枚举各家措辞，要么放宽，要么统一格式。**

---

# W11a（有根三元组 · Aho 有根版 / F7）的复核脚本

| 脚本 | 对应模块 | 复核什么 | 结果 |
|---|---|---|---|
| `rooted_triplet_aho.py` | `Phylo/RootedTriplet.lean`（**§5 §6**） | (A) 递归划分枚举 `L` 上全部**有根树**（规范形 = 非根子树叶集集合），计数命中 **A000311** `1,1,4,26,236,2752`（`n ≤ 6`）——先自证； (A2) 三叶**至多**三选一（非二叉树上不成立「恰一」）； (B) **可展示 ⟺ `AhoOK`** 穷举：`n=3` 全部 8 族 / `n=4` 全部 4096 族 / `n=5` 全部 `\|R\| ≤ 4`（31931 族）/ `n=6` 全部 `\|R\| ≤ 2` + 3000 随机； (C) **★B 反例**：`n=4` 全部 4096 族里「两两相容但不一致」的有 **122** 族、最小基数 **3**、最小反例 **56** 个，含 Lean 的 `fourLeafCounterexample = {01\|2, 02\|3, 03\|1}`； (D) 同一三叶集上的不同三元组**互不相容**（故 `{ab\|c, ac\|b, bc\|a}` **不**两两相容）； (E) 展示 ⟹ 两两相容（800 抽查 0 例外）； (F) Bryant–Steel **Theorem 2 的 (⟹)** 的数值旁证（281 个 `(树, S)` 组合，`\|S\| ≥ 3` 时 `[R,S]` 恒不连通 —— 这正是 Lean 里**未证**的缺口 1） | **VERDICT: PASS**（19 项） |

**这个脚本自己踩到的坑（记下来免得后人重踩）**：
* 第一版 (A2) 断言「每棵树在给定 3 叶上**恰**展示 1 个三元组」——被 **401 个反例**当场打回。
  正解：**至多 1 个**。**非二叉**树（例：三叶星形 `(a,b,c)`，没有内部边）展示 **0** 个，
  所以「恰一」只对**二叉**树成立。这条现在固化成了 (A2) 的显式断言。
* 一致性 / 两两相容的判定必须**先重标号**（树枚举器按**叶数**索引，与叶标签无关）；
  第一版直接把 `{1,2,3}` 的叶集喂给 `n = 3` 的树表 ⇒ 标签错位。

运行方式（纯标准库，`python3 rooted_triplet_aho.py`，`n = 6` 全跑约 1 分钟）。

---

# W13（把「位点分布 = MSC 理论分布」假设升级为**定理**）的复核脚本 —— **13 个**

背景：W13 用老师给的三步显式生成模型，把库内两条端到端 a.e. 一致性定理所挂的
「位点分布 ＝ MSC 理论分布」假设**双双升级为定理** —— ASTRAL 侧 `hmean`
（`Phylo/Stat/GeneTreeSamplingAE.lean`）与 CASTER 侧 `hconv`
（`Phylo/Stat/BlockModelAE.lean`）。本目录的脚本为**每一步**提供独立数值背书。

| 脚本 | 对应声明／模块 | 复核什么 | 结果 |
|---|---|---|---|
| `W13aSiteWeightCheck.py` | `SiteWeightMeasurable.lean`（**W13a**） | 位点权重函数的**可测性（B2）＋ 有界性（B3）**（含**阴性对照**：负枝长时有界性确实会失效） | **PASS** |
| `W13b_rate_mixture_check.py` | `SiteRateMixture.lean`（**W13b+c**） | `Ã` 的定义性恒等式 · **命题 A/B 在 `Ã` 下保持** · 混合可交换 · 退化一致性 · **箱体一致下界** · 并实测「`fbar_pos` 需内枝长 > 0，无限制的一致下界为**假**」 | **VERDICT: PASS** |
| `w13_coord_f84_audit.py` | `CASTERF84Pos.lean`（**W13h**） | **协调侧自写实现**的独立审计：`lamF84_pos`／`f84Amp_pos`（20 万随机 ＋ 5 万逼近退化样本，无反例）＋ JC69 退化点 `lamF84 = 4/3` 逐字吻合 | **VERDICT: PASS** |
| `W13e_endtoend_check.py` | `CASTERRateAE.lean`（**W13e**） | 端到端装配（`abarPropAData → TopoIdeal.ofModel` ＋ 与块级 SLLN 的组合）＋ **退化一致性** | **ALL CHECKS PASSED** |
| `w13f_fixed_k_check.py` | `ToyMSCFin4.lean`（**W13f**） | ★ **规格 §4.1「`k` 固定 ⇒ 结论假」的机制**：`k = 1` 时在正测度事件上极限 `= freqA ≠ m.freq`（**差 1/10**），`k → ∞` 才收敛 | 机制数值确认 ✓ |
| `w13g_gap_check.py` | `GeneTreeSamplingAE.lean`（**W13g ⭐**） | 缺口 G2 ／ 基因树层：任意常数表 `C` 上 `(1/k)·Σ_(j<k) C = C`（`k = 1..5` 逐点）＋ 规格 §4.1 同族反例 | **全部断言通过** |
| `w13h_f84_positivity_audit.py` | `CASTERF84Pos.lean`（**W13h**） | F84 正性链 `lamF84_pos`／`f84Amp_pos`；JC69 退化点吻合；并说明**为何「π 正下界」是必需**（分母的**一致**下界） | **AUDIT PASSED** |
| `w13i_coeff_check.py` | `GeneTreeHmeasDischarge.lean`（**W13i**） | `siteCoeff` 的**单位分解** ＋ ★ **证伪**「`1/4 = p(1−p)/n`」（**仅 `n = 1` 成立** ⇒ 原命题为假） | **ALL CHECKS PASSED** |
| `W13j_index_shift_check.py` | `BlockSLLNIndex.lean`（**W13j**） | 规格 **§3.3 换指标**（`n = 7999`：块平均 = 前缀平均，**差 0**）＋ ★ **`L_j ≤ C` 的必要性**（块长无界 ⇒ 前缀平均在 `0` 与 `1/3` 振荡） | **全部通过** |
| `w13_coord_kmat_audit.py` | `CASTERF84.lean`／`KmatNonneg.lean` | **协调侧自写实现**的独立审计：`Kmat ≥ 0`（JC69 退化点失配 0；并给出三个**反例**值 `−0.429570`／`−3.352558`） | **AUDIT PASSED** |
| `w13k_blockmodel_check.py` | `BlockModelAE.lean`（**W13k**） | **块概率空间**：6 类检查共 **1784 条断言**（`sum_ite_lt_card`／`blockW_eq_sum_filter`／`rateMeasure` 归一与积分／`blockMeasure` 边缘律与 iid 配对／退化点），**全部 `Fraction` 精确有理数** | **ALL CHECKS PASSED** |
| `w13l_split_kmat_check.py` | `SplitFin4Count.lean`／`KmatNonneg.lean`（**W13l**） | `Fintype.card (Split (Fin 4)) = 14 = 6 + 8` **穷举** ＋ `Kmat` 网格 **4096 格** `0 ≤ Kmat ≤ 1` ＋ 3 反例 ＋ 2 退化点 | **VERDICT: PASS** |
| `W13m_no_L1_check.py` | `BlockSLLNNoL1.lean`（**W13m**） | 零假设取商恒等式（**20 万次**随机，含 75763 个 `ΣL = 0` 样本）＋ ★ **`∫L₀ ≠ 0` 不能再瘦**的反例（`{±1}` 一维随机游走） | **汇总：8/8 通过** |

**两个追加脚本**（不是 W13 规格要求，是协调侧补的）：

| 脚本 | 补什么 | 结果 |
|---|---|---|
| `W13_astral_msc_convergence_check.py` | ★★ **ASTRAL 主线的独立端到端数值背书**：真的按 **MSC 采基因树**（内枝 `T ~ Exp(1)`），验**经验** quartet 频率收敛到 `Coalescent.pConcordant`（`Phylo/Stat/Coalescent.lean:374`／`:382`，**与脚本公式逐字对应**）；并验理论式与独立推导一致 ＋ 退化极限 | **VERDICT: PASS**<br>（`t=0.1, k=10⁴`：`emp_conc = 0.396600` vs 理论 `0.396775`，**Δ = 1.75e-4**） |
| `w11h_x9_pic_root_check.py` | ★ 给 W11h「**未定根 ⇒ PIC 对比量集合依赖根**」补数值背书（原 `w11h_x9_pic.py` **从未跑完过**，见下"已知红"）：6 种根 × 16 叶对 = **96 组合**根不变性 ＋ **6 种不同**姊妹对集合 | **VERDICT: PASS** |
| `W15a_box_prior_check.py` | ★★ 给 **W15a（`Phylo/Stat/CASTERRateBoxAE.lean`，★ 超出规格）** 做数值背书：逐字重实现库内 JC69 链，验**箱体上 `max\|geneScore\|`/`max\|Ã\|`/`max\|f̃\|`/`max\|hint\|` 全部 `≤ 1`**（实测 0.2267 / 0.1203 / 0.1345 / 0.1203）＋ 把重实现**钉在库内定理上**（`max\|Σ_σ patternProb − 1\| = 2.2e−16`；`clause_*` 恒等式 `4.2e−17`）＋ **反空洞**（箱体**外** `max\|geneScore\| = 5.27e11` ⇒ 「枝长非负」前提**必需**，即 `CASTERRateAE:64` 那句"爆炸"的数值复核） | 未注入 **`exit 0` ＋ `VERDICT: PASS`**<br>**`--inject` ⇒ `exit 1` ＋ `FAIL`**（`max\|hint\| = 1.33e12 > 1`）<br>**`--inject=amplify` ⇒ `exit 1` ＋ `FAIL`**（`max\|fbar\| = 1.075739 > 1`）⇒ **能为假** ✓ |

> ★ 与之配套的 Lean 模块是 **`Phylo/Stat/CASTERRateBoxAE.lean`（710 行 / 34 定理 / 37 条声明）**：
> **箱体先验 ⇒ `Ã` 有界（上界恰为 1）⇒ `Integrable`**，从而把
> `hf_int` / `hint` / `hlx` / `hdeep` / `hf_pos` / **`hpos`** **全部证掉**，
> 并给出与 Dirac 端点**同形**的端到端变体 `abar_caster_statisticallyConsistent_kingman_ae_box`
> （物种树侧假设面**只剩箱体先验**；`leaf`/`a`/`b`/`hab` 全部消失）＋ **`…_via_box_dirac`**（Dirac 是其机器验证特例）。
> ⚠️ **本件超出 W13 规格**（规格 §1.2 把物种树取为**固定** ⇒ Dirac 情形**已满足规格**），属**库内一般性的加强**，**可叫停**。

## ★ 本目录脚本的**判据纪律**（2026-10-12 起）

`run_all.sh` 的判据是「**`exit 0`** 」＋「输出里出现 `PASS`/`通过`/`OK`」（见上文）。
为让这个"绿"**携带信息**，本目录脚本遵守三条（均有**失败注入自测**佐证）：

1. **必须有真正的判据**，并且**判据为假时退出码真的会变**（★ 反例：只有 `print('FAIL')` 而恒 `exit 0`
   —— 失败只存在于 stdout，任何看退出码的消费者都看不见）；
2. **判据要能抓真错、又不许对正确实现假红**（例：收敛判据用**有原理的界** `3/√k`，
   而不是"末档偏差必须小于首档"这种会被小样本幸运值破坏的规则）；
3. **注入自测**：注入一处错误 ⇒ 非零退出 ＋ 打印 `FAIL`；未注入 ⇒ `exit 0` ＋ `PASS`。

## ⚠️ 已知红（`run_all.sh` 当前仍有 **3** 个，均**已定性**、**不是**本目录脚本的回归）

| 脚本 | 状态 | 说明 |
|---|---|---|
| `w12g_fin5_instance_gen.py` | **结构性例外**（**不是检查**） | 它是**生成器/打补丁工具**（成功 = 往 `Phylo/Algorithm/NeighborNet.lean` 追加 §9.4/§9.5），**没有可判定断言** ⇒ 跑过也证明不了任何东西。它**先查哨兵**（`'### 9.4' in src`）⇒ 幂等；且从 `run_all.sh` 的 cwd（`scripts/msc`）跑会在**读**文件时 `FileNotFoundError`（在写之前就失败 ⇒ 无害）。**建议移到 `scripts/tools/`**（需老师定）。 |
| `w12g_fin5_nni_gen.py` | 同上 | 同因（目标 `Phylo/Algorithm/NNINeighborhood.lean` 的 §8）。 |
| `w11h_x9_pic.py` | **真红灯** | 它**有**失败路径也有判定词，红是因为**判据真的为假**：4 条 `[FAIL]` 后崩在 `root_at_node` 的 `assert len(ch) == 2`（它自己的错误信息写着「**除根外**内部顶点度应为 3」，但代码把**根**也算进去了 ⇒ 6 种根**全部**触发 ⇒ 该脚本**从未跑完过**）。它要背书的结论已由 **`w11h_x9_pic_root_check.py`** 补上（见上表）；本脚本**未修**（需把树表示扩到"多子根"，属结构性改动）。 |

> ★ 除上述 3 个外，`run_all.sh` 的**其余脚本**（含 W13 的 13 个 ＋ 两个追加脚本）**都能为假且都会自报** ✓。

## ★ 给后来者：本目录与「数值背书」的协作约定（2026-10-12 立）

1. **判据三律**（见上文"判据纪律"）：判据要**接到退出码**；要**能抓真错、又不许对正确实现假红**；必须附**失败注入自测** ✓。
2. **数字纪律**：凡**可机械核对**的数字（脚本数/模块数/job 数/红数），**写完立刻用命令核** ✓；
   ★ 引用**别人报告**里的数字时，**要么自己复测、要么标注来源** ✓ —— **"我跑过那个脚本"只证明它通过，不证明它打印的数值** ✗。
3. **可见性纪律**：**后人需要知道的**（约定 · 判据纪律 · 已知红 · 脚本↔声明的对应）**必须写进本 README** ✓ ——
   因为仓库里的 `HANDOVER.md` / `MEMORY.md` **都在 `.gitignore` 里** ✗，clone 之后**看不到** ✓。
4. **"全部/所有 X"的说法**：X 的名单**用命令生成**（例：`git diff --diff-filter=A <基线>..HEAD -- '*.lean'` ✓），
   并做**数量校验**（`基线 + A − D = HEAD` ✓）—— 别用手写清单 ✗（本季在此栽过一次：把 15 个模块写成 14 个 ✗）。
5. **诚实边界**：与规格原文逐条对照后再写（避免把"规格如此"误报成"我没做到"✓）；
   ★ 也避免把**过强的前提**写进文档（本季实例：`Integrable` 其实**只需叶长非负**，不需要上界 ✗）✓。
