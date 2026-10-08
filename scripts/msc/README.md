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

**不是**数值脚本，是**能被 Lean 编译**的探针（**22 个 `example`**）：证明本批的构造与定理
**不是空真** —— 实例可居留、真树 quartet 概率**严格为正**、`1/3` **真的是求和**、
`MSCSampling (Fin 4)` **真的是空类型**（空洞性发现的**回归护栏**）、四处修正版**真的有居民**、
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
