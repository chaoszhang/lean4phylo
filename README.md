# lean4phylo

计算系统发生学（computational phylogenetics）经典算法的形式化库 —— 用 **Lean 4 + Mathlib**
建立**可机器检验**的证明。

> 名字双关：**Lean 4** phylo ／ **lean for** phylo。

## 目标

把系统发生学的经典定义与算法（树 · 分裂系统 · quartet · 树度量 · 建树算法 · 统计一致性）
形式化进 Lean 4，目标是**一个可长期积累的算法正确性库** —— 不是单个大定理，而是
「每个经典算法的正确性都有机器检验的证明」。

## 已形式化的内容

全部**零 `sorry`**：尚未形式化处一律写成显式 `def … : Prop` 缺口，依赖关系清晰可审计。

### 基础层：树 · 分裂 · quartet

| 内容 | 主定理 | 文件 |
|---|---|---|
| 树的载体（cladogram）与基础引理 | `Cladogram` / `IsBinary` / 度数与叶数关系 | `Phylo/Core.lean` |
| 分裂系统与相容性 | **Splits-Equivalence 两个方向**：树 ⟹ 两两相容（`pairwiseCompatible`）；相容 ⟹ 存在树 | `Phylo/Split.lean`、`Phylo/Laminar.lean` |
| Aho–Buneman 建树 | **相容的分裂系统 ⟹ 存在展示它的树**（`compatible_exists_rootedTree`） | `Phylo/Aho.lean` |
| 镶嵌族（laminar）与规范簇字典 | `toCladogram` / `toRootedTreeOfCard` / `splitOf` | `Phylo/Laminar.lean` |
| quartet / triplet 与推理规则 | `Topology` · `display` · Colonius–Schultze 推理规则 | `Phylo/Quartet.lean` |
| 二叉树 quartet 唯一性 | 4-元集上 quartet 唯一（模 swap）⟹ `q_T` 良定义 | `Phylo/QuartetUnique.lean` |
| 不兼容分裂的见证 | 不兼容 ⟹ 同一 4-叶集上两个不同 quartet | `Phylo/Binary.lean` |
| 内部边两侧叶数 | 内部边的侧分量子树是树；两侧各 ≥ 2 叶 | `Phylo/SideSubtree.lean`、`Phylo/InternalEdge.lean` |

### 建树算法与树比较

| 算法 / 工具 | 主定理 | 文件 |
|---|---|---|
| **Aho–Buneman** | 相容 ⟹ 存在树（见上） | `Phylo/Aho.lean` |
| **多数共识树**（Margush–McMorris） | 多数分裂两两相容 ⟹ 共识树存在 | `Phylo/Consensus.lean` |
| **UPGMA**（分子钟） | 超度量 ⟹ 球族镶嵌 ⟹ 存在展示全部球的树 | `Phylo/Dendrogram.lean` |
| **cherry 存在性** | 每棵树都有 cherry（纯组合计数，不用距离） | `Phylo/Algorithm/Cherry.lean` |
| **RF 距离** | 对称 + 三角不等式 | `Phylo/Algorithm/RF.lean` |
| **二叉树计数** | ℓ = i + 2、\|V\| = 2ℓ−2、\|E\| = 2ℓ−3 | `Phylo/Algorithm/BinaryCount.lean` |
| **NNI** | NNI 分解与母分裂的相容性 | `Phylo/Algorithm/NNI.lean` |
| **NJ**（邻接法） | 代数层全证（`Q_eq_neg_two_ell` / `two_mul_z` / `z_hinge` / `four_point_z_iff`）；樱桃引理模显式假设 `MaxZCherryCore` | `Phylo/Algorithm/NJ.lean` |

### 统计一致性层（多物种溯祖 MSC）

| 算法 | 主定理 | 文件 |
|---|---|---|
| **ASTRAL** | 真树得分唯一最大（`astralScore_le` / `_eq_iff` / `astral_maximizer_agrees`）+ **统计一致性** | `Phylo/Stat/ASTRAL.lean`、`Phylo/Stat/Stability.lean` |
| **CASTER** | `casterScore_eq`（归约到 ASTRAL）⟹ **统计一致性** | `Phylo/Stat/CASTER.lean` |
| **parsimony**（ISM） | `Pattern.fitchCost_eq`（48 情形枚举）⟹ **统计一致性** | `Phylo/Stat/Parsimony.lean` |
| **SVDQuartets** | 秩判据 `svdquartets_selects_true` + 分离性 ⟹ **无条件正确性** `svdquartets_concrete` | `Phylo/Stat/SVDQuartets.lean` |
| **NJst** | 第一步正确（`njst_cherry`） | `Phylo/Stat/NJst.lean` |
| **MSC 公理化** | `MSCFreq`（真树 + 选择 + 频率 + `majorizes`）、`MSCSampling`（`emp` 依赖真实律，含 `mscSampling_nonempty`） | `Phylo/Stat/MSC.lean` |
| **一致性引擎** | 理想一致性 → gap 引理 → 稳定性（扰动 < δ/(2N+1)） | `Phylo/Stat/Stability.lean` |

> **诚实的边界**：ASTRAL / CASTER / parsimony 的「逐 quartet 一致」已证完，
> 升到「同构」需一条共享引理 `QuartetDecidesTree`（`Phylo/Stat/QuartetDecides.lean`）。
> 该定理是 Colonius–Schultze (1981) / Steel (1992) 的**经典结果**，属**形式化工程量**而非数学未解。
> NJ / NJst 卡在 `MaxZCherryCore`（NJ 樱桃引理，同为经典定理的形式化缺口）。

## 结构

```
Phylo.lean              根模块（按字母序 import 全部子模块）
Phylo/
├── Core.lean           树载体 cladogram 与基础引理
├── Split.lean          分裂系统 · 相容性
├── Laminar.lean        镶嵌族 · toCladogram · toRootedTreeOfCard · splitOf
├── Aho.lean            相容 ⟹ 存在树
├── Consensus.lean      多数共识树
├── Dendrogram.lean     超度量 ⟹ 树（UPGMA 结构定理）
├── Binary.lean         不兼容分裂的见证 · binary 树
├── Quartet.lean        quartet / triplet · 推理规则
├── QuartetUnique.lean  二叉树 quartet 唯一性
├── SideSubtree.lean    侧分量子树
├── InternalEdge.lean   内部边两侧叶数
├── Distance.lean       距离与四点条件
├── Algorithm/          Cherry · NJ · NNI · RF · UPGMA · BinaryCount
├── Stat/               ASTRAL · CASTER · MSC · NJst · Parsimony
│                       QuartetDecides · SVDQuartets · Stability
└── Mathlib/            Mathlib 尚未提供、本库自建的声明（便于将来回灌）
```

## 规模

| 指标 | 值 |
|---|---|
| Lean 源文件 | 27 个（约 7200 行） |
| 顶层声明 | 401 个 |
| `sorry` | **0**（未形式化处落成显式 `def … : Prop` 缺口） |
| `lake build` | 通过（3187 jobs） |

## 快速开始

```bash
lake exe cache get    # 下载 Mathlib 预编译缓存（首次必需；否则要编译数小时）
lake build
```

在 VS Code 中打开**目录**（不是单个文件）以获得完整补全。

## 说明

- 本仓库只收录**项目成果**：证明代码、本文件、LICENSE。
- 设计与工作记录类文档（概念设计、工作日志、任务交接等，含参考文献汇编）
  在本仓库**之外**维护，故不在 GitHub 上。
