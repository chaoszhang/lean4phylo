# lean4phylo

计算系统发生学（computational phylogenetics）经典算法的形式化库 —— 用 **Lean 4 + Mathlib**
建立**可机器检验**的证明。

> 名字双关：**Lean 4** phylo ／ **lean for** phylo。

## 目标

把系统发生学的经典定义与算法（树 · 分裂系统 · quartet · 树度量 · 建树算法 · 统计一致性）
形式化进 Lean 4，目标是**一个可长期积累的算法正确性库** —— 不是单个大定理，而是
「每个经典算法的正确性都有机器检验的证明」。

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

## 快速开始

```bash
lake exe cache get    # 首次必需：下载 Mathlib 预编译缓存（否则要编译数小时）
lake build
```

五条复跑命令（都只依赖仓库内脚本）：

| 想核什么 | 命令 |
|---|---|
| 规模（模块 / 行 / 声明 / job 数） | `bash scripts/measure.sh` |
| 缺口台账与七桶 | `bash scripts/list_gaps.sh` |
| 「空转缺口」的机械依据 | `bash scripts/check_vacuous.sh` |
| 「已证伪缺口」的源码层标记 | `bash scripts/check_refuted.sh` |
| **依赖版本锁是否一致** | `bash scripts/check_pins.sh` |

### 版本锁定（可复现性）

| 锁在哪 | 值 | 谁动 |
|---|---|---|
| `lean-toolchain` | `leanprover/lean4:v4.35.0`（**已发布稳定版**） | 换编译器才改 |
| `lakefile.toml`（mathlib `rev`） | **`v4.35.0`**（tag，与 toolchain 严格配对；**不是** `master`） | 升级 mathlib 才改 |
| `lake-manifest.json`（mathlib `rev`） | `56a005855ea1…`（= `v4.35.0` 的解析结果，须与 toolchain 的 tag 对应） | 由 `lake update` 生成，改了就一起提交 |

⇒ 三者一致由 `bash scripts/check_pins.sh` 机器检查（CI 里也跑）。**不要**在不改 `lakefile.toml` 的情况下单独跑
`lake update` —— 那会让 manifest 漂到一个 lakefile 没声明过的 commit。

## 已形式化的内容

全部**零 `sorry` / 零 `axiom` / 零 `opaque`**：尚未形式化处一律写成显式 `def … : Prop` 缺口，
依赖关系清晰可审计（见下「缺口台账」）。

### 基础层：树 · 分裂 · quartet

| 内容 | 主定理 | 文件 |
|---|---|---|
| 树的载体（cladogram）与基础引理 | `Cladogram` / `IsBinary` / 度数与叶数关系 | `Phylo/Core.lean` |
| 分裂系统与相容性 | **Splits-Equivalence 两个方向**：树 ⟹ 两两相容；相容 ⟹ 存在树 | `Phylo/Split.lean`、`Phylo/Laminar.lean` |
| Aho–Buneman 建树 | 相容的分裂系统 ⟹ 存在展示它的树 | `Phylo/Aho.lean` |
| 镶嵌族（laminar）与规范簇字典 | `toCladogram` / `toRootedTreeOfCard` / `splitOf` | `Phylo/Laminar.lean` |
| quartet / triplet 与推理规则 | `Topology` · `display` · Colonius–Schultze 推理规则 | `Phylo/Quartet.lean` |
| 二叉树 quartet 唯一性 | 4-元集上 quartet 唯一（模 swap）⟹ `q_T` 良定义 | `Phylo/QuartetUnique.lean` |
| 不兼容分裂的见证 | 不兼容 ⟹ 同一 4-叶集上两个不同 quartet | `Phylo/Binary.lean` |
| 内部边两侧叶数 | 内部边的侧分量子树是树；两侧各 ≥ 2 叶 | `Phylo/SideSubtree.lean`、`Phylo/InternalEdge.lean` |

### 建树算法与树比较

| 算法 / 工具 | 主定理 | 文件 |
|---|---|---|
| **Aho–Buneman** | 相容 ⟹ 存在树 | `Phylo/Aho.lean` |
| **多数共识树**（Margush–McMorris） | 多数分裂两两相容 ⟹ 共识树存在 | `Phylo/Consensus.lean` |
| **UPGMA**（分子钟） | 超度量 ⟹ 球族镶嵌 ⟹ 存在展示全部球的树 | `Phylo/Dendrogram.lean` |
| **cherry 存在性** | 每棵树都有 cherry（纯组合计数，不用距离） | `Phylo/Algorithm/Cherry.lean` |
| **RF 距离** | 对称 + 三角不等式 | `Phylo/Algorithm/RF.lean` |
| **二叉树计数** | ℓ = i + 2、\|V\| = 2ℓ−2、\|E\| = 2ℓ−3 | `Phylo/Algorithm/BinaryCount.lean` |
| **NNI** | NNI 分解与母分裂的相容性 | `Phylo/Algorithm/NNI.lean` |
| **NJ**（邻接法） | 代数层全证（`Q_eq_neg_two_ell` / `two_mul_z` / `z_hinge` / `four_point_z_iff`） | `Phylo/Algorithm/NJ.lean` |

### 统计一致性层（多物种溯祖 MSC）

| 算法 | 主定理 | 文件 |
|---|---|---|
| **ASTRAL** | 真树得分唯一最大 ＋ 统计一致性 | `Phylo/Stat/ASTRAL.lean`、`Stability.lean` |
| **CASTER** | **定理 1（三模型，端到端）**：`lm1/jc69/f84_caster_statisticallyConsistent` ⟹ **逐 quartet 统计一致性**。⚠️ CASTER **不是**「归约到 ASTRAL」 | `CASTERTheorem1.lean`、`CASTERInstances.lean` |
| **parsimony**（ISM） | `Pattern.fitchCost_eq`（48 情形枚举）⟹ 统计一致性 | `Phylo/Stat/Parsimony.lean` |
| **SVDQuartets** | 秩判据 + 分离性 ⟹ 无条件正确性 | `Phylo/Stat/SVDQuartets.lean` |
| **NJst** | 第一步正确（`njst_cherry`） | `Phylo/Stat/NJst.lean` |
| **MSC 公理化** | `MSCFreq` / `MSCSampling` | `Phylo/Stat/MSC.lean` |
| **一致性引擎** | 理想一致性 → gap 引理 → 稳定性（扰动 < δ/(2N+1)） | `Phylo/Stat/Stability.lean` |

> **诚实的边界**：ASTRAL / CASTER / parsimony 的「逐 quartet 一致」已证完；
> 由「逐 quartet 一致」升到「**树同构**」的那一步也已**无条件收口** ——
> 共享引理 `QuartetDecidesTree` 是**定理**（`Phylo/Stat/QuartetDecides.lean:330`），
> 故 `astral_iso` 与 `multiLocus_iso` **不再带 `hQD` 缺口假设**。
> 仍受限的是**概率层**：`MSCFreq.majorizes` 与 `MSCSampling.converges` 是结构字段（公理化）。

### 三条已发表定理（原文级对齐）

| 文献 | 内容 | 落点 |
|---|---|---|
| **Bandelt & Dress 1992** Thm 2 | 典范 split 分解（存在性） | `BunemanIndexBridge.lean`（`canonicalSplitDecomposition_gap_holds`） |
| **Bandelt & Dress 1992** Thm 3 | d-splits 集 = 𝒮 **且** `α_S = λ_S`（两条断言都在账上） | 同上 ＋ `BunemanIndexQuartet.lean` |
| **Zhu–Degnan–Steel 2011** Thm 6.3 | clades / clans 概率 (i)(ii) | `RankedTreeClanLaw.lean`、`ClanPairLaw.lean` |

## 规模

★ 下表为 **`2026-10-28` 实测值**，复跑：`bash scripts/measure.sh`（口径与本表逐字一致 —— 剥注释后统计）。
★ **`lake build` 的 job 数随 Mathlib 版本变**（它含依赖图里的全部目标）：Mathlib `master` 时代是 3988，
换到 `v4.35.0` 后是 **4007** —— 所以 job 数只能与同一份 `lake-manifest.json` 下的数字比。

| 指标 | 值（`2026-10-28` 实测） |
|---|---|
| Lean 模块 | **156**（`Phylo/**` 的 `.lean` 文件数 **恒等于** `Phylo.lean` 的 `import Phylo` 条数） |
| Lean 源行数 | **105,372**（`Phylo/**/*.lean`） |
| 顶层声明 | **6,494**（剥注释后机械统计） |
| `sorry` / `axiom` / `opaque` | **0 / 0 / 0** |
| `lake build` | **通过（4007 jobs）** |
| 缺口台账（七桶） | 真开放 **1** · 已收口 38 · 条件收口 2 · 已证伪 17 · 追溯 6 · 判定收档 7 · 长期开放 1 ＝ **72** |

## 缺口台账：七桶怎么读

`scripts/list_gaps.sh` 把全部 **72** 条缺口登记（`def … : Prop`）按**状态**分七桶；
判据写死在 `scripts/gap_ledger.py` 里，并逐条打印收口定理的**完整签名**供人工核「有没有吃假设」。

| 桶 | 条数 | 含义 |
|---|---|---|
| **真开放** | **1** | 既无收口定理、又无机器反例 ⇒ **唯一**还需要做数学的桶（`atteson_lemma11_gap_quantitative`） |
| **已收口** | 38 | 存在**无条件、无特化**的收口定理（多吃一个显式假设就降入「条件收口」） |
| 条件收口 | 2 | 收口定理多吃了 `def` 里没有的假设，或把 `def` 特化到了具体集合实例 |
| **已证伪** | 17 | 存在**机器反例**定理：陈述本身是假命题（结论已定，不是欠账） |
| 追溯 | 6 | 名字以 `_legacy` 结尾：旧形态留痕，已有取代它的正名 |
| 判定收档 | 7 | 白名单 `ARCHIVED_JUDGED`：**无可证内容**（登记形态恒真 / 裁定不再作为待证条目） |
| 长期开放 | 1 | 白名单 `LONGTERM_OPEN`：有可证内容但**裁定不证**（Conjecture 类，不进派单） |

### 「已证伪」为什么不算「未闭合」

「已证伪」= 先把它写成 `def … : Prop`，再证出**它是假命题**（机器反例定理）。
**它已经有结论了**（`¬ gap` 就是定理），不是「还欠一个证明」。

⚠️ 但**读者风险是真的**：`grep gap` 会把假命题与待证目标混在一起。所以读这个库时，
**先看 `bash scripts/list_gaps.sh B` 给出的桶位，再读源码**。源码层也已处置：这 17 条 `def` 的 docstring
**首行**都带 `⚠️ **已证伪，非待证目标** —— 机器反例见 <定理名>（<文件>:<行>）`，
由 `bash scripts/check_refuted.sh` 机器核（缺标记、或标记点名的定理与实际反例不符，即非零退出）。

### 「空转」6 条：已登记、有机械依据

`scripts/check_vacuous.sh` 对 6 条「`∃` 自由槽」缺口给出**可复跑的定理依据**，并覆盖全部 44 条登记
（每条归入「有实例 / 自由槽 / 无实例」三类之一，无「未归类」才通过）。判定必须**可复跑**，不许口头声明。

这 6 条中 **5 条已于 2026-10-28 从「已收口」降入「判定收档」**（老师裁定）—— 它们的登记形态**恒真**，
`_vacuous_holds` 就是它的机器证据；留在「已收口」会让人误以为文献结论在库内。
**降级不删任何东西**：那 5 条定理仍全部保留、名字一字未改。

### 严格口径

去掉空转之后：**严格口径 = 38 / 72**（38 条「已收口」里已无空转）。
本库对外声称的是「**72 条登记状态全部判定清楚**」，**不是**「72 条都证成了」—— 两者差别以本表为准。

## 收录纪律（本仓库里到底有什么）

**跟踪**：`Phylo/**` 与 `Phylo.lean`（项目成果）· `scripts/**`（护栏与度量脚本）· `README.md` ·
`lakefile.toml` · `lake-manifest.json` · `lean-toolchain` · `.github/workflows/`。

**不跟踪**（`.gitignore`）：交接与工作日志（`HANDOVER.md`、`MEMORY.md` 等）、临时脚本、`.lake/`。
过程性文档（review / audit / 派单）不进仓库 —— 只有**可长期维护的成果与可复跑的护栏**进来。
