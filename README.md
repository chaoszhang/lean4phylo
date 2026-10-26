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
| **CASTER** | **定理 1（三模型，端到端）**：`lm1_caster_statisticallyConsistent` / `jc69_caster_statisticallyConsistent` / `f84_caster_statisticallyConsistent`（后者三条核恒等式已不再作为假设）⟹ **逐 quartet 统计一致性**；升到树层用 `iso_of_quartets_true`。⚠️ CASTER **不是**「归约到 ASTRAL」（那是多标记 ASTRAL，见 `MultiLocusASTRAL.lean`），残差假设逐条显式：`hdeep` / `hpos` / `hf_int` / `hf_pos` / `hint`（正文条件 (2)）/ `hconv`（大数定律） | `Phylo/Stat/CASTERTheorem1.lean`、`Phylo/Stat/CASTERInstances.lean`（jc69 见 `CASTERGeneTree.lean`，f84 见 `CASTERF84PropA.lean`） |
| **parsimony**（ISM） | `Pattern.fitchCost_eq`（48 情形枚举）⟹ **统计一致性** | `Phylo/Stat/Parsimony.lean` |
| **SVDQuartets** | 秩判据 `svdquartets_selects_true` + 分离性 ⟹ **无条件正确性** `svdquartets_concrete` | `Phylo/Stat/SVDQuartets.lean` |
| **NJst** | 第一步正确（`njst_cherry`） | `Phylo/Stat/NJst.lean` |
| **MSC 公理化** | `MSCFreq`（真树 + 选择 + 频率 + `majorizes`）、`MSCSampling`（`emp` 依赖真实律，含 `mscSampling_nonempty`） | `Phylo/Stat/MSC.lean` |
| **一致性引擎** | 理想一致性 → gap 引理 → 稳定性（扰动 < δ/(2N+1)） | `Phylo/Stat/Stability.lean` |

> **诚实的边界**：ASTRAL / CASTER / parsimony 的「逐 quartet 一致」已证完；
> 由「逐 quartet 一致」升到「**树同构**」的那一步也已**无条件收口** ——
> 共享引理 `QuartetDecidesTree` 是**定理**（`Phylo/Stat/QuartetDecides.lean:330`；
> Colonius–Schultze (1981) / Steel (1992) 的经典结果，2026-10-08 由 `def` 变定理），
> 故 `astral_iso`（同文件 `:348`）与 `multiLocus_iso`（`:357`）**不再带 `hQD` 缺口假设**，
> 属无条件结果（它们只吃定理自身的语义前提：二元 cladogram ＋ 最优性）。
> 仍受限的是**概率层**：`MSCFreq.majorizes`（MSC 核心不等式）与 `MSCSampling.converges`
> 是结构字段（公理化），此处不隐瞒。
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

★ 下表全部为 **`2026-10-27` 实测值**（`2026-10-26` 那一版「156 模块 / 101,916 行 / 6,378 声明 / 3988 jobs」
已被本表取代；更早的「155 模块 / 100,768 行 / 6,323 声明 / 3987 jobs」、「151 模块 / 98,677 行 / 6,207 声明 / 3983 jobs」
与「27 文件 / 7200 行 / 401 声明 / 3187 jobs」均已作废）。
复跑：`bash scripts/measure.sh`（**仓库内脚本**，口径与本表逐字一致 —— 剥注释后统计；口径说明见脚本头部）。

| 指标 | 值（`2026-10-27` 实测） |
|---|---|
| Lean 模块 | **156**（`Phylo/**` 的 `.lean` 文件数 **恒等于** `Phylo.lean` 的 `import Phylo` 条数；另有根模块 `Phylo.lean` 本身，故库内 `.lean` 计 **157** 个） |
| Lean 源行数 | **105,222**（`Phylo/**/*.lean`） |
| 顶层声明 | **6,486**（剥注释后机械统计 `theorem`/`lemma`/`def`/`abbrev`/`structure`/`class`/`instance`/`inductive`） |
| `sorry` / `axiom` / `opaque` | **0 / 0 / 0**（未形式化处落成显式 `def … : Prop` 缺口登记） |
| `lake build` | **通过（3988 jobs）** |
| 缺口台账（七桶 · `scripts/list_gaps.sh`） | 真开放 **0** · 已收口 44 · 条件收口 2 · 已证伪 21 · 追溯 1 · 判定收档 2 · 长期开放 1 ＝ **71** |

复跑方式：`lake build`（job 数）、`bash scripts/list_gaps.sh B`（七桶）、`bash scripts/check_vacuous.sh`（空转自证）。

## 缺口台账：七桶怎么读（正面回答外部审查的「53%」）

`scripts/list_gaps.sh` 把全部 **71** 条缺口登记（`def … : Prop`）按**状态**分七桶；
判据写死在 `scripts/gap_ledger.py` 里，并逐条打印收口定理的**完整签名**供人工核「有没有吃假设」。
当前实测：

| 桶 | 条数 | 含义（判据见 `gap_ledger.py`） |
|---|---|---|
| **真开放** | **0** | 既无收口定理、又无机器反例 ⇒ **唯一**还需要做数学的桶 |
| **已收口** | 44 | 存在**无条件、无特化**的收口定理（多吃一个显式假设就降入「条件收口」） |
| 条件收口 | 2 | 收口定理多吃了 `def` 里没有的假设，或把 `def` 特化到了具体集合实例 |
| **已证伪** | 21 | 存在**机器反例**定理（`¬ gap` / `¬ ∀ …`）：陈述本身是假命题 |
| 追溯 | 1 | 名字以 `_legacy` 结尾：旧形态留痕，已有取代它的正名 |
| 判定收档 | 2 | 白名单 `ARCHIVED_JUDGED`：按「任务完成」收档，不再计作开放 |
| 长期开放 | 1 | 白名单 `LONGTERM_OPEN`：有可证内容但**裁定不证**（Conjecture 类，不进派单） |

### ① 「已证伪」为什么不算「未闭合」

「已证伪」= 我们先把它写成 `def … : Prop`，再证出**它是假命题**（机器反例定理）。
**它已经有结论了**（`¬ gap` 就是定理），不是「还欠一个证明」；所以它既不该进「真开放」，
也不该从「闭合」里被扣 —— 它已经从「待证」变成了「已判定」。

⚠️ 但**读者风险是真的**：`grep gap` 会把假命题与待证目标混在一起。所以读这个库时，
**先看 `bash scripts/list_gaps.sh B` 给出的桶位，再读源码**。

源码层也已处置（W35）：这 21 条 `def` 的 docstring **首行**都带
`⚠️ **已证伪，非待证目标** —— 机器反例见 <定理名>（<文件>:<行>）`，
由 `bash scripts/check_refuted.sh` 机器核（缺标记、或标记点名的定理与实际反例不符，即非零退出）。

### ② 「空转」6 条：已登记、有机械依据、且单列

`scripts/check_vacuous.sh` 对 6 条「`∃` 自由槽」缺口给出**可复跑的定理依据** ——
例如 `bootstrap_confidence_gap_iff_true`：`∃ Ω TrueSplit p` 三个自由槽，取 `Ω := Empty`
则三条 `∀ ω` 全空真 ⇒ `bootstrap_confidence_gap ↔ True`。
它们仍留在「已收口」桶（收口定理确实成立），但**内容空转**：数学内容为零。
台账 `VACUOUS` 白名单逐条登记；脚本找不到依据定理就以非零码退出
（「空转」判定必须**可复跑**，不许口头声明）。

### ③ 严格口径：去掉已证伪与空转之后

外部审查按「已证伪不算闭合、空转不算内容」重算，得 **38 条**：
`44（已收口）− 6（空转）= 38`，占 71 的 **≈ 53.5%**（即审查报告写的「53%」）。
这个数字不回避，就写在这里：**严格口径 = 38 / 71**。
本库对外声称的是「71 条登记**状态全部判定清楚**（真开放 0）」，
**不是**「71 条都证成了」—— 两者差别以本节为准。

## 快速开始

```bash
lake exe cache get    # 下载 Mathlib 预编译缓存（首次必需；否则要编译数小时）
lake build
```

在 VS Code 中打开**目录**（不是单个文件）以获得完整补全。

## 收录纪律（本仓库里到底有什么）

判据只有一条：**`git ls-files` 的输出必须与本节一致**。

- **项目成果**：证明代码（`Phylo/**`、`Phylo.lean`）、`README.md`、`LICENSE`、
  `scripts/`（护栏脚本 `list_gaps.sh` / `gap_ledger.py` / `check_vacuous.sh` /
  `check_file_imports.sh` / `measure.sh`，以及 `scripts/f84/`、`scripts/msc/` 的可复现数据脚本）。
- **构建与 CI 配置**：`lakefile.toml` · `lake-manifest.json` · `lean-toolchain` ·
  `.gitattributes` · `.gitignore` · `.github/workflows/build.yml`。
- **仍在被证明引用的规格 / 发现记录（5 份，入库）**：`MSC_INSTANCE_SPEC.md` ·
  `MSC_KINGMAN_SPEC.md` · `W10_COALESCENT_SPEC.md` · `CASTER_F84_PROPASPEC.md` ·
  `CASTER_F84_FINDING.md`。它们以「`<文件名>` §x.y」的形式被 `Phylo/**` 的 docstring
  指名引用（规格条目、笔误更正、常数因子定位），属**证据链的一部分**，故留在库内。
- **不在库内**：工作日志 / 总结 / 卡点报告 / 任务交接（原先入库的 `W10_SUMMARY.md`、
  `W16a_BLOCKER.md`、`W16b_HANDOVER.md` 已于 W35 移出，见 `git log`）、参考文献汇编
  （`references/`）、agent 记忆与交接文档（`MEMORY.md` / `HANDOVER.md` 等，由 `.gitignore` 挡住）。
  这些在项目外维护，不在 GitHub 上。
