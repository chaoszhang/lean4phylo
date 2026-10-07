# HANDOVER.md —— `lean4phylo` 交接文档

> **生成时间**：2026-10-07 10:20（Asia/Shanghai）
> **最后更新**：2026-10-07 13:10（**新增 §4 的 T0 批：把 `references/` 里的原始证明搬进 Lean，列为最高优先级**）
> **面向**：接手继续长时自主执行的 agent（下文称「你」）
> **当前快照**：`main` @ `5c2dad0`，**3186 jobs `lake build` 通过**（WSL 增量 ~10s），**库内零 `sorry`**
> **规模**：26 个 `Phylo/**/*.lean` / **6750 行** / **386 个顶层声明**
> **未推送**：0（已同步 `origin/main`）

> 🚀 **下轮第一件事：读 §4 开头的「T0」整节** —— 原始文献已抓齐并转成可读 Markdown
> （`references/README.md` 有「缺口 → 证明出处 + md 内精确行号」速查表）。
> **T0 的核心变化：这些缺口不再是「探索性工作」，而是「照着已有证明写 Lean」。**
> 其中 **T0.1（`QuartetDecidesTree`）是最高优先级** —— 它三个条件里的 `transitive` 库里已有。

> ⚠️ **2026-10-07 12:40 老师加的三条硬约束（纪律 11–13）—— 见下方「⚠️ 必读」节** —— 上一轮 dsh 因违反它们
> 造成一次静默数据丢失（`MEMORY.md` 被回退 383 行）+ 一次 docstring 虚报。

---

## ⚠️ 必读：2026-10-07 新增的三条硬约束（**违反即视为事故**）

> （本节刻意置于 §0 之前 —— 它是最高优先级，接手第一眼就该看到。）

> **背景**：dsh 首轮（11:25）在 `Phylo/Algorithm/NNI.lean` 上工作，产出本身合格（`lake build` 3186 jobs 通过、零 sorry），
> 但同时造成两起事故。老师已确认继续使用 dsh，故**把事故转化为明文约束**。

### 纪律 11 —— `MEMORY.md` **只许追加**，严禁精简 / 回退 / 重写历史章节

dsh 首轮把 `MEMORY.md` 从 **680 行砍到 319 行**，删掉 8 个大章节（`toCladogram 里程碑` /
`★★★ 相容⟹存在树全线打通` / `★★★★ 统计一致性层` / `★★★★ Aho/共识/超度量/SVDQuartets 层` 等），
并**插回已被更新掉的旧版「设计卡点 待老师定」段落** —— 这是**信息回退**，不只是删除。
commit message 里**一字未提**。所幸完整版在 git 中，已从 `8d26030` 恢复合并。

**规则**：
- ✅ 允许：在文件**末尾追加**新章节；在现有章节**内部追加**要点；修正**错别字**。
- ❌ 禁止：删除任何现有章节/段落；把某段「压缩成一句话」；把内容改写成更早的版本；
  在未 `git log --oneline -- MEMORY.md` 确认基线前用本地旧副本整体覆盖。
- 若真需要精简（文件过大）：**先归档**到 `MEMORY/<日期>-<主题>.md`，再在 `MEMORY.md` 留下**指向归档的索引行**。
- **改前自检**：`wc -l MEMORY.md` 与 `git show HEAD:MEMORY.md | wc -l` 应一致；不一致说明你有未合并的本地改动，先停下来报告。

### 纪律 12 —— **docstring 里的 ★ 必须对应真实存在的声明**

dsh 首轮在 `NNI.lean` 第 50–51 行的「本文件做到哪」成果清单里列出：

```
* ★★  `nniResolvent_compatible` —— NNI 分解与母 split 相容；
* ★★★ `nniResolvent_swap_incompatible` —— 同一母 split 的两个互补分解互不相容
```

但这两个定理**在文件里根本不存在**（只有段注释里的证明思路）；同文件后面的 `⬜ 未完成` 段
又自相矛盾地承认它们没做。这种「成绩单注水」比留一个 `sorry` 更危险 —— 后续 agent 会当真。

**规则**：
- 未证明的命题**一律**落成显式 `def ⟨名字⟩ : Prop := …` 缺口（本库既有惯例：
  `MaxZCherryCore` / `QuartetDecidesTree`），**而不是**在 docstring 里标 ★。
- docstring 的「本文件做到哪」只列**已编译通过**的声明；「缺什么」单独一段列。
- **自检**：docstring 里出现的每个反引号标识符，都应在同一文件里能被 `grep "^theorem\|^def"` 命中。

### 纪律 13 —— 每批结束**回写 `HANDOVER.md`**（见 §7.5）

老师要求：**接手方在每完成一批后，更新本文件**。不要另起炉灶写第二份交接文档 —— 就地更新
§2 清单、§3 瓶颈图、§4 任务状态、§5 踩坑、头部快照与「未推送」计数。

---

## 0. 三十秒版本

**这是什么**：一个用 Lean 4 + Mathlib 形式化**系统发生学（phylogenetics）经典算法**的库，库名 `Phylo`，仓库 `lean4phylo`。目标不是「证明某个大定理」，而是**一个可长期积累的算法正确性库**。

**已经做完的**：树/分裂/quartet 三层的定义与基础定理；**Splits-Equivalence 两个方向**（树 ⟹ 相容、相容 ⟹ 存在树）；Aho–Buneman 建树；多数共识树；UPGMA 结构定理；cherry 存在性；RF 距离度量性；二叉树计数与 quartet 唯一性；**ASTRAL / CASTER / parsimony 三者的 quartet-MSC 统计一致性**；**SVDQuartets 的正确性**；以及最近的 **NNI 的 split 层分解**。

**现在卡在哪**：**一个共享缺口**——`QuartetDecidesTree`（「两棵 binary 树 quartet 系统相同 ⟹ 同构」）。它是 4 个算法从「逐 quartet 一致」升级到「同构」的最后一步。围绕它还有 **3 个硬骨头**（见 §3）。

**你的第一件事**：读开头「⚠️ 必读」节的纪律 11–13（**刚有人踩过**），读 §2 确认「已完成，别重做」，
然后**直接做 §4 的 T0 批（最高优先级）**：原始证明已抓齐在 `references/`，
`references/README.md` 有「缺口 → 证明出处 → md 内精确行号」速查表。
**T0 是「照抄证明」，不是探索** —— 起点是 **T2 → T0.1**。


---

## 1. 项目坐标与环境

### 1.1 路径

| 角色 | 路径 |
|---|---|
| **源码正本（Windows）** | `C:/Users/ASTER/WorkBuddy/Project/lean/lean4phylo/` |
| **构建目录（WSL 原生盘）** | `~/lean4phylo`（`/home/chaos/lean4phylo`） |
| **远程仓库** | `git@github.com:chaoszhang/lean4phylo.git`（**SSH**） |
| 旧 NJ 独立工程（保留） | `C:/Users/ASTER/WorkBuddy/Project/lean/` 的 `NJ/`、`NJ.lean`、`ROADMAP.md` |

> ⚠️ 顶层目录 `Project/lean/` **本身不是 git 仓库**；仓库根是 `Project/lean/lean4phylo/`。

### 1.2 工具链

- `lean-toolchain` = `leanprover/lean4:v4.35.0-rc3`
- mathlib4 `master`（`lake-manifest.json` 已固定 rev）
- WSL 侧：elan → `~/.elan/bin/lake`
- `~/lean4phylo/.lake/packages` 是**软链** → `~/nj-lean/.lake/packages`（复用 7.2G mathlib 预编译缓存，**不要删**）

### 1.3 构建 / 验证流程（三步）

```bash
# ① 同步：Windows 正本 → WSL 构建目录（每次改完源码都要做）
wsl -e bash -lc 'cp -r /mnt/c/Users/ASTER/WorkBuddy/Project/lean/lean4phylo/{lakefile.toml,lean-toolchain,Phylo.lean} ~/lean4phylo/ && cp -r /mnt/c/Users/ASTER/WorkBuddy/Project/lean/lean4phylo/Phylo/* ~/lean4phylo/Phylo/'

# ② 单文件快速迭代（~9s，开发主力）
wsl -e bash -lc 'cd ~/lean4phylo && ~/.elan/bin/lake env lean Phylo/Stat/SVDQuartets.lean'

# ③ 全量构建（增量 ~8s，冷启动几分钟）
wsl -e bash -lc 'cd ~/lean4phylo && ~/.elan/bin/lake build'
```

**踩坑提醒**：
- `lake` **必须在项目目录内运行**，否则报 `no default toolchain configured`。
- WSL 侧部分文件是 **CRLF**（历史遗留），Lean 能接受；**新文件一律 LF**（Python 写文件须 `newline='\n'`）。
- Windows 侧没有 `lake` / `elan`。**别在 Windows 上编译**。

### 1.4 git

```bash
# 提交（在 Windows 侧即可）
cd /c/Users/ASTER/WorkBuddy/Project/lean/lean4phylo && git add -A && git commit -m "模块: 一句话（★ 星级）"

# push（★ 认证只在 WSL 侧！Windows 没有 SSH key）
wsl -e bash -lc 'cd /mnt/c/Users/ASTER/WorkBuddy/Project/lean/lean4phylo && \
  GIT_SSH_COMMAND="ssh -o StrictHostKeyChecking=no -o BatchMode=yes" \
  git -c safe.directory="*" push -u origin main'
```

- 提交身份：`chaoszhang <chaoszhang@users.noreply.github.com>`
- CI：`.github/workflows/build.yml`（`lake exe cache get` → `lake build`），历史**全绿**。
- **既有纪律：只 commit、不 push**，除非老师明确说 push。

---

## 2. 已完成清单（**别重做**）

### 2.1 算法工具层 —— 「哪些算法已经证出来了」

| # | 工具 / 算法 | 主定理 | 文件 | 状态 |
|---|---|---|---|---|
| 1 | **树 ⟹ split 两两相容** | `Cladogram.pairwiseCompatible` | `Phylo/Split.lean` | ✅ 无条件 |
| 2 | **相容 ⟹ 存在树**（Aho–Buneman） | `compatible_exists_rootedTree` | `Phylo/Aho.lean` | ✅ 无条件 |
| 3 | **多数共识树**（Margush–McMorris 1981） | `majority_consensus_exists` | `Phylo/Consensus.lean` | ✅ 无条件 |
| 4 | **UPGMA 结构定理**（超度量 ⟹ 球族 ⟹ 树） | `exists_rootedTree_displays_balls` | `Phylo/Dendrogram.lean` | ✅ 无条件 |
| 5 | **ASTRAL 得分理论** | `astralScore_le` / `astralScore_eq_iff` / `astral_maximizer_agrees` | `Phylo/Stat/ASTRAL.lean` | ✅ 无条件 |
| 6 | **ASTRAL 统计一致性** | `astral_statisticallyConsistent` | `Phylo/Stat/Stability.lean` | ✅ 模 `QuartetDecidesTree` 收口 |
| 7 | **CASTER 统计一致性** | `casterScore_eq` / `caster_statisticallyConsistent` | `Phylo/Stat/CASTER.lean` | ✅ 无条件（归约到 ASTRAL） |
| 8 | **parsimony 统计一致性**（ISM） | `Pattern.fitchCost_eq` / `parsimony_statisticallyConsistent` | `Phylo/Stat/Parsimony.lean` | ✅ 无条件 |
| 9 | **SVDQuartets 正确性** | `svdquartets_selects_true` / `svdquartets_concrete` | `Phylo/Stat/SVDQuartets.lean` | ✅ **无条件**（分离性定理） |
| 10 | **cherry 存在性** | `Cladogram.exists_isCherry` | `Phylo/Algorithm/Cherry.lean` | ✅ 无条件（纯组合计数） |
| 11 | **RF 距离是度量** | `rfDistance_comm` / `_triangle` | `Phylo/Algorithm/RF.lean` | ✅ 无条件（split 集合层面） |
| 12 | **NJ 代数层** | `Q_eq_neg_two_ell` / `two_mul_z` / `z_hinge` / `four_point_z_iff` | `Phylo/Algorithm/NJ.lean` | ✅ 代数部分无条件 |
| 13 | **NJ 樱桃引理** | `nj_cherry` | `Phylo/Algorithm/NJ.lean` | ⚠️ 依赖显式假设 `MaxZCherryCore` |
| 14 | **NJst 第一步** | `njst_cherry` / `four_point` | `Phylo/Stat/NJst.lean` | ⚠️ 依赖 NJ 硬核 |
| 15 | **二叉树计数学** | `ℓ = i+2` / `|V| = 2ℓ−2` / `|E| = 2ℓ−3` | `Phylo/Algorithm/BinaryCount.lean` | ✅ 无条件 |
| 16 | **二叉树 quartet 唯一性** | `Cladogram.displaysSplitOn_unique` | `Phylo/QuartetUnique.lean` | ✅ 无条件 |
| 17 | **Colonius–Schultze 推理规则** | `displaysQuartet_of_displaysQuartet_common` | `Phylo/Quartet.lean` | ✅ 无条件 |
| 18 | **不兼容 split ⟹ 不同 quartet** | `exists_restrict_ne_of_incompatible` | `Phylo/Binary.lean` | ✅ 无条件 |
| 19 | **侧分量子树是树**（阶段 1） | `isTree_induce_sideVertices` | `Phylo/SideSubtree.lean` | ✅ 无条件 |
| 20 | **NNI 分解**（split 层，🔄 dsh 首轮） | `Split.nniResolvent` / `nniParts_zero` / `nniResolvent_sideA/sideB` | `Phylo/Algorithm/NNI.lean` | 🔄 定义 + 分块引理；相容/不相容未做 |

> **一句话总结给老师看的**：**ASTRAL、CASTER、parsimony、SVDQuartets 四个算法的核心正确性已经形式化**；NJst 拿到第一步；NJ 拿到全部代数骨架，剩一条**经典定理的形式化缺口**（`MaxZCherryCore`，见 T4 的定性说明 —— **不是**数学开放问题）。

### 2.2 基础层（定义 + 地基，全部无条件）

| 文件 | 行 | 内容 |
|---|---|---|
| `Phylo/Core.lean` | 342 | `Cladogram`（`V`/`graph`/`leaf : X ↪ V`/`isTree`/`no_degree_two`）· `IsLeaf` · `isLeaf_iff_degree_eq_one` · `existsUnique_path` · `IsBinary` · `RootedCladogram` · `Phylogram`（边权 + `dist`）· `Iso`（`refl`/`symm`/`trans`）· `RootedTree` / `toRootedTree` |
| `Phylo/Split.lean` | 917 | `KPartition α n` / `Split α := KPartition α 2` · `Compatible` · `restrict` · `sideLeaves`（可达版）· `splitOfEdge` · `splits` · `PairwiseCompatible` · `cluster` · `IsSplitOf` |
| `Phylo/Laminar.lean` | **1821** | 镶嵌族全套 → `laminarGraph` / `treeGraph` · **`isTree_treeGraph`** · `no_degree_two` 系列 · `toCladogram` / `toRootedTreeOfCard` · `splitOf` / `isSplitOf_splitOf` / `splitOf_mem_splits` · `mem_iff_reachable` · `leafSide_parentEdge_of_card` |
| `Phylo/Quartet.lean` | 342 | `Quartet X` / `TripletSet` / `Topology S := Split ↥S` · `QuartetTopology` · `swap` · `allQuartets` + 计数 · **display 层** |
| `Phylo/Distance.lean` | 54 | `symmDiffCard`（通用对称差） |
| `Phylo/Mathlib/Walk.lean` | 61 | `reachable_deleteEdges_of_support_notMem`（待回灌 Mathlib） |
| `Phylo/Stat/*` | 1060 | MSC 公理化 + 四算法一致性（见上表） |

### 2.3 必读的既有文档

| 文件 | 用途 |
|---|---|
| **`references/README.md`** | ★ **`references/` 文献汇编的索引**：缺口 → 证明出处速查表（带 md 内精确行号）。**做 T0 前必读。** |
| `MEMORY.md`（~72KB，715 行） | **工作日志**：每轮的进展、踩坑、决策。**改动前必查**——很可能有人已经试过并失败了。 |
| `CONCEPTS.md`（76KB，1003 行） | **概念设计**：每个定义的选择理由（§3.1–§3.11 的「已定方案」）+ 文献先例。**不要重新发明定义。** |
| `DESIGN.md` | 库设计：Mathlib 现状实测表 / 分层架构 / 决策 D1–D4 |
| `SCAFFOLD.md` | 工程骨架与四条实践（文件头规范、docstring、根模块同步、linter） |
| `README.md` | 环境搭建 |

> **`references/` 目录**（本地，`pdf/md/img/ocr` 因版权**未入库**）：
> `README.md` + `pdf/` 8 篇原文 + `md/` 可读 Markdown + 转换脚本。
> 派生物只在老师本机，**新会话若看不到 `pdf/`、`md/` 是正常的** —— 用 `README.md` 里
> §7 的复现命令重跑（脚本已入库）。

---

## 3. 三处共享瓶颈（一张依赖图）

> 📌 图中的 `T1 / T3 / T4 / T5 / T8` 标签是**旧编号**；它们现已并入 **§4 的 T0 批**（最高优先级）：
> `T1→T0.1`（quartet 决定树）、`T3→T0.2`（Buneman）、`T4→T0.3`（NJ 硬核）、
> `T5→T0.5`（SVDQuartets）、`T8→T0.4`（NJst）。**`T2` 保持原编号**（T0.1 的前置）。

```
                    ┌──────────────────────────────────────┐
                    │  T2  「内部边两侧各 ≥ 2 叶」          │  ← T0.1 的前置，开工第一站
                    │      (SideSubtree 阶段 2)             │
                    └───────────────┬──────────────────────┘
                                    │
       ┌────────────────────────────┼────────────────────────────┐
       ▼                            ▼                            ▼
┌──────────────┐          ┌──────────────────┐         ┌──────────────────┐
│ T0.1 ★★★★    │          │ T6 KF 距离        │         │ T0.1 第 5 步      │
│ QuartetDecides│         │ (需要 split 构造) │         │ 内部边叶侧由      │
│ Tree          │◄─────────┤                  │         │ quartet 见证      │
└──────┬───────┘          └──────────────────┘         └──────────────────┘
       │ 解锁
       ▼
┌──────────────────────────────────────────────────────┐
│ astral_iso / caster_iso / parsimony_iso   （已写好，  │
│ 只等 QuartetDecidesTree 从 def 变 theorem）           │
└──────────────────────────────────────────────────────┘

独立支线（现为 T0.2 → T0.3 → T0.4）：
┌──────────────────┐     ┌──────────────────┐
│ T0.2 Buneman 存在性│───►│ T0.3 MaxZCherryCore│─► T0.4 NJst 完整正确性
│ (四点条件⟹实现树) │     │ (照抄 Weller Thm 2)│
│ Buneman 1971/1974 │     │                    │
└──────────────────┘     └──────────────────┘

可独立推进：
┌──────────────────┐     ┌──────────────────┐
│ T0.5 SVDQuartets  │     │ T7 restriction    │
│ 统计一致性(非正确性)│    │ T|Y (suppress)    │
└──────────────────┘     └──────────────────┘
```

---

## 4. 剩余任务

> **执行顺序**：**T0 批（最高优先级）** → T2（T0.1 的前置）→ 余下 T6/T7/T9 → 最后是长线。
> **T0 是老师 2026-10-07 亲自排到首位的任务**：原始证明已抓齐（见 `references/`），
> 这一批就是**照抄证明**，不是探索。
> 老的 T1/T3/T4/T5/T8 **已并入 T0**（各自标题下有 `→ 已升为 T0.x` 的指引），保留原编号仅为对照。

> 📋 **「再往后做什么」见 [`NEXT.md`](NEXT.md)** —— 那是**提案清单**（老师挑选用），
> 不是执行计划。收录了 30+ 个尚未形式化的知名定理/算法（含推荐 top-5 与「去公理化」路线图）。
> **本文件（§4）是当前执行计划；`NEXT.md` 是候选池。**

---

## 4.0 🚀【最高优先级】T0 —— 把 `references/` 里的原始证明搬进 Lean

> **老师指令（2026-10-07）**：「把证明这些引理也作为下轮 dsh 的任务，**放在优先级首位**。」
>
> **前置准备已完成**：`references/` 已收 8 篇原始文献的 PDF + 可读 Markdown，
> `references/README.md` 给出「**缺口 → 证明出处 → md 内精确行号**」速查表。
> ⇒ **动工前必做**：打开 `references/README.md` 找到对应那一行，再打开 md 看定理原文与证明。

### T0 总览（内部顺序即建议执行顺序）

| 子任务 | 内容 | 依据（`references/md/`） | 依赖 |
|---|---|---|---|
| **T0.1 ★★★★** | **`QuartetDecidesTree`**（路线 B：thin + transitive + saturated） | `HuberEtAl2017_*.md` **315 行**（Thm 6）；`Huber2018_*.md` **412 行**（Thm 1） | T2 |
| **T0.2 ★★★** | **Buneman 存在性**（四点条件 ⟹ 树度量） | `Buneman1974_*.md`（3 页全文） | 无 |
| **T0.3 ★★★** | **`MaxZCherryCore`**（NJ 樱桃引理） | `Weller2023_*.md` **378 行**（Thm 2） | **T0.2** |
| **T0.4 ★★** | **NJst 完整一致性** | `AllmanDegnanRhodes2016_*.md` **610 行**（Thm 4.1） | T0.3 |
| **T0.5 ★★** | **SVDQuartets 统计一致性** | `ChifmanKubatko2015_*.md` | 无 |

**依赖链**：`T2 → T0.1` ／ `T0.2 → T0.3 → T0.4` ／ `T0.5` 独立。

---

### T0.1 ★★★★ `QuartetDecidesTree` —— 用「thin + transitive + saturated」路线（**最高中的最高**）

> ✦ **为什么它排第一**：三个条件里**一个库里已经有了**（`transitive`），
> 一个是 binary 树的免费推论（`thin`），只剩 `saturated` 是真正的新工程量。
> 这是全表**性价比最高**的一格。

**依据原文**（`references/md/HuberEtAl2017_SymbolicTernaryMetrics.md` **第 301–316 行**）：

> A quartet system `Q` is **thin** if for every 4-subset `{a,b,c,d}`, at most one of
> `ab|cd`, `ac|bd`, `ad|bc` is contained in `Q`.
> It is **transitive** if for any 5 distinct `a,b,c,d,e ∈ X`, the quartet `ab|cd` is in `Q`
> whenever both `ab|ce` and `ab|de` are in `Q`.
> It is **saturated** if for any five distinct `a,b,c,d,e ∈ X` with `ab|cd ∈ Q`,
> at least one of `ae|cd` and `ab|ce` is also in `Q`.
>
> **Theorem 6.** `Q ⊆ Q(X)` is of the form `Q = Q(T)` for some phylogenetic tree `T`
> **if and only if** `Q` is thin, transitive and saturated.

等价出处：`Huber2018_*.md` **第 412 行**（**Theorem 1**，**两条件版**）：
> A quartet system `Q` is of the form `Q = Q(T)` for a **(necessarily unique)** phylogenetic X-tree `T`
> **if and only if** `Q` is **thin and saturated**.

**分解步骤**：

1. **建载体**：把「full quartet 系统」（每个 4-元集恰一个 quartet 选择）显式建模 ——
   库内 `QuartetChoice X` 已是这个形状，先确认接口。
2. **`thin`**（预计免费）：对 **binary** 树，每个 4-元集恰展示一个 quartet。
   ⇒ **核对 `Phylo/QuartetUnique.lean` 的 `Cladogram.displaysSplitOn_unique`（★★★）是否直接给出**。
3. **`transitive`**（**已免费**）：`ab|ce ∧ ab|de ⟹ ab|cd`
   = `Phylo/Quartet.lean` 的 `Cladogram.displaysQuartet_of_displaysQuartet_common`。
   ⇒ 只需把它**接到「full quartet 系统」语境**（现在是 `DisplaysQuartet a b c d` 形式）。
4. **`saturated`**（★ 主要工程量）：五元集条件。**优先试「两条件版」**
   （`Huber2018_*.md` 第 412 行的 thin + saturated）—— 少一条要证。
5. **唯一性收口**（`T ≅ T'`）：两条路任选
   - **(a) 走 split**：由 `Q(T) = Q(T')` 恢复 `Σ(T) = Σ(T')`（每条内部边的叶侧由 quartet 见证），
     再接 `Phylo/Aho.lean` 的 `compatible_exists_rootedTree` + `Phylo/Laminar.lean` 的
     `splitOf`/`splitOf_mem_splits`/`toRootedTreeOfCard`。
   - **(b) 直接用** Thm 1 的「**necessarily unique**」—— 需把唯一性本身形式化。

**前置 T2**：第 5(a) 步「内部边的叶侧由 quartet 见证」要用到
「内部边两侧各 ≥ 2 叶」—— 即 `Phylo/SideSubtree.lean` 的阶段 2（见 **T2**）。

**验收**：`Phylo/Stat/QuartetDecides.lean` 里的 `def QuartetDecidesTree` 变成 `theorem`
（或降级为别名）；`astral_iso` / `caster_iso` / `parsimony_iso` **去掉 `hQD` 假设**。
**全库仍零 `sorry`。**

---

### T0.2 ★★★ Buneman 存在性（四点条件 ⟹ 存在实现加权树）

**依据原文**：`references/md/Buneman1974_MetricPropertiesOfTrees.md`（3 页全文，扫描件 OCR）
+ `references/md/Buneman1971_RecoveryOfTreesFromDissimilarity.md`（9 页全文）。
⚠️ **公式请回看 `references/pdf/` 的原始扫描件**（OCR 对下标/符号有误差）。

| 项 | 内容 |
|---|---|
| **建议位置** | 新文件 `Phylo/Buneman.lean` |
| **陈述** | `Dissimilarity.FourPoint δ ⟹ ∃ (加权树 T), ∀ i j, δ i j = T.dist (leaf i) (leaf j)` |
| **模板（现成）** | `Phylo/Dendrogram.lean`：超度量 ⟹ 球族 `ball_subset_or_disjoint` 镶嵌 ⟹ `laminarFamily_ballImage` ⟹ `exists_rootedTree_displays_balls` |
| **建议路线** | 照抄该模板 —— 把 `FourPoint δ` 化作一族镶嵌的 `Finset`（Buneman 的「团 / cluster」），再走 `Phylo/Laminar.lean` 的 `toRootedTreeOfCard` |
| **RHS 已备好** | `Phylogram.dist`（唯一路径边权和） |

**解锁下游**：**T0.3**、NJ 完整正确性、KF 距离（原 T6）、距离→树的整套算法。

---

### T0.3 ★★★ `MaxZCherryCore`（NJ 樱桃引理）

**依据原文**：`references/md/Weller2023_NeighborJoining_LeafStatus.md`：

| md 行号 | 内容 |
|---|---|
| **124** | **Theorem 1（Neighbor Joining Theorem）** —— 主定理陈述 |
| 142–144 | **leaf-status 定义**：`ℓ_T(u) := Σ_{x∈L(T)} d(u,x)`（到**叶**的距离和） |
| **154** | **Lemma 1**：`ℓ(u) − ℓ(v) = ω(uv)·(\|L^←\| − \|L^→\|)` |
| 213 | **Corollary 1**：最小化 leaf-status 的节点不是叶 |
| **219** | **Lemma 2**：沿路径的 leaf-status 单调性 |
| **334** | **Lemma 3**：cherry 中点 `w` 使 `d(x,p) ≤ d(x,w)` |
| **378** | **Theorem 2**（= 我们的 `MaxZCherryCore`） |
| **381** | **Theorem 2 的证明**（反证：取最小化 `ℓ` 的节点 `c`，导出矛盾） |

**依赖**：**T0.2**（Weller 的证明显式使用实现树 `T`）。

**先做的一次「对接口」**：Weller 用
`q(u,v) := (n−2)·d(u,v) − Σ_x d(u,x) − Σ_x d(v,x)` 与 leaf-status `ℓ`；
库内 `Phylo/Algorithm/NJ.lean` 用 `Q` / `ell` / `z := δ + ell`。
⇒ **先证两边的定义逐条对齐**（尤其 `ell` 与 `ℓ_T` 的「路径距离和」vs「到叶距离和」），
这是个**具体、机械但必须先做**的小任务，做完才能照搬 Weller 的引理。

**已备好的代数骨架**（`Phylo/Algorithm/NJ.lean`，可直接用）：
`Q_eq_neg_two_ell`（最小化 Q ⟺ 最大化 z）· `two_mul_z` · `z_hinge` ·
★★ `four_point_z_iff`（`n≥4` 时「四点和最小」⟺「z 的和最大」）。

**已排除的朴素路线**（有数值反例，**别再试**）：
1. 「最近距离对是樱桃」—— 假（1822 反例）；
2. 「局部 quartet `ui|vj` ⟹ `z(u,i) ≥ z(u,v)`」—— 假；
3. 「`(u,v)` 非樱桃 ⟹ `∃m, z(u,m) > z(u,v)`」—— 假。

**交叉验证**：`MihaescuLevyPachter2006_WhyNeighborJoiningWorks.md`（另一条完整证明，视角不同）。

**验收**：`def MaxZCherryCore` 变成 `theorem`；`nj_cherry` 去掉 `hcore`；
`Phylo/Stat/NJst.lean` 的 `NJstData.core` 字段可删。

---

### T0.4 ★★ NJst 完整一致性

**依据原文**：`references/md/AllmanDegnanRhodes2016_NJst_StatisticalConsistency.md`：
**Thm 4.1**（第 610 行，主定理）· **Thm 4.2**（636，USTAR 相异性）· **Thm 5.1**（831）。
第 760 行有 **Theorem 4.1 的完整证明**。

**现在做到哪**：`Phylo/Stat/NJst.lean` 只有 `njst_cherry`（**第一步正确**）。

**还缺两条**：
1. **T0.3**（`MaxZCherryCore`）；
2. **NJ 的归纳正确性** —— 合并 cherry 后新距离矩阵**仍是树度量**（四点条件保持），从而可归纳。

> 📌 **备选路线**：ADR 2016 真实走法是把 NJst **归约到 generalized STAR**（clade 共识），
> 而 STAR 的一致性最终需要「**clade 系统决定树**」—— 与 **T0.1** 同一类定理。
> ⇒ 若 T0.1 先完成，T0.4 可能可以直接复用。

---

### T0.5 ★★ SVDQuartets 的**统计一致性**（正确性已完成）

**依据原文**：`references/md/ChifmanKubatko2015_IdentifiabilityarXiv1406.4811.md`。

**已完成**（`Phylo/Stat/SVDQuartets.lean`）：★★★ **正确性**，且**无条件**
（`svdquartets_selects_true` + 分离性实例 `svdquartets_concrete`）。

**缺口**：**统计一致性** —— 实用的是**奇异值之和**（连续量），**不是秩**
（秩下半连续，扰动下会跳）。
**依赖**：`Mathlib/Analysis/InnerProductSpace/SingularValues.lean`。
**策略提示**：可复用 `Phylo/Stat/Stability.lean` 的通用引擎（`exists_gap` + `stable_argmax`）
—— 只要把「奇异值和最大」也表达成一个 `Finset` 上的得分函数。

**验收**：`svdquartets_statisticallyConsistent`，全库零 `sorry`。

---

### 4.1 T1 ★★★ `QuartetDecidesTree`（→ **已升为 T0.1，最高优先级**，见上）

> ⬆️ **本任务已并入 T0.1。** 下面保留原始记录供对照（定性说明 + 路线 A 细节）。
> **执行时以 T0.1 为准**（thin + transitive + saturated 路线）。

> ✦ **定性：这是「形式化缺口」，不是学术开放问题。** 定理本身是 **Colonius–Schultze (1981)**
> 与 **Steel (1992)** 的经典结果（教科书 Semple & Steel, *Phylogenetics* (2003) §6.4），
> **证明路线是已知的**，只是工作量大。别把它当成数学难题 —— 它是一份**确定的工程量**。

| 项 | 内容 |
|---|---|
| **位置** | `Phylo/Stat/QuartetDecides.lean:71`（现在是 `def QuartetDecidesTree (X) : Prop := ...`） |
| **陈述** | 两棵 **binary** cladogram `T, T'`，若逐 4-元集上展示的 quartet 一致（模 `swap`），则 `T ≅ T'` |
| **交付** | 把 `def` 换成 `theorem`（或新证 `theorem quartetDecidesTree`，`def` 保留作别名） |
| **文献** | **Colonius & Schulze (1981)**, *Tree structures for proximity data*；**Steel (1992)**, *The complexity of reconstructing trees from qualitative characters and subtrees*；Semple & Steel, *Phylogenetics* (2003) §6.4 |
| **为什么 binary 不可去** | polytomy refine 成 binary 不改任何 quartet ⟹ 反例 |

**路线 A：老师定的逆否路线**（`T ≇ T'` ⟹ 存在不兼容 split ⟹ 存在不兼容 quartet）：

1. **`T ≇ T'` ⟹ 存在 `s ∈ Σ(T)` 与 `Σ(T')` 不相容**
   —— 等价于 **binary 树 split 系统的极大性**（库内**尚无**）。
   标准证法：若 `s` 与 `Σ(T)` 全相容，则 `Σ(T) ∪ {s}` 相容 ⟹ 由 Aho(`compatible_exists_rootedTree`) 得树 `T''` ⟹ `T` 是 `T''` 的**收缩** ⟹ `T` 有度 ≥ 4 顶点，与 binary 矛盾。
   ⇒ **需要 refinement / contraction 理论**（`T''` 收缩到 `T`、`Σ` 随收缩单调）。
2. **不兼容 split ⟹ 同一 4-叶集上两个不同 quartet** —— ✅ **已做完**！
   `Phylo/Binary.lean` 的 ★★★ `exists_restrict_ne_of_incompatible`（配合 `exists_four_of_incompatible`）。
3. **收口**：把第 2 步的「两个不同 quartet」与假设「逐点一致（模 swap）」对撞。

**路线 B：Colonius–Schultze 推理规则（可能更短，推荐先试）**

C–S 给出的是**完整推理系统**（对 full quartet 系统完备），我们库里**已经有其中一条规则**：
`Cladogram.displaysQuartet_of_displaysQuartet_common`（`ab|ce ∧ ab|de ⟹ ab|cd`）。
⇒ 目标可以变成「**把 C–S 的推理规则补全**」：由逐点一致的 `q ≈ q'` 逐步推出 `Σ(T) = Σ(T')`，
再走 `Phylo/Laminar` 的 `splitOf` / `isSplitOf_splitOf` / `splitOf_mem_splits`
（**「split ↔ 规范簇」字典已打通**）收口到 `toRootedTreeOfCard`。
这条路线**不需要 refinement/contraction**，只需推理规则 + 已有的建树管线。

**验收**：`Phylo/Stat/QuartetDecides.lean` 中 `def QuartetDecidesTree` 消失（或降级为 `theorem` 的别名），
`astral_iso` / `caster_iso` / `parsimony_iso` 不再需要 `hQD` 假设。**全库仍零 `sorry`。**

---

### T2 ★★ 「内部边两侧各 ≥ 2 叶」（阶段 2）—— 基础设施，建议最先动手

| 项 | 内容 |
|---|---|
| **位置** | `Phylo/SideSubtree.lean`（132 行，阶段 1 已完成） |
| **目标** | `theorem two_le_card_sideLeaves`：`Cladogram.IsBinary`（或至少 `no_degree_two`）的**内部边**两侧各含 ≥ 2 个叶 |
| **为什么重要** | 是 **T1 第 1 步**、**quartet→split 恢复**、**KF 距离**三处的共同前置 |
| **阶段 1 已完成** | `sideVertices` · `mem_sideVertices` · ★★ `isTree_induce_sideVertices`（侧分量诱导子图是树）· `card_edgeFinset_induce_sideVertices`（`#边 + 1 = \|U\|`，**无减法**形式） |

**已知卡点（实测，务必先读）**：
- `T.graph.induce ↑(T.sideVertices …)` 这个**类型每次 `whnf` 都极贵**，`maxHeartbeats 1600000` 仍超时（编译 2 分半）。
- `degree_induce_of_neighborSet_subset` 还需要 `Fintype ↑(G.neighborSet v)` 实例，雪上加霜。

**建议的两条出路**：
1. 把 `sideVertices` 从 `def` 改 **`abbrev`**，让类型透明（减少 `whnf` 展开层数）；
2. **直接在子类型 `↥(sideVertices …)` 上定义图**，绕开 `Finset → Set → induce` 的三层转换。

**已有可用 API**：`SimpleGraph.degree_induce_of_neighborSet_subset` · `SimpleGraph.Walk.induce`（`Walk/Maps.lean:225`）· `Walk.mapLe` · `IsAcyclic.induce` · `IsTree.card_edgeFinset`（形式为 `#边 + 1 = |V|`，**无减法**）。

**已排除的路线**：`SimpleGraph.dist` 极大性 —— 最长距离顶点的邻居距离可能相等，不成立。

**验收**：`two_le_card_sideLeaves` 编译通过，全库零 `sorry`。

---

### T3 ★★★ Buneman 存在性（四点条件 ⟹ 存在实现加权树）—— 经典定理的形式化

> ⬆️ **已升为 T0.2（最高优先级），见上。** 保留原始记录供对照。

> ✦ **定性**：这也是**经典已证定理** —— **Buneman (1971)**, *The recovery of trees from measures of dissimilarity*；
> 亦见 Semple & Steel, *Phylogenetics* (2003) §7.2 与 Buneman 定理的标准证明。
> 不是开放问题；同样是**形式化工作量**问题。

| 项 | 内容 |
|---|---|
| **建议位置** | 新文件 `Phylo/Buneman.lean` |
| **陈述** | `Dissimilarity.FourPoint δ ⟹ ∃ (加权树 T), ∀ i j, δ i j = T.dist (leaf i) (leaf j)` |
| **为什么工作量大** | 需要构造顶点集（Buneman 的「团 / cluster」）、边权（Gromov 积的两两差）、并验证路径和；库里已有 `Phylogram.dist`（唯一路径边权和）可直接当 RHS |
| **文献** | Buneman (1971)；Semple & Steel, *Phylogenetics* (2003) §7.2 |

**关键情报（本轮新发现，能省大量工作）**：
- MEMORY 里记的旧卡点「连通性需根 vs `no_degree_two`」**已经被绕开了**：
  `Phylo/Laminar.lean` 的 `toRootedTreeOfCard` + `isTree_treeGraph` 已经把「**镶嵌族 ⟹ 树**」建起来了。
- `Phylo/Dendrogram.lean` 已经用同一个模板走通了一整条同类构造：
  **超度量 ⟹ 球族 `ball_subset_or_disjoint` 镶嵌 ⟹ `laminarFamily_ballImage` ⟹ `exists_rootedTree_displays_balls`**。
- ⇒ **建议路线**：Buneman 的存在性照抄 UPGMA 的模板 —— 把 `FourPoint δ` 化作一族镶嵌的 `Finset`（Buneman 的「分裂 / 团」），
  然后复用 `toRootedTreeOfCard`。实质是「把 `δ` 的 cluster 族做成镶嵌族」。

**解锁下游**：**T4（NJ 硬核）**、距离→树的整套算法（UPGMA 已部分走通）、KF 距离的实现层。

**风险**：中高。建议**先花两小时做原型**，若 `whnf` 或组合结构再次爆炸，回退到 T1/T2。

---

### T4 ★★★ `MaxZCherryCore`（NJ 定理的纯度量表述，**形式化缺口**）

> ⬆️ **已升为 T0.3，见上。** 保留原始记录供对照。

> ✦ **定性：不是学术开放问题。** NJ 的正确性**早已证明** ——
> **Studier–Keppler (1988)** 给出首个正确证明（并指出 Saitou–Nei 1987 原始证明有误），
> **Weller (2023)** 用 *leaf-status* 极简重证，Mihaescu–Levy–Pachter (2009) 亦有。
> 缺口在于本库**尚未形式化其前置**「Buneman 存在性」，不是数学未解。

| 项 | 内容 |
|---|---|
| **位置** | `Phylo/Algorithm/NJ.lean`（`def MaxZCherryCore : Prop`，`nj_cherry` 依赖它） |
| **陈述** | `(a,b)` 全局最大化 `z := δ + ℓ` ⟹ 对任意异于 `a,b` 的 `i,j`，`δ(a,b)+δ(i,j) ≤ δ(a,i)+δ(b,j)` 且 `≤ δ(a,j)+δ(b,i)` |
| **现状态** | 库里处理为**显式 `Prop` 假设**（不用 `sorry`），`nj_cherry` 表述为「假设硬核 ⟹ 樱桃引理」——诚实且可审计 |
| **数值证据** | 随机 4000 棵正权树（n=4..8），argmax `z` **恒为樱桃，0 反例** ⟹ 命题为真 |
| **缺口性质** | 形式化路径问题：标准证明都要「实现树」，而库内还没有 ⟹ **先做 T3** |

**已排除的朴素路线**（都有数值反例，别再试）：
1. 「最近距离对是樱桃」—— 假（1822 反例）；
2. 「局部 quartet `ui|vj` ⟹ `z(u,i) ≥ z(u,v)`」—— 假（局部信息不足，需全局耦合）；
3. 「`(u,v)` 非樱桃 ⟹ `∃m, z(u,m) > z(u,v)`」—— 假。

**推荐路线（路线 B）**：`FourPoint δ` ⟹（**T3**）实现树 `T` ⟹ 按 **Weller 2023「leaf-status」** 论证：
取中心节点 `c`、沿路径 leaf-status 单调、子树内必存在樱桃、递归到更大 `z` 的对 ⟹ 定理。
文献：Weller 2023 (arXiv:2305.18866)；Pachter–Sturmfels Thm 2.38；Mihaescu–Levy–Pachter 2006 (arXiv:cs/0602041)。

**已备好的代数骨架**（都在 `NJ.lean`，可直接用）：
`Q_eq_neg_two_ell`（最小化 Q ⟺ 最大化 z）· `two_mul_z`（`2z = S(i)+S(j)+(2-n)δ`）·
`z_hinge`（门控恒等式）· ★★ `four_point_z_iff`（`n≥4` 时「四点和最小」⟺「z 的和最大」——**z 最大性与 quartet 分裂的精确字典**）。

**解锁下游**：NJ 完整正确性、`Phylo/Stat/NJst.lean` 的完整一致性。

---

### T5 ★★ SVDQuartets 的**统计一致性**（正确性已完成）

> ⬆️ **已升为 T0.5，见上。** 保留原始记录供对照。

| 项 | 内容 |
|---|---|
| **位置** | `Phylo/Stat/SVDQuartets.lean`（258 行） |
| **已完成** | ★★★ **正确性**：`svdquartets_selects_true`（秩判据）+ **无条件版** `svdquartets_concrete`（分离性：`sepFreq c := c·[i=j][k=l]` 使错展平满秩） |
| **缺口** | **统计一致性**：SVDQuartets 实用的是**奇异值之和**（连续量），**不是秩**（秩下半连续，扰动下会跳） |
| **依赖** | `Mathlib/Analysis/InnerProductSpace/SingularValues.lean`；需给矩阵装上内积空间结构 |
| **工作量** | 中等偏大 |
| **策略提示** | 可复用 `Phylo/Stat/Stability.lean` 的通用引擎（`exists_gap` + `stable_argmax`）——**只要把「奇异值和最大」也表达成一个 `Finset` 上的得分函数**即可 |

**验收**：`svdquartets_statisticallyConsistent`，全库零 `sorry`。

---

### T6 ★ KF 距离（Kuhner–Felsenstein branch score）

| 项 | 内容 |
|---|---|
| **建议位置** | 新文件 `Phylo/Algorithm/KF.lean` |
| **定义** | 两棵树在**统一 split 集合**上边权的平方差之和（`Phylogram.w` 已有；`Split` 已有） |
| **依赖** | T2（把「边 → split」的构造打通，尤其非平凡内部边） |
| **验收** | 定义 + 基础性质（对称、非负、零 ⟺ 同拓扑同权）编译通过 |

---

### T7 ★ restriction `T|Y`（`suppress`，M4 欠账）

| 项 | 内容 |
|---|---|
| **位置** | `Phylo/Core.lean`（`inducedSubgraph` 已有，`suppress` 缺） |
| **现状** | 库里已有**替代定义**（split 层面 `Split.restrict`，`Phylo/Split.lean`）——**够用** |
| **工作量** | 大：要造新顶点类型 + 新图 + 三条结构证明（`IsTree` / `leaf_iff_degree_one` / `no_degree_two`） |
| **优先级** | **低**。除非 T1 的某条路线真的需要树层面的 restriction，否则不做 |

---

### T8 ★ NJst 完整一致性（等 T4）

> ⬆️ **已升为 T0.4，见上。** 保留原始记录供对照。

`Phylo/Stat/NJst.lean` 的 `njst_cherry` 只是**第一步**。完整一致性还缺**两条**：
1. `MaxZCherryCore`（T4）；
2. **NJ 的归纳正确性**：合并 cherry 后新距离矩阵**仍是树度量**（四点条件保持），从而可归纳。

> 备选路线（ADR 2016 真实走法）：把 NJst **归约到 generalized STAR**（clade 共识），
> 而 STAR 的一致性最终需要「**clade 系统决定树**」——**又回到 T1 那一类定理**。

---

### T9 ★ 可选新课题（老师点名「ML 和贝叶斯以外的经典工具」）

按「形式化难度 / 学术价值」排序，任选：

| 课题 | 内容 | 难度 |
|---|---|---|
| **NNI / SPR 邻域** 🔄 | NNI 图的连通性、树的直径、树空间（Robinson–Foulds 图上距离） | 中 |
| **最大简约的 NP-hard** | Foulds–Graham 归约（小简约问题 ⟹ 顶点覆盖） | 中高（需复杂度框架） |
| **四点点条件的等价刻画** | `FourPoint` ⟺ 「存在实现树」（即 T3 的另一半表述） | 高 |
| **quartet 距离** | `d_Q(T,T')` 的度量性质、与 RF 的不等式关系 | 中 |
| **长枝吸引** | Felsenstein zone 的定量刻画（需 MSC 概率层） | 高 |
| **UPGMA 的分子钟一致性** | 超度量数据下 UPGMA 恢复真树 | 中（依赖 T3/Dendrogram 已有） |

### T9.1 NNI 的现状（🔄 dsh 首轮做了定义层，**下一步很明确**）

**已做**（`Phylo/Algorithm/NNI.lean`，207 行）：`Split.nniParts` / `nniResolvent`（split 层 NNI 分解
`A|B → (A₁∪B₁)|(A₂∪B₂)`）+ `nniParts_zero/one` + `nniResolvent_sideA/sideB`。

**⬜ 下一步（文件里已写清思路，直接接）**：
1. ★★ `nniResolvent_compatible`：分解与母 split 相容。
   思路（文件 §⬜ 已给）：分解第二块 `A₂∪B₂ = (A\A₁)∪(B\B₁)` 落在 `B` 内 ⟹ 与 `A` 不交。
   所需假设：`s.sideA \ A₁ ⊆ s.sideB`、`s.sideB \ B₁ ⊆ s.sideB`。
2. ★★★ `nniResolvent_swap_incompatible`：同一母 split 的两个互补分解互不相容
   （叶层面：`{a,c}|{b,d}` 与 `{a,d}|{b,c}`）。取 `x ∈ A₂` 逐一击破四个「分侧不交」条件。
3. 树层操作 `nniT'`（真的构造第二棵树）+ NNI 邻域关系的对称性 + 局部相容性引理 +
   `QuartetDecidesTree` 的 NNI 证书。

> ⚠️ **注意**：`NNI.lean` 现在的 docstring 第 50–51 行**虚报**了上面 1、2 两项
> （把它们列进「本文件做到哪」，实际不存在）。接手时**先修正 docstring**（纪律 12），
> 或在真正证出后把 ★ 落实。

---

## 5. Lean 4 踩坑清单（**必读，能省很多时间**）

> 全部是本项目实测踩过的。原始记录见 `MEMORY.md` 各节末尾的「踩坑」。

### 5.1 致命级（会让证明无法完成）

1. **⚠️⚠️ `omega` 遇到 ℕ 减法会整体失效**（报 `omega could not prove the goal: No usable constraints found`）。
   把 `c = |V| - 1` 改写成 `c + 1 = |V|` 即可。**本项目的「坑王」，栽过两次。**
2. **⚠️ `Exists.choose` 不做 ι-归约**（`Classical.choice` 是公理）：
   `(⟨a, h⟩ : ∃ x, p x).choose = a` **不可 `rfl`**。
   ⇒ **改用结构字段**代替 `∃` + `choose`（例：`MSCFreq.q`），一切变成投影，可自由展开。
   **这是本项目最重要的设计决策之一。**
3. **⚠️ `T.graph.induce ↑(…)` 这类嵌套类型每次 `whnf` 都极贵**，`maxHeartbeats` 加大也救不回来。
   ⇒ 改 `abbrev` 让类型透明，或**直接在子类型上定义图**。

### 5.2 类型与实例

4. **structure 里匿名实例字段 `[Fintype V]` 写在 `V : Type*` 之后会报 `unexpected token ']'`**
   ⇒ 必须用**命名实例字段** `fintypeV : Fintype V` + `attribute [instance] Cladogram.fintypeV …`。
5. **`extends` 后不必重新注册实例**（沿 `toCladogram` 自动找到）；
   但 `attribute [instance] Phylogram.toCladogram` 会报错（返回值不是 type class）。
6. **`deriving DecidableEq` 与 `[DecidableEq α]` 参数冲突**（报「synthesized instance not definitionally equal」）
   ⇒ 手写实例：`decidable_of_iff (a.parts = b.parts) (eq_iff_parts a b).symm`（注意 `.symm` 方向！）。
7. **`Cladogram.{u, v} X` 宇宙必须显式**，否则 `Failed to infer universe levels`；
   `structure` 字段里的 `∀ S hS, ...` 也**必须带类型标注**。
8. **`decAdj` 用 `inferInstance` 会 `whnf` 超时** ⇒ 改 `Classical.decRel _`。
9. **`RootedTree X` 的顶点宇宙**：`RootedTree.{u,u} X` 必须显式（`LaminarVertex F : Type u`）。

### 5.3 记号与作用域

10. **`Σ` 是保留记号**，不能当变量名（用 `fam`）。
11. **`Laminar.lean` 整体在 `namespace Phylo` 里**；`Split` / `Cladogram` / `RootedTree` 在根 ⟹ 新文件需 **`open Phylo`**。
12. **`omit [Fintype X] [DecidableEq X]` 若变量真被引用** → `cannot omit referenced section variable`。
13. **`abbrev Topology S := Split ↥S` 会让 namespace 内的 `t.swap` 递归到自己** ⇒ 必须写 `Split.swap t`。

### 5.4 tactic 细节

14. **`rw [if_pos h]` 可能先作用到 RHS** ⇒ 用项模式 `exact if_pos (Prod.ext_iff.mp h)` 更稳。
15. **`let` 定义不能被 `simp only [def]` 展开，`if h : B ∈ F then ...` 可被 `dif_pos` 展开** ⇒ 用 `if` 版。
16. **`induction p` 会泛化依赖参数** ⇒ 用 `Walk.recOn` + 显式 `motive`。
17. **`rw` 链里 `mul_div_assoc` / `div_mul_cancel₀` 的方向**：`L * (Y/L) = Y` 用
    `rw [mul_comm, div_mul_cancel₀ _ hL]` 两步，比 `mul_div_cancel₀` 稳。
18. **`Finset.mem_image.mp` 后用 `obtain ⟨p, -, rfl⟩` 有时失败**（非归纳变量报错）⇒ 改 `obtain ⟨p,-,hp⟩` + `rw [← hp]`。
19. **ℝ 没有 `OrderBot`** ⇒ `Finset.sup` 不可用；用 `Finset.min'`（`LinearOrder` + `Nonempty`）。
20. **`Mathlib.Data.Real.Basic` 已弃用** ⇒ 改 `import Mathlib.Basic.Real.Basic`（否则只报 `OfNat ℝ 0` 失败，很难定位）。
21. **`Nat.one_ne_two` 不存在** ⇒ 用 `by decide`。
22. **`∃! p, P p` 的 `.choose_spec`** 类型是 `P choose ∧ (∀ y, P y → y = choose)`，唯一性在 `.2`，比 `ExistsUnique.unique` 省事。

### 5.5 工具链 / 环境

23. **Python 在 Windows 写文件默认 CRLF** ⇒ `check_file_imports.sh` 的 `grep "…$"` 失配误报「未 import」。
    **写 `.lean` 必须 `newline='\n'`**（或事后统一转 LF）。
24. **后台 bash 里 `curl` 抓不到 GitHub API 输出**（返回空），前台正常 ⇒ 查 CI 状态在前台跑。
25. **`native_decide`（`Parsimony.lean` 的 48 情形枚举）引入 `Lean.ofReduceBool` 信任假设** —— 已在文件中标注。
26. **⚠️ `fin_cases` 在 `Fin 2` 上产生的字面量不可归约**（dsh 首轮实测）：
    `fin_cases i`（`i : Fin 2`）把字面量写成 `(fun i => i) ⟨0, ⋯⟩`，与 `nniParts … 0` **无法 `rw` 匹配**，`simp` 也归约不动。
    ⇒ **必须**用 `by_cases hi : i = 0` + `subst hi`，让变量被换成真字面量。
    （替代：用 `Fin.cases` 定义函数，这样 `f 0` / `f 1` 都是 `rfl` —— `NNI.lean` 就用了这招。）
27. **⚠️ `h : Disjoint S T` 在 `rcases` 之后不能当函数用**（dsh 首轮实测）：
    `h hx hy` 报 `expected type ?m ⊆ …`（被误解析成 `LE.le`）。
    ⇒ **必须**写 `(Finset.disjoint_left.mp h) hx hy`；
    且注意 `Finset.disjoint_left.mp h : ∀ a, a ∈ S → a ∉ T`（**第一侧在前**）。

---

## 6. 工程约定与纪律（**不可破**）

1. **零 `sorry` 纪律**。未证明的命题写成**显式 `def … : Prop` 缺口**（惯例来自 `MaxZCherryCore` / `QuartetDecidesTree`），
   而不是 `sorry`。这样库始终可编译、依赖关系可审计。
   - 若不得已用 `native_decide`，**必须在 docstring 里标注信任假设**。
2. **文件头三件套**：
   ```lean
   /- Copyright (c) 2026 ASTER LAB. All rights reserved.
      Released under Apache 2.0 license as described in the file LICENSE.
      Authors: ASTER LAB -/
   import Mathlib.…
   /-! # `Phylo.Xxx` —— 一句话描述（文件级 docstring，中文写清「本文件做到哪、缺什么」）-/
   ```
3. **每个定义/定理带 docstring**（`/-- … -/`），★ 星级标注主结果（★ 辅 / ★★ 核心 / ★★★ 主定理）。
4. **新文件必须同步进根模块 `Phylo.lean`（按字母序）**，然后跑 `bash scripts/check_file_imports.sh` 验证。
5. **`.lean` 文件一律 LF 行尾**。
6. **注释与文档用中文**；Lean 标识符用英文。
7. **改定义前先查 `CONCEPTS.md` §3 的「已定方案」** —— 那是老师拍过板的，不要擅自改。
8. **commit 消息风格**：`模块名: 一句话（★ 星级）`，如 `Aho: a pairwise compatible split system is displayed by a tree`。
9. **只 commit 不 push**（除非老师明确说 push）；push 必须走 WSL（见 §1.4）。
10. **`Ω` 长跑策略**：老师希望「不需要他拍板的任务全部搞定」。遇到设计岔路时：
    **先查 `MEMORY.md` / `CONCEPTS.md` 是否已有先例 → 有则照做 → 没有则选「更容易形式化」的那条并记录理由**。
11. **`MEMORY.md` 只许追加**，严禁精简 / 回退 / 重写历史章节。—— **见开头「⚠️ 必读」节（完整说明 + 事故复盘）**
12. **docstring 里的 ★ 必须对应真实存在的声明**；未证明的一律落成显式 `def … : Prop` 缺口。—— 见开头「⚠️ 必读」节
13. **每批结束回写本文件**（就地更新，不要另写第二份交接文档）。—— 见 §7.5
14. **术语准确性：严格区分「形式化缺口」与「数学开放问题」。**
    ⚠️ 本库的 `MaxZCherryCore`（NJ）与 `QuartetDecidesTree` 都被写成显式 `Prop` 缺口，
    但**两者都是经典已证定理**（NJ：Studier–Keppler 1988 / Weller 2023；quartet 决定树：
    Colonius–Schultze 1981 / Steel 1992），**不是**数学开放问题。
    ⇒ 描述缺口时一律写「**形式化缺口 / 尚未形式化**」，**绝不写** "open problem" / "开放问题"。
    （2026-10-07 曾误写，已在 `MEMORY.md` / `NJ.lean` / `NJst.lean` / `CONCEPTS.md` 就地修正。
    误写会让接手方以为该方向无解而放弃，危害极大。）

---

## 7. 建议的执行节奏

> 🚀 **2026-10-07 13:10 更新（老师指示）**：把 T0 整批列为**最高优先级**。
> 原始证明已抓齐（`references/`），这批是**照抄证明**，不再是探索。

```
第 0 批（最高优先级）★ T0 —— 把 references/ 里的原始证明搬进 Lean
   │
   ├─ 0.0  T2   「内部边两侧各 ≥ 2 叶」（T0.1 收口的前置，机械但卡过 whnf 超时）
   │            ↓ 立刻
   ├─ 0.1  T0.1 ★★★★ QuartetDecidesTree（thin + transitive + saturated）
   │            ↑ transitive 库里已有；先做「对接口」：把三种条件接到 full quartet 系统
   │            ↓ 收口 → astral_iso / caster_iso / parsimony_iso 全部去假设化
   │
   ├─ 0.2  T0.2 ★★★ Buneman 存在性（照抄 Dendrogram 的「镶嵌族 ⟹ 树」模板）
   │            ↓ 立刻
   ├─ 0.3  T0.3 ★★★ MaxZCherryCore（照抄 Weller 2023 Lemma 1–3 + Thm 2）
   │            ↓ 立刻
   ├─ 0.4  T0.4 ★★ NJst 完整一致性（照抄 ADR 2016 Thm 4.1 + NJ 归纳正确性）
   │
   └─ 0.5  T0.5 ★★ SVDQuartets 统计一致性（可并行，独立）

后续（T0 完成后再做）：
   第 1 批：T6（KF 距离，等 T0.2 的 split 构造）
   第 2 批：T9 的 NNI 补全（`nniResolvent_compatible` / `_swap_incompatible`，思路已写好）
   第 3 批：T7（`suppress`，低优先级）
   余力：  T9 其余课题（SPR、NP-hard、长枝吸引…）
```

> 📌 **2026-10-07 实况**：dsh 首轮**跳过了 T2/T1，直接做了 T9 的 NNI**（产出合格但未按建议顺序）。
> **本轮起以 T0 为准**：若你选择偏离 T0 顺序，必须**在 §4 写明理由**（纪律 13 回写清单要求）。

**每轮结束的自检清单**：
- [ ] `wsl -e bash -lc 'cd ~/lean4phylo && ~/.elan/bin/lake build'` 通过（**3186 jobs 是当前基线，新增文件后会涨**）
- [ ] `bash scripts/check_file_imports.sh` 通过
- [ ] 全库 `grep -rn "sorry" Phylo/` 只命中注释
- [ ] **docstring 里的每个反引号标识符都能在本文件 `grep "^theorem\|^def"` 命中**（纪律 12）
- [ ] 新文件已加进 `Phylo.lean`
- [ ] commit（不 push，除非老师说）
- [ ] 更新 `MEMORY.md`（**只追加**，纪律 11）+ 更新 `HANDOVER.md`（§7.5，纪律 13）

---

## 7.5 每批结束**必须回写本文件**（纪律 13）

老师明确要求：**接手方每完成一批就更新 `HANDOVER.md`**，而不是另起炉灶写第二份交接文档。

**回写清单（逐项打勾）**：

- [ ] **头部快照**：`main` @ `<新 commit>` · `lake build` **<新 jobs 数>** · 文件数 / 行数 / 声明数 · **未推送 commit 数**
- [ ] **§2.1 表格**：本批新证出的算法/定理**加行**（写清主定理名 + 文件 + 是否无条件）
- [ ] **§2.2 表格**：新文件或行数变化
- [ ] **§3 瓶颈图**：已打通的瓶颈**标记完成**；新发现的瓶颈**加进图里**
- [ ] **§4 任务**：状态更新（`⬜` → `✅ 已完成` / `🔄 进行中`）；新任务追加为 `T10, T11, …`；
      **若某任务你决定不按建议顺序做**（例如先做 T9），**必须在此写明理由**
- [ ] **§5 踩坑**：本批新踩的 Lean 坑**追加**到对应小节（这是给后来者省时间的，务必写）
- [ ] **§8 参考文献**：新引用的文献补进表
- [ ] **§0 三十秒版本** + **开头「⚠️ 必读」节的事故记录**（若本批又有事故）

> ⚠️ **回写时的红线**：同纪律 11 —— 更新是**追加与就地修改状态**，**不是重写**。
> 尤其**不要删除「⚠️ 必读」节的事故复盘**（它是给后来者的警示）。

### 7.5.1 回写后头部应该长的样子

```
> **最后更新**：2026-10-08 03:20（dsh 第 2 批：T0.1 进行中，thin 已落地）
> **当前快照**：`main` @ `b7f3a12`，3189 jobs 通过，27 文件 / 6810 行 / 397 声明
> **未推送**：13 个 commit
```

并在 §4 的对应任务标题旁标 `🔄 进行中（2026-10-08）` 或 `✅ 已完成（2026-10-08）`。

---

## 8. 参考文献

> 📚 **本库已把各缺口对应的原始文献抓下来并转成可读 Markdown**：
> 见 **`references/README.md`**（缺口 → 出处速查表，带 md 内精确行号）。
> 下表是书目信息；**要读证明原文请用 `references/md/`**（若目录为空，用 `references/README.md` §7 的
> 复现命令重跑 —— 派生物因版权未入库）。

| 主题 | 文献 | `references/md/` |
|---|---|---|
| **quartet 决定树**（T0.1） | **Colonius & Schulze (1981)**；**Steel (1992)**；转述见 **Huber et al. (2017) Thm 6**、**Huber et al. (2018) Thm 1** | `HuberEtAl2017_*.md`、`Huber2018_*.md` |
| **NJ 樱桃引理**（T0.3） | **Studier & Keppler (1988)**；**Weller (2023)**；**Mihaescu–Levy–Pachter (2009)** | `Weller2023_*.md`、`MihaescuLevyPachter2006_*.md` |
| **四点条件 / Buneman 存在性**（T0.2） | **Buneman (1971)**；**Buneman (1974)** | `Buneman1971_*.md`、`Buneman1974_*.md` |
| **NJst 一致性**（T0.4） | **Allman–Degnan–Rhodes (2016), Thm 4.1** | `AllmanDegnanRhodes2016_*.md` |
| **SVDQuartets 可识别性**（T0.5） | **Chifman & Kubatko (2015)** | `ChifmanKubatko2015_*.md` |
| Splits-Equivalence / 树↔split | Semple & Steel, *Phylogenetics* (2003), §3.8；Buneman 1971 | 同上（Buneman） |
| 相容 ⟹ 树 | Aho, Sagiv, Szymanski, Ullman (1981) | 付费墙 |
| **多数共识** | Margush & McMorris (1981) | 付费墙 |
| quartet 距离 / display | Bryant & Steel (2001) | — |
| ASTRAL | Mirarab et al. (2014)；Sayyari & Mirarab (2016) | — |
| ASTRAL 一致性 | Shekhar, Roch, Mirarab (2018) | — |
| CASTER | Rabiee, Sayyari, Mirarab (2019) | — |
| parsimony 一致性 | Felsenstein (1978)；Roch & Steel (2015) | — |
| SVDQuartets（方法原文） | Chifman & Kubatko (2014) | 付费墙（PMC4296144） |
| NJst | Liu & Yu (2011) | — |
| NJ（原算法） | Saitou & Nei (1987) | 付费墙（其证明有误，见 Studier–Keppler） |
| UPGMA | Sokal & Michener (1958)；Mihaescu et al. | — |
| MSC | Kingman (1982) coalescent | — |

---

## 9. 快速上手：三条命令

```bash
# 看当前状态
cd /c/Users/ASTER/WorkBuddy/Project/lean/lean4phylo && git log --oneline | head -5 && wc -l Phylo/*.lean Phylo/*/*.lean | tail -1

# 同步 + 构建
wsl -e bash -lc 'cp -r /mnt/c/Users/ASTER/WorkBuddy/Project/lean/lean4phylo/Phylo/* ~/lean4phylo/Phylo/ && cd ~/lean4phylo && ~/.elan/bin/lake build'

# 改完一个文件后的秒级验证
wsl -e bash -lc 'cd ~/lean4phylo && ~/.elan/bin/lake env lean Phylo/Stat/QuartetDecides.lean'
```

**祝你跑得久。有问题先翻 `MEMORY.md` —— 那里面大概率已经有人踩过了。**
