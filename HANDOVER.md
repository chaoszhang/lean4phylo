# HANDOVER.md —— `lean4phylo` 交接文档

> **生成时间**：2026-10-07 10:20（Asia/Shanghai）
> **面向**：接手继续长时自主执行的 agent（下文称「你」）
> **当前快照**：`main` @ `8d26030`，**3185 jobs `lake build` 通过**（WSL 增量 8s），**库内零 `sorry`**
> **规模**：26 个 `.lean` 文件 / **6553 行** / **384 个顶层声明**
> **未推送**：`origin/main` 落后 11 个 commit（老师指示「途中只 commit 不 push」）

---

## 0. 三十秒版本

**这是什么**：一个用 Lean 4 + Mathlib 形式化**系统发生学（phylogenetics）经典算法**的库，库名 `Phylo`，仓库 `lean4phylo`。目标不是「证明某个大定理」，而是**一个可长期积累的算法正确性库**。

**已经做完的**：树/分裂/quartet 三层的定义与基础定理；**Splits-Equivalence 两个方向**（树 ⟹ 相容、相容 ⟹ 存在树）；Aho–Buneman 建树；多数共识树；UPGMA 结构定理；cherry 存在性；RF 距离度量性；二叉树计数与 quartet 唯一性；以及 **ASTRAL / CASTER / parsimony 三者的 quartet-MSC 统计一致性** 与 **SVDQuartets 的正确性**。

**现在卡在哪**：**一个共享缺口**——`QuartetDecidesTree`（「两棵 binary 树 quartet 系统相同 ⟹ 同构」）。它是 4 个算法从「逐 quartet 一致」升级到「同构」的最后一步，也是逆否路线（老师 2026-10-07 定的）的收口点。围绕它还有 **3 个硬骨头**（见 §3）。

**你的第一件事**：读 §2 确认「已完成，别重做」，然后从 **T1 / T2** 开始（见 §4 的执行顺序建议）。

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

> **一句话总结给老师看的**：**ASTRAL、CASTER、parsimony、SVDQuartets 四个算法的核心正确性已经形式化**；NJst 拿到第一步；NJ 拿到全部代数骨架但硬核仍是 open problem。

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
| `MEMORY.md`（66KB，680 行） | **工作日志**：每轮的进展、踩坑、决策。**改动前必查**——很可能有人已经试过并失败了。 |
| `CONCEPTS.md`（76KB，1003 行） | **概念设计**：每个定义的选择理由（§3.1–§3.11 的「已定方案」）+ 文献先例。**不要重新发明定义。** |
| `DESIGN.md` | 库设计：Mathlib 现状实测表 / 分层架构 / 决策 D1–D4 |
| `SCAFFOLD.md` | 工程骨架与四条实践（文件头规范、docstring、根模块同步、linter） |
| `README.md` | 环境搭建 |

---

## 3. 三处共享瓶颈（一张依赖图）

```
                    ┌──────────────────────────────────────┐
                    │  T2  「内部边两侧各 ≥ 2 叶」          │  ← 基础设施，最该先做
                    │      (SideSubtree 阶段 2)             │
                    └───────────────┬──────────────────────┘
                                    │
       ┌────────────────────────────┼────────────────────────────┐
       ▼                            ▼                            ▼
┌──────────────┐          ┌──────────────────┐         ┌──────────────────┐
│ T1           │          │ T6 KF 距离        │         │ T1 第 1 步        │
│ QuartetDecides│         │ (需要 split 构造) │         │ split 系统极大性   │
│ Tree          │◄─────────┤                  │         │                  │
└──────┬───────┘          └──────────────────┘         └──────────────────┘
       │ 解锁
       ▼
┌──────────────────────────────────────────────────────┐
│ astral_iso / caster_iso / parsimony_iso   （已写好，  │
│ 只等 QuartetDecidesTree 从 def 变 theorem）           │
└──────────────────────────────────────────────────────┘

独立支线：
┌──────────────────┐     ┌──────────────────┐
│ T3 Buneman 存在性 │────►│ T4 MaxZCherryCore │───► NJ / NJst 完整正确性
│ (四点条件⟹实现树) │     │ (open problem)    │
└──────────────────┘     └──────────────────┘

可独立推进：
┌──────────────────┐     ┌──────────────────┐
│ T5 SVDQuartets    │     │ T7 restriction    │
│ 统计一致性(非正确性)│    │ T|Y (suppress)    │
└──────────────────┘     └──────────────────┘
```

---

## 4. 剩余任务（按建议执行顺序编号）

### T1 ★★★ 头号目标：把 `QuartetDecidesTree` 从缺口变成定理

| 项 | 内容 |
|---|---|
| **位置** | `Phylo/Stat/QuartetDecides.lean:59`（现在是 `def QuartetDecidesTree (X) : Prop := ...`） |
| **陈述** | 两棵 **binary** cladogram `T, T'`，若逐 4-元集上展示的 quartet 一致（模 `swap`），则 `T ≅ T'` |
| **交付** | 把 `def` 换成 `theorem`（或新证 `theorem quartetDecidesTree`，`def` 保留作别名） |
| **文献** | Steel 1992；Colonius–Schultze 1981 |
| **为什么 binary 不可去** | polytomy refine 成 binary 不改任何 quartet ⟹ 反例 |

**老师定的逆否路线**（`T ≇ T'` ⟹ 存在不兼容 split ⟹ 存在不兼容 quartet）：

1. **`T ≇ T'` ⟹ 存在 `s ∈ Σ(T)` 与 `Σ(T')` 不相容**
   —— 等价于 **binary 树 split 系统的极大性**（库内**尚无**）。
   标准证法：若 `s` 与 `Σ(T)` 全相容，则 `Σ(T) ∪ {s}` 相容 ⟹ 由 Aho(`compatible_exists_rootedTree`) 得树 `T''` ⟹ `T` 是 `T''` 的**收缩** ⟹ `T` 有度 ≥ 4 顶点，与 binary 矛盾。
   ⇒ **需要 refinement / contraction 理论**（`T''` 收缩到 `T`、`Σ` 随收缩单调）。
2. **不兼容 split ⟹ 同一 4-叶集上两个不同 quartet** —— ✅ **已做完**！
   `Phylo/Binary.lean` 的 ★★★ `exists_restrict_ne_of_incompatible`（配合 `exists_four_of_incompatible`）。
3. **收口**：把第 2 步的「两个不同 quartet」与假设「逐点一致（模 swap）」对撞。

**顺带可做的替代路线**（可能更短）：
走 `Laminar.toRootedTreeOfCard` —— 「`Σ(T) = Σ(T')` 的 binary 树 ⟹ 由 split 系统唯一决定」。
库里 `splitOf` / `isSplitOf_splitOf` / `splitOf_mem_splits` 已经把「split ↔ 规范簇」的字典打通，
第 3 步只差「两棵树有同样的 split 系统 ⟹ 同构」（Splits-Equivalence 的**同构版本**）。

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

### T3 ★★★ Buneman 存在性（四点条件 ⟹ 存在实现加权树）—— 独立大定理

| 项 | 内容 |
|---|---|
| **建议位置** | 新文件 `Phylo/Buneman.lean` |
| **陈述** | `Dissimilarity.FourPoint δ ⟹ ∃ (加权树 T), ∀ i j, δ i j = T.dist (leaf i) (leaf j)` |
| **为什么是大定理** | 这是「相容 ⟹ 存在树」的**度量版**；库里已有 `Phylogram.dist`（唯一路径边权和）可直接当 RHS |

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

### T4 ★★★ `MaxZCherryCore`（NJ 硬核，**open problem**）

| 项 | 内容 |
|---|---|
| **位置** | `Phylo/Algorithm/NJ.lean`（`def MaxZCherryCore : Prop`，`nj_cherry` 依赖它） |
| **陈述** | `(a,b)` 全局最大化 `z := δ + ℓ` ⟹ 对任意异于 `a,b` 的 `i,j`，`δ(a,b)+δ(i,j) ≤ δ(a,i)+δ(b,j)` 且 `≤ δ(a,j)+δ(b,i)` |
| **现状态** | 库里处理为**显式 `Prop` 假设**（不用 `sorry`），`nj_cherry` 表述为「假设硬核 ⟹ 樱桃引理」——诚实且可审计 |
| **数值证据** | 随机 4000 棵正权树（n=4..8），argmax `z` **恒为樱桃，0 反例** ⟹ 命题为真 |

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
| **NNI / SPR 邻域** | NNI 图的连通性、树的直径、树空间（Robinson–Foulds 图上距离） | 中 |
| **最大简约的 NP-hard** | Foulds–Graham 归约（小简约问题 ⟹ 顶点覆盖） | 中高（需复杂度框架） |
| **四点点条件的等价刻画** | `FourPoint` ⟺ 「存在实现树」（即 T3 的另一半表述） | 高 |
| **quartet 距离** | `d_Q(T,T')` 的度量性质、与 RF 的不等式关系 | 中 |
| **长枝吸引** | Felsenstein zone 的定量刻画（需 MSC 概率层） | 高 |
| **UPGMA 的分子钟一致性** | 超度量数据下 UPGMA 恢复真树 | 中（依赖 T3/Dendrogram 已有） |

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

---

## 7. 建议的执行节奏

```
第 1 批（1–2 轮）：T2  → 把「两侧各 ≥ 2 叶」打下来（基础设施）
                      ↓ 立刻
第 2 批（2–4 轮）：T1  → QuartetDecidesTree（第 1 步需要 refinement/contraction）
                      ↓ 收口
                      astral_iso / caster_iso / parsimony_iso 全部去假设化
                      ↓
第 3 批（并行）：    T5（SVDQuartets 统计一致性）或 T6（KF 距离）
                      ↓
第 4 批（长线）：    T3 → T4（Buneman → NJ 硬核），风险最高，放最后
                      ↓
余力：              T9 的可选课题（NNI/SPR、NP-hard）
```

**每轮结束的自检清单**：
- [ ] `wsl -e bash -lc 'cd ~/lean4phylo && ~/.elan/bin/lake build'` 通过（**3185 jobs 是当前基线，新增文件后会涨**）
- [ ] `bash scripts/check_file_imports.sh` 通过
- [ ] 全库 `grep -rn "sorry" Phylo/` 只命中注释
- [ ] 新文件已加进 `Phylo.lean`
- [ ] commit（不 push）
- [ ] 更新 `MEMORY.md`（追加当轮进展 + 踩坑）

---

## 8. 参考文献

| 主题 | 文献 |
|---|---|
| Splits-Equivalence / 树↔split | Semple & Steel, *Phylogenetics* (2003), §3.8；Buneman 1971 |
| 相容 ⟹ 树 | Aho, Sagiv, Szymanski, Ullman (1981) |
| 多数共识 | Margush & McMorris (1981) |
| quartet 决定树 | Steel (1992)；Colonius & Schultze (1981) |
| quartet 距离 / display | Bryant & Steel (2001) |
| ASTRAL | Mirarab et al. (2014)；Sayyari & Mirarab (2016) |
| ASTRAL 一致性 | Shekhar, Roch, Mirarab (2018) |
| CASTER | Rabiee, Sayyari, Mirarab (2019) |
| parsimony 一致性 | Felsenstein (1978)；Roch & Steel (2015) |
| SVDQuartets | Chifman & Kubatko (2014)；Allman, Degnan, Rhodes (2016) |
| NJst | Liu & Yu (2011)；**Allman–Degnan–Rhodes 2016 (arXiv:1604.05364) Thm 4.1** |
| NJ | Saitou & Nei (1987)；Studier & Keppler (1988)；**Weller 2023 (arXiv:2305.18866)**；Mihaescu–Levy–Pachter 2006 (arXiv:cs/0602041) |
| UPGMA | Sokal & Michener (1958)；Mihaescu et al. |
| MSC | Kingman (1982) coalescent |

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
