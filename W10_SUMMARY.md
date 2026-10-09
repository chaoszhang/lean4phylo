# W10 总结 —— 把**溯祖理论本体（Kingman coalescent）**从论文形式化进 `lean4phylo`

> 派单：`../DISPATCH.md` §一（W10a–W10j）｜规格：`W10_COALESCENT_SPEC.md`｜
> 执行：**协调侧 ＋ 8 个并行子 agent**，每个交付由**协调侧独立复核**（md5 / 编译 / 全量 guard / 数值穷举）
> ｜过程记录：`HANDOVER.md`（第 87 批）＋ `MEMORY.md`（第 91–106 批，42 条教训）
> ｜**只 commit，不 push**。

> ## 🆕 后续（2026-10-09，老师裁决后）：**空结构已删除，修正版升为规范版**
>
> 本报告 §2 记录的「四条采样公理全是空类型」的处置，老师已定为 **彻底清理**：
> * 四个空结构（`MSCSampling` / `USTARSampling` / `CASTERSampling` / `SiteSampling`）
>   与旧谓词 `StatisticallyConsistent` **就地改回正确形状**（`emp` **依赖真实律/模型**），
>   并各配 `*_nonempty` 显式居民；
> * 七条「空洞」定理（`astral_statisticallyConsistent` / `njst_statisticallyConsistent` /
>   `caster_statisticallyConsistent` / `caster_greedy_consistent` /
>   `caster_statisticallyConsistent_iso` / `parsimony_statisticallyConsistent` / `parsimony_iso`）
>   由修正版**接管同名**（证明逐字相同），**全部非空洞**；
> * `Phylo/Stat/SamplingAxiomVacuity.lean`（含空性证明与 `*SamplingLaw` 修正版）**整文件删除**；
>   树层定理并入 `Phylo/Stat/QuartetDecides.lean`（`astral_statisticallyConsistent_iso`）。
> ⇒ 库内**不再残留任何「空洞」物件**。下文 §2 保留为当时的发现记录（其中的 `*Law` 名字已不存在）。

---

## 0. 一句话结论

**「n-溯祖 = 跳链（有限组合）⊗ 独立指数」这条分解已经在 Lean 里成立，并且它把 MSC 的公理
一条条换成了定理**；同时**发现在本库原先的写法下，四条「统计一致性」定理其实全是空洞的**，
四条都给了修正与非空洞性证明。

---

## 1. 最终链条（每一步都是 Lean 里可引用的定理）

```
W10a  跳链 (2.1) 转移 ＋ (2.2) 绝对概率       KingmanJumpChain.lean（1390 行，验收①②③全收口）
  ↓   层间一致性（索引双射）· 归一化（倒向归纳）· 概率质量函数等价物
W10b  逗留时间 τ_k ~ Exp(d_k) ＋ Theorem 1     KingmanCoalescent.lean（真 IndepFun ＋ 两个边缘）
  ↓   (1.7) 密度 / 生存函数接库内 survival / E[τ_k] = 1/d_k
接合  跳链律 ⊗ 独立指数                        KingmanLaw.lean（把 μ 实例化成 (2.2) 的跳链律）
  ↓
W10c  MSC quartet 分布 ⇒ majorizes 是**定理**   MSCProof.lean（Fin 4 实例 → 任意 X）
  ↓   M1 升到**测度层** ⇒ 根部 1/3 = **跳链质量**   MSCMeasure.lean ＋ RootJumpMass.lean
  ↓
W10d  Etemadi 强大数定律 ⇒ 整张表 a.e. 收敛     EmpiricalConvergence.lean ＋ MSCSamplingAE.lean
  ↓   公理被数据 **a.e. 实现** ⇒ quartet 层 ⇒ **树层** a.e. 一致性（Iso）
```

**旁支子批**：W10e `DegnanSalter`（`p_uv(T)` 引擎）· W10f `SplitProbabilities`（ADR2017 的 `1/3` 阈值）·
W10g `Identifiability`（ADR2011 枝长可识别 ＋ **单调性**）· W10h `ReciprocalMonophyly`（ZDS2011 clade/clan）·
W10i `RankedGeneTree`（Stadler–Degnan ranked）· W10k `CoalescentStats`（经典统计量）。

**顺带补掉/新增**：`TrivialSplitCount`（缺口 G1：平凡 split 计数 `= 2n`）·
`CoalescentHistoryCount`（**一般 `n`**：`|RankedTree n| = H_n`，纯内核）·
`FiveTaxonLemma4`（**ADR2011 Lemma 4**：5 taxa 的 15 个无根拓扑**等概率**）·
**`KingmanStep`（跳链「一步去向计数」`= C(k+1,2)`，(2.1) 的正向语句，结构路线）**。

---

## 2. ★★★★ 头条发现：本库**四处采样公理全是空类型**

`MSCSampling`（`MSC.lean`）· `USTARSampling`（`NJst.lean`）· `CASTERSampling`（`CASTERTheorem1.lean`）·
`SiteSampling`（`Parsimony.lean`）**形状完全相同**：

```lean
emp : ℕ → 数据                    -- ← 不依赖真实模型
converges : ∀ 模型, ∀ ε > 0, ∃ N, ∀ n ≥ N, Close (emp n) (理论值) ε
```

⇒ 只要有两个模型（`CASTER` 侧甚至只要**两张权重表**）不同，要求即**自相矛盾** ⇒ 结构**空**
⇒ 被它支撑的四条一致性定理（`astral_` / `njst_` / `caster_` / `parsimony_`）**空洞成立**。

**处理**（`SamplingAxiomVacuity.lean`，511 行，＋四个现场文件的 🔴 docstring 警告）：

| 交付 | 内容 |
|---|---|
| **判据** | `not_nonempty_mscSampling_of_freq_ne`（一般 `X`）、`not_nonempty_ustarSampling_of_ne`、`not_nonempty_casterSampling_of_ne`、`not_nonempty_siteSampling_of_ne` |
| **实例** | `Fin 4` 上**无条件**两处：`MSCSampling`（用 `t = 1, 2` 两条律）、`CASTERSampling`（两张常值权重表） |
| **加强** | `not_statisticallyConsistent_of_tree_ne`：**旧谓词本身永假**（与结构是否为空无关） |
| **修正** | 四个 `*SamplingLaw`（`emp` **依赖真实模型**） |
| **非空洞性** | 四个 `*_nonempty`（显式居民，理想样本） |
| **修复定理** | 四条 `*_statisticallyConsistent_law`（**证明逐字相同**）＋ **两处树层**：`astral_statisticallyConsistentLaw`（落在库的 `StatisticallyConsistentLaw` 上）、`parsimony_iso_law`（落在 `Iso` 上） |
| **回归护栏** | `W10Probe.lean` ⑬⑯ 断言「旧结构仍是空的」——若有人「修好」它，护栏立刻报警 |

**公理被数据实现**（`MSCSamplingAE.lean` §4）：
★★★ `exists_mscSamplingFixed_ae`（a.e. 事件上经验频率表**就是**那个结构的居民）
→ `astral_statisticallyConsistent_ae`（quartet 层 a.e.）→ ★★★ `astral_iso_ae`（**树层 `Iso`**）。
⇒ **「统计一致性」这条叙事，在概率空间里、在树层、把公理去掉之后的形态已经成立**；
剩下的**唯一**假设是 iid 模型本身（Mathlib 无 `Measure.infinitePi`）。

---

## 3. 四条**规格/文献勘误**（三条是执行 agent 抓出来的）

| # | 位置 | 问题 | 处理 |
|---|---|---|---|
| ① | `W10_COALESCENT_SPEC.md` §1.7 | `\|B\| = 4` 写了 `36`，实为**无序**和（有序是 `72 = 4!·3`） | 改写并标注 |
| ② | `references/md/DegnanSalter2005_*.md` 式 (1)（393–421 行） | **OCR 损坏**（`−`→`(cid:53)`、`∑`→`O`），按它读**不满足归一化** | 改用 **PDF** 重提取，定义写成**部分分式/Sylvester** 形式（正确性由 `ΣP_k = I` ＋ ODE 特征关系背书） |
| ③ | `references/md/ZhuDegnanSteel2011_*.md` Lemma 4.4（389 行） | 印的**范围** `k = a+b ≤ n` 在 `k = n` 时**不等于真值** | 限定 `k < n`，`qn` 改用 Lemma 4.3 |
| ④ | `W10_COALESCENT_SPEC.md` §11.3 | **我举的例子**「给定拓扑 ranked 树数 `= (n−1)!`」**是错的**（`n = 3` 反例） | agent 穷举证伪后改用论文 **Remark 6** 的 `(n−1)!/∏(c_i−1)` |

⇒ 教训：**「文献要逐字抄」之外还要「抄完用穷举验一遍」**；`references/md/` **不是**地面真值，PDF 才是。

---

## 4. 验收（**复核方式可复现**）

```bash
# 1) 全量构建 + 零 sorry/axiom + 两个脚本（必须串行，见下面提醒）
~/w10/withlock.sh /tmp bash scripts/guard_batch.sh 3825 <要抽查的声明名…>

# 2) 14 个精确复核脚本（动态扫描，无 Monte Carlo）
bash scripts/msc/run_all.sh

# 3) 反空真探针（**24** 条 example，需先 lake build Phylo）
~/w10/withlock.sh <镜像> ~/.elan/bin/lake env lean scripts/msc/W10Probe.lean
```

**实测**：guard **全绿**（job 数 **3531 → 3825**）· `#print axioms` **只有**
`[propext, Classical.choice, Quot.sound]` · **零 sorry / 零 axiom / 零 `native_decide`** ·
14 个脚本**全 PASS** · 探针 **0 字节**（24/24）。

⚠️ **构建提醒**：`FiveTaxonLemma4` 的内核 `decide` 实测 **~172 s / `MAXRSS` ~6.9 GB**
（WSL 上限 ~8 GB，余量 ~1 GB）⇒ **整库 `lake build Phylo` 变重，且不能并发编译**
（并发会被 OOM 杀，报 `exit code 137`）。

---

## 5. 已知缺口与后续方向（**都写成了可检查的形态**）

| 缺口 | 位置 | 只差什么 |
|---|---|---|
| 一步联合律的**测度层**边缘等式 `jumpMeasure_step_gap` | `KingmanLaw.lean` | **只剩簿记**：两个边缘的**实数层算术都已具备**（左 `KingmanLaw.sum_targets_jumpWeight`、右 `KingmanStep.sum_parents_partitionProb`，另有 `KingmanStep.card_mergeTargets_cast` 的去向计数）；差的只是 `Measure.sum_apply` / `ENNReal.ofReal` 的搬运。`jumpStepLaw` 与 `pairMeasure` **已定义** |
| ~~轨迹律：`mergeTargets_gap`~~ | ~~`KingmanLaw.lean`~~ | ✅ **已证** —— 且**两条独立内核证明**（`KingmanLaw` 走 `Nat` 除法算术、`KingmanStep` 走 `ℝ` cast） |
| `pUV_normalization`（一般 `n`） | `DegnanSalter.lean` | 系数恒等式 `Σ_v c(u,v,k) = δ_{ku}`（= `Σ_k P_k = I` 的一行） |
| `rankedFiberCount_gap` / `sd2012_eq4_uniform_rates_gap` / `ranked4_probability_gap` | `RankedGeneTree.lean` | 论文 Remark 6 的一般 `n`；式 (4) 的一般 `m`；`n = 4` 的概率表 |
| 一般 `n` 的 MSC gene tree 分布 | — | **W10e/f/h 三个缺口共同的根** |
| `R_t = S_{D_t}` | `KingmanLaw.lean` | 连续时间死亡过程（本库无 CTMC） |
| W10j（贝叶斯 MSC / AGT） | — | 派单标「可延后」，**未做** |

---

## 6. 规模（**截至 2026-10-09 08:20**；计数值易变，以 `git log` 为准）

* **46 个 commit**（`c3c82aa` … `1455a86`，**只 commit 未 push**）；
* **20 个新模块**；全库 **91 个 `.lean` 文件 / 40612 行**；
* 全量 job 数 **3531 → 3825**；
* 新增复核资产：**14 个精确脚本** ＋ **24 条探针 example** ＋ README 一览表。

> ⚠️ **本节的计数带时间戳是有意的**：本批已经**三次**出现「文档里的计数立刻过期」
> （job 数 3538/3539/3540 的预计值 · README 的脚本数 4 vs 14 · 探针 22 vs 24）。
> **教训**：文档里的**计数**要么**带时间戳**，要么**干脆不写**（说「见 `git log`」）。
