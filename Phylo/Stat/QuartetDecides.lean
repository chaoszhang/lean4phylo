/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.Stat.CASTER
import Phylo.Stat.Parsimony
import Phylo.Stat.NJst

/-!
# `Phylo.Stat.QuartetDecides` —— 收口缺口：**quartet 系统决定 binary 树**

四个算法（ASTRAL / CASTER / parsimony / NJst）的统计一致性都已证到
**「输出与真树在每个 4-元集上一致」**。要把它升级为 **「输出与真树同构」**，
只需最后一条定理：

> ★★ **`QuartetDecidesTree`**：两棵 **binary** cladogram 若有相同的 quartet 系统，则同构。

✦ **定性（重要，勿误传）**：这**不是学术开放问题** —— 它是 **Colonius–Schultze (1981)**
与 **Steel (1992)** 的**经典定理**，教科书 Semple & Steel, *Phylogenetics* (2003) §6.4 有完整叙述。
本库把它写成缺口，**只是尚未形式化**，不是数学未解。

（**binary 假设不可去**：polytomy 会产生反例 ——
把多叉顶点 refine 成 binary 不改变任何 quartet。）

## 为什么它仍是缺口

本文件按库里 `MaxZCherryCore`（`Phylo/Algorithm/NJ`）的既有惯例，
把这条**经典但尚未形式化**的定理写成**显式 `Prop` 缺口**，而不是 `sorry` ——
于是「零 `sorry`」保持，且依赖关系**清晰可审计**。

**这是「形式化缺口」而非「数学开放问题」** —— 定理本身已证（1981/1992），
证明思路也是已知的，只是工作量较大。

**证明路线（已知，非探索性）**：

1. **边的叶侧**：binary `T` 的每条内部边 `e`，两侧各含 `≥ 2` 个叶
   （`deg = 3` ⟹ 除 `e` 外的两个方向各有叶）；
2. **见证 quartet**：`e` 的叶侧 `A|B` 由「被 `e` 分离的 4-元 2|2 划分」见证；
3. **恢复 split**：由 `q ≈ q'` 得 `Σ(T) = Σ(T')`（用 Colonius–Schultze 推理规则，
   库里**已有** `Cladogram.displaysQuartet_of_displaysQuartet_common`）；
4. **由 split 系统重构**：binary 树由 `Σ(T)` 唯一决定（Steel；或接 `Phylo.Laminar`
   的 `toRootedTreeOfCard` + Buneman 存在性）。

第 1 步需要「树的分量 / 诱导子图 / 叶存在性」的基础设施层，这是**尚未建立**的部分
（`Phylo/SideSubtree.lean` 已做阶段 1）。

## ✅ 进展（2026-10-08）

* **第 1 步已完成**：`Phylo/InternalEdge.lean` 的 ★★ `two_le_card_sideLeaves` /
  `two_le_card_sideLeaves_both`（= HANDOVER 的 **T2**）。
* **第 2 步已完成**：同文件的 ★★ `exists_displaysQuartet_of_internalEdge` ——
  每条内部边都有 quartet 见证。
* **⬜ 剩**：接线 —— 把「`QuartetTree` 逐点一致」过渡到 `SameQuartetSystem`，并补
  「split 系统相同 ⟹ 树同构」这一步。
  ⚠️ 已就位的零件（**均已无条件证出**，此处只是**尚未接线**）：
  ★★★ `Cladogram.isClade_iff_isClan_of_isBinary`（clade 刻画 = T0.1 第 3 步），
  其上游 `BinarySplitsMaximal`（`Phylo/InternalEdge.lean:937` 的 `def`）已由
  `Phylo/SplitsMaximal.lean` 的 `binarySplitsMaximal` **无条件**证出；
  以及 ★★★ `compatible_of_sameQuartetSystem`（quartet 系统相同 ⟹ `Σ(T) ∪ Σ(T')` 两两相容）。

## 下游收口

* ★★★ `astral_iso` —— ASTRAL 输出与真树**同构**（假设缺口成立）；
* ★★★ `parsimony_iso` / `caster_iso` —— 同理。
-/

universe u v

variable {X : Type u} [Fintype X] [DecidableEq X]

/-- ★★ **（缺口，显式假设）quartet 系统决定 binary 树**。

✦ **经典已证定理，本库尚未形式化**（**非**学术开放问题）。

**陈述**（**T0.6 之后的形状**）：两个 `QuartetTree` `qt, qt'`（各自带**真 `2|2`** 的字段
`q_card` 与 `displays`），若其底层树皆 binary 且逐点一致（模 `swap`），
则 `Nonempty (Iso qt.tree qt'.tree)`。

**文献**：Colonius & Schulze (1981), *Tree structures for proximity data*；
Steel (1992), *The complexity of reconstructing trees from qualitative characters and subtrees*；
教科书 Semple & Steel, *Phylogenetics* (2003) §6.4（full 情形的完整推理系统）。

**为什么 binary 不可去**：若 `T` 有 polytomy（内部度 `≥ 4`），把它 refine 成 binary 得到
`T'`，则 `q = q'` 但 `T ≇ T'`。

## ⚠️ 修正记录（2026-10-08）：旧陈述**是假命题**；已由 **T0.6 治本**

**本命题的旧版本（没有 `2|2` 假设）是假命题**，反例（`X = {1,2,3,4}`）：

* `T` = 唯一内部 split 为 `{1,2}|{3,4}` 的 binary 树；
* `T'` = 唯一内部 split 为 `{1,3}|{2,4}` 的 binary 树（两者显然**不同构**，
  因为 `Iso` 保标号、故保 split 系统，见 `Phylo/Core.lean` 的 `Iso.leaf_compat`）；
* 令 `q` 为**常函数**，把唯一的 4-元集 `S = {1,2,3,4}` 送到 `↥S` 上的 **1|3** split
  `{1} | {2,3,4}`，并取 `q' := q`。

`DisplaysSplitOn S q` 只要求存在 `T` 的某条 split `s` 使 `q.sideA = {x ∈ S : x ∈ s.sideA}`
—— 取 `s` = `T` 的**平凡 split** `{1}|rest` 即可（`Cladogram.sideLeaves_leaf_edge`），
`T'` 同理。于是四条假设全部成立（`q = q'` 甚至不需要模 `swap`），
但结论 `Nonempty (Iso T T')` 为**假**。

**根源**：`QuartetChoice` 只要求 `Split ↥S`，而 `Split ↥S` 的两侧只须非空 —— `1|3` 也算。
「quartet」按定义必须是 `2|2`。

### ✅ 收口（**T0.6**，2026-10-08）：`2|2` 升为 `QuartetTree` 的**字段**

当时的治标补丁是「给本命题多加一条 `2|2` 合取项」，并让 `astral_iso` / `caster_iso` /
`parsimony_iso` 各自多传一条 `2|2` 假设（在旧陈述下那条假设**不可满足**，
故三条定理当时是**空真**的）。**现已治本**：

* `Phylo/Stat/MSC.lean` 的 `QuartetTree` 新增字段 ★ `q_card`
  （`∀ S hS, (q S hS).sideA.card = 2`）；`MSCFreq` 经 `extends` **自动继承**；
* `Phylo/Stat/Parsimony.lean` 的 `MSCSite` 同步新增 `q_card` 字段，
  `MSCSite.asQuartetTree` 相应补上该坐标；
* ⇒ 本 `def` **改收 `QuartetTree`**（而非裸 `QuartetChoice`）：那条 `2|2` 合取项
  不再需要（它就是 `qt.q_card`），`qt.displays` / `qt'.displays` 亦然；
* ⇒ 三条 `iso` 定理的 `2|2` 显式假设**已全部删除**。

✦ **改陈述的反例审查**（本项目纪律：改陈述前先造反例）：

* 新形状下 `q`、`q'` **都必须**带 `q_card`，故旧反例里的常函数 **`1|3` 选法不再可表达**
  ⇒ 旧反例失效；
* 对 binary 树，「被展示的 `2|2` split 在 4-元集上模 `swap` 唯一」
  （`Phylo/QuartetUnique.lean` 的 ★★★ `displaysSplitOn_unique`）⇒ 新形状**恰是**
  经典定理（Colonius–Schulze 1981 / Steel 1992）的忠实形式
  —— 两棵树「逐点一致」正是「quartet 系统相同」；
* `|X| ≤ 3` 时两侧假设自动空真，结论退化为「≤3 叶的 binary 树唯一」——
  这与**旧陈述完全相同**，不是本次改动引入的新风险。 -/
def QuartetDecidesTree (X : Type u) [Fintype X] [DecidableEq X] : Prop :=
  ∀ (qt qt' : QuartetTree.{u, v} X),
    qt.tree.IsBinary → qt'.tree.IsBinary →
    (∀ (S : Finset X) (hS : S.card = 4),
      qt.q S hS = qt'.q S hS ∨ qt.q S hS = (qt'.q S hS).swap) →
    Nonempty (Iso qt.tree qt'.tree)

open Classical in
/-- 「逐 quartet 一致」（模 `swap`）关系**对称**。 -/
theorem agreesWith_symm {q q1 : QuartetChoice X}
    (h : ∀ (S : Finset X) (hS : S.card = 4), q S hS = q1 S hS ∨ q S hS = (q1 S hS).swap) :
    ∀ (S : Finset X) (hS : S.card = 4), q1 S hS = q S hS ∨ q1 S hS = (q S hS).swap := by
  intro S hS
  rcases h S hS with h1 | h1
  · exact Or.inl h1.symm
  · refine Or.inr ?_
    have h2 : (q S hS).swap = ((q1 S hS).swap).swap := congrArg Split.swap h1
    rw [Split.swap_swap] at h2
    exact h2.symm

/-! ## 下游收口：从「逐 quartet 一致」升级到「树同构」 -/

/-- ★★★ **ASTRAL 恢复真树的拓扑**（在缺口 `QuartetDecidesTree` 成立时）。

由 `astral_maximizer_agrees`（ASTRAL 输出与真树逐 quartet 一致）
+ 缺口（一致 ⟹ 同构）。`2|2` 条件现为 `QuartetTree.q_card` 字段，故**不必再传**。 -/
theorem astral_iso (hQD : QuartetDecidesTree.{u, v} X)
    (m : MSCFreq.{u, v} X) (hT : m.tree.IsBinary)
    {qt : QuartetTree.{u, v} X} (hqt : qt.tree.IsBinary)
    (h : IsASTRAL m.freq qt) : Nonempty (Iso qt.tree m.tree) :=
  hQD qt m.toQuartetTree hqt hT fun S hS => astral_maximizer_agrees m h S hS

/-- ★★★ **CASTER 恢复真树的拓扑**（同 `astral_iso`，经 `caster_isASTRAL`）。 -/
theorem caster_iso (hQD : QuartetDecidesTree.{u, v} X)
    (m : MSCFreq.{u, v} X) (hT : m.tree.IsBinary) (M : MultiMarkerFreq X)
    (hM : M.avg = m.freq)
    {qt : QuartetTree.{u, v} X} (hqt : qt.tree.IsBinary)
    (h : ∀ qt1 : QuartetTree.{u, v} X, casterScore M qt1.q ≤ casterScore M qt.q) :
    Nonempty (Iso qt.tree m.tree) :=
  astral_iso hQD m hT hqt (hM ▸ (caster_isASTRAL M).mp h)

/-- ★★★ **parsimony 恢复真树的拓扑**（在缺口 `QuartetDecidesTree` 成立时）。

由 `stable_argmax_site`（最简树 ⟹ 逐 quartet 一致）+ 缺口。 -/
theorem parsimony_iso (hQD : QuartetDecidesTree.{u, v} X)
    (M : MSCSite.{u, v} X) (hT : M.tree.IsBinary) (sm : SiteSampling.{u, v} X)
    {E : SiteSupport X → QuartetTree.{u, v} X} (hE : ∀ D, IsParsimony D (E D))
    (hEbin : ∀ D, (E D).tree.IsBinary)
    (hNE : ∃ q : QuartetChoice X, ¬ AgreesWith M.q q) :
    ∃ N : ℕ, ∀ n ≥ N, Nonempty (Iso (E (sm.emp n)).tree M.tree) := by
  obtain ⟨N, hN⟩ := parsimony_statisticallyConsistent M sm hE hNE
  exact ⟨N, fun n hn => hQD (E (sm.emp n)) M.asQuartetTree (hEbin (sm.emp n)) hT (hN n hn)⟩
