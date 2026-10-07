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

## 下游收口

* ★★★ `astral_iso` —— ASTRAL 输出与真树**同构**（假设缺口成立）；
* ★★★ `parsimony_iso` / `caster_iso` —— 同理。
-/

universe u v

variable {X : Type u} [Fintype X] [DecidableEq X]

/-- ★★ **（缺口，显式假设）quartet 系统决定 binary 树**。

✦ **经典已证定理，本库尚未形式化**（**非**学术开放问题）。

**陈述**：两棵 binary cladogram `T, T'`，若存在各自展示的 quartet 选择 `q, q'`
使得逐点一致（模 `swap`），则 `T ≅ T'`。

**文献**：Colonius & Schulze (1981), *Tree structures for proximity data*；
Steel (1992), *The complexity of reconstructing trees from qualitative characters and subtrees*；
教科书 Semple & Steel, *Phylogenetics* (2003) §6.4（full 情形的完整推理系统）。

**为什么 binary 不可去**：若 `T` 有 polytomy（内部度 `≥ 4`），把它 refine 成 binary 得到
`T'`，则 `q = q'` 但 `T ≇ T'`。 -/
def QuartetDecidesTree (X : Type u) [Fintype X] [DecidableEq X] : Prop :=
  ∀ (T T' : Cladogram.{u, v} X) (q q' : QuartetChoice X),
    T.IsBinary → T'.IsBinary →
    (∀ (S : Finset X) (hS : S.card = 4), T.DisplaysSplitOn S (q S hS)) →
    (∀ (S : Finset X) (hS : S.card = 4), T'.DisplaysSplitOn S (q' S hS)) →
    (∀ (S : Finset X) (hS : S.card = 4), q S hS = q' S hS ∨ q S hS = (q' S hS).swap) →
    Nonempty (Iso T T')

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
+ 缺口（一致 ⟹ 同构）。 -/
theorem astral_iso (hQD : QuartetDecidesTree.{u, v} X)
    (m : MSCFreq.{u, v} X) (hT : m.tree.IsBinary)
    {qt : QuartetTree.{u, v} X} (hqt : qt.tree.IsBinary)
    (h : IsASTRAL m.freq qt) : Nonempty (Iso qt.tree m.tree) :=
  hQD qt.tree m.tree qt.q m.q hqt hT qt.displays m.displays
    (fun S hS => astral_maximizer_agrees m h S hS)

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
  exact ⟨N, fun n hn => hQD (E (sm.emp n)).tree M.tree (E (sm.emp n)).q M.q
    (hEbin (sm.emp n)) hT (E (sm.emp n)).displays M.displays (hN n hn)⟩
