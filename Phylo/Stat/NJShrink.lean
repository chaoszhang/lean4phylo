/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.Stat.CASTERNJStep
import Phylo.Stat.StrictCherry

/-!
# `Phylo.Stat.NJShrink` —— L5a 步骤 A：树层樱桃收缩（W46 长程，**进行中**）

派单：`W44_TO_DSH_prompt.txt` §3.7 步骤 A；方案见 `Phylo/Stat/CASTERNJStep.lean` 文件头 §3。

## 目标

给定 `T : Phylogram X`（边权全正、二叉）、`{a,b}` 是 `T` 的樱桃（公共邻居 `w`），造出
`T' : Phylogram (MergeIdx X a b)`，使

```text
∀ u v : MergeIdx X a b, T'.dist (T'.leaf u) (T'.leaf v) = (mergeStep δ a b).val u v
```

从而 `HasPosReal δ → HasPosReal (mergeStep δ a b)`（= `CASTERNJ.njAdditiveGap`）。

## 构造（★ 已更正 —— 见 `CASTERNJStep.lean` §3 的 ★D）

* `V' := {v : T.V // v ≠ T.leaf b ∧ v ≠ w}`（删叶 `b`、再删中点 `w`）；
  ⚠️ 只删叶不改权是**错的**：删叶后 `w` 的度从 3 掉到 2，违反 `Cladogram.no_degree_two`。
* 图 = `T.graph.induce {v | v ≠ leaf b ∧ v ≠ w}` **再加一条 `leaf a — z`**
  （`z` = `w` 除 `a`、`b` 外**唯一**的邻居，由二叉性给出）；
* 边权：新边取 `½·(w ⟨a,w⟩ + w ⟨b,w⟩) + w ⟨w,z⟩`，其余原样；
* 算术核 **已证**：`Phylo.Stat.StrictCherry.mergeStep_val_eq`
  （`½·δ(x,a) + ½·δ(x,b) = ½(w_a+w_b) + d(w,x)`）⇒ 新–旧距离自动对上。

## 本文件进度（逐步提交）

| # | 内容 | 状态 |
|---|---|---|
| A1 | `ShrinkV`（收缩后的顶点类型） | ✅ |
| A2 | 两个不同邻居 ⇒ `w` 不是叶 | ✅ |
| A3 | `IsBinary` ⇒ `degree w = 3` | ✅ |
| A5 | `leafShrink : MergeIdx X a b ↪ ShrinkV T b w` ＋ 单射 | ✅ |
| A4 | 第三邻居 `z` 的存在 ＋ **穷尽性** | ✅ |
| A6 | 图（诱导 ＋ 一条边）、`Connected`、`IsAcyclic` ⇒ **`IsTree` 两半** | ✅ |
| A7 | **`deg_G v = deg_T v.1`**（三支：合并叶 / `z` / 其余） | ✅ |
| A7′ | `leaf_iff_degree_one` / `no_degree_two` 从 `T` 搬过来 | ✅ |
| A8-0 | 一般化中点避开引理（两端都 ∉ `{leaf a, leaf b, w}`） | ✅ |
| A8-1 | `njStep` ⇒ 树层 `T.IsCherry a b`（`Q = −2z` → Weller eq (3) → Thm 2） | ✅ |
| A8-2 | 边权 `shrinkW` ＋ `dist` 对齐 ＋ `HasPosReal` 收口 | ⏳ 下一步 |

**纪律**：零 sorry / axiom / opaque。本文件只加新声明，不动任何既有定理。

## A7b 的做法（第 31 轮）：度数**不变**，不必重建

收缩对每个**存活顶点**只做「删一条旧边、补一条新边」的局部平衡，于是

```text
∀ v : ShrinkV, (shrinkGraph T a b w z hza).degree v = T.graph.degree v.1
```

（★★★ `degree_shrinkGraph`，三支：合并叶 `⟨T.leaf a, ·⟩` / `z` / 其余）。
⇒ `Cladogram` 的两个度字段（`leaf_iff_degree_one`、`no_degree_two`）可以**整体**从 `T` 搬过来。

★ 三支都用 `Finset.card_bij`（显式双射），**不用** `Finset.attach/map/∩` 的运算链 ——
后者要先把 `shrinkGraph` 重写成 `induce ⊔ edge` 再搬 `map_neighborFinset_induce`，
状态数多、第 29–31 轮实测反复卡在类型不匹配上。

## ⚠️ 一条被排除的捷径（W46 长程第 18 轮）

**`HasPosReal` 不能从 `FourPoint` 推出来** —— 所以「用 `exists_realizingPhylogram_pos_of_addConst`
绕开树层收缩」这条路**不通**。反例（3 叶）：

```text
δ(1,2) = δ(1,3) = 1,  δ(2,3) = 2   （additive，四点条件平凡成立）
唯一的实现是星形：中心 w，垂枝 (0, 1, 1)
```

`HasPosReal` 要求**每条边权 > 0**，而叶 1 的垂枝必须是 `0` ⇒ 无反例可救。
（`addConst` 技巧只给出 `δ + ε` 的**正权**实现；把 `ε/2` 从垂枝上减回来，垂枝就回到 `ℓ ≥ 0`，
可能是 `0`。内部边确实仍是正的，但 `HasPosReal` 管的是**所有**边。）

⇒ 结论：`njAdditiveGap` 里那条「归约保持正权实现」**不是**可绕过的技术条件，
树层收缩（本文件的 A 步）是**唯一**出路。这条记录避免下一轮重走。

## ⏭️ 下一步（A6g 边数记账）的完整方案

`IsTree` 走 `isTree_iff_connected_and_card`（`G.IsTree ↔ G.Connected ∧ Nat.card ↑G.edgeSet + 1 = Nat.card V`），
`Connected` 已在手（`shrinkGraph_connected`），只差**边数**。

**目标**：`Nat.card ↑(shrinkGraph …).edgeSet = Fintype.card T.V - 3`
（配合本文件已证的 `card_shrinkV`：`Fintype.card (ShrinkV) + 2 = Fintype.card T.V`，
即得 `|E| + 1 = |V'|`）。

**计数方案（逐条）**：
1. `G` 的边 = 「两个端点都在 `ShrinkV` 的 `T`-边」∪ {新边}，且二者**不交**
   —— 新边不是 `T`-边：`not_adj_leaf_a_z`（已证）。
2. `T` 里「有一个端点在 `{leaf b, w}`」的边**恰 3 条**：
   `leaf b` 只有 1 条（`w—leaf b`，`leaf_b_adj_eq_midpoint` 已证）；
   `w` 有 3 条（`exists_third` 的穷尽性：`leaf a`、`leaf b`、`z`）；
   并集 = `{w—leaf b, w—leaf a, w—z}`，故共 **3** 条。
3. `|E_T| = Fintype.card T.V - 1`（`SimpleGraph.IsTree.card_edgeFinset`，已探到）。
4. 于是 `|E_G| = (|E_T| - 3) + 1 = (n-1) - 3 + 1 = n - 3`；而 `|V'| = n - 2` ⇒ `|E| + 1 = |V'|` ✓。

**已探到的器材**：
```
@SimpleGraph.IsTree.card_edgeFinset : G.IsTree → G.edgeFinset.card + 1 = Fintype.card V
@SimpleGraph.edgeFinset / mem_edgeFinset
@SimpleGraph.isTree_iff_connected_and_card : G.IsTree ↔ G.Connected ∧ Nat.card ↑G.edgeSet + 1 = Nat.card V
@SimpleGraph.IsTree.isAcyclic  （拿到 IsTree 后无环性免费）
```
**难点**：第 1、2 条的基数记账需要把 `edgeSet` 按端点分类（`Sym2` 的 `mem_edgeSet` 只给
「三角边 ↔ `Adj`」，取端点要用 `Sym2` 的消去/嵌入引理），这部分是 A 步最后一块工程。

**备选（若边数记账太难）**：反证法「环 ⟹ 顶点度 ≥ 2」—— 但 `Walk.IsCycle` 的 API 很薄
（只有 `not_nil` 与 `cons_isCycle_iff`），实现「环上顶点有两个相异邻居」要自己从 `cons_isCycle_iff`
的 `p.IsPath ∧ s(u,v) ∉ p.edges` 剥，且需要 `edges`（边）侧的 API —— 本文件目前全是**顶点**侧器械，
所以这条路**不建议**。

## ★★★ 更好的路：`IsAcyclic.sup_edge_of_not_reachable`（第 27 轮探到，**从这里继续**）

原本以为 A6g 只能走「边数记账」（要新建 `Sym2` 边侧地基，60–100 行）。**不必** ——
Mathlib 有两条现成引理，把 A6g 压成约 40 行：

```lean
@SimpleGraph.IsAcyclic.induce : G.IsAcyclic → ∀ (s : Set V), (induce s G).IsAcyclic
@SimpleGraph.IsAcyclic.sup_edge_of_not_reachable :
    ¬G.Reachable u v → G.IsAcyclic → (G ⊔ edge u v).IsAcyclic
```

**路线**（`shrinkGraph` 的结构从出生就是为它准备的：诱导 ＋ 一条边）：

1. `T.graph.induce {v | v ≠ leaf b ∧ v ≠ w}` 无环 —— `IsAcyclic.induce`（`T.toCladogram.isTree.isAcyclic`）；
2. `shrinkGraph = 上者 ⊔ edge ⟨leaf a⟩ ⟨z⟩` —— 逐点 `ext`，`sup_adj` / `induce_adj` / `edge_adj` 三件套；
3. `⟨leaf a⟩` 在诱导子图里是**孤点**（唯一 `T`-邻居 `w` 已删，`leaf_a_adj_eq_midpoint`）⇒ 与 `⟨z⟩` **不连通**；
4. ⇒ `IsAcyclic.sup_edge_of_not_reachable` 收口。

⇒ **边数记账可以整个跳过**（`card_shrinkV` 仍有用：`dist` 记账要用顶点数）。

⚠️ 试写时的三个坑（第 27 轮实测，本轮因上下文耗尽未收口，已 `git checkout` 回滚）：
* `ext u v` 后 `Subtype.ext_iff` 会把 `u = ⟨leaf a,·⟩` 化成 `u.1 = leaf a`，三支 `Or` 的
  `⟨h1,h2⟩` 配对会错位 ⇒ 建议 `simp only [...]` 之后直接 `tauto`，**别手写** `constructor/rintro`；
* 「孤点 ⇒ 不连通」要对走法 `cases p`（**不能** `induction p`，会报
  「Index in target's type is not a variable」）；
* `sup_edge_of_not_reachable` 是 **`IsAcyclic` 的字段**，写法
  `SimpleGraph.IsAcyclic.sup_edge_of_not_reachable hnr hacyc _`（`hnr` 在前）。



-/

noncomputable section

universe u v

namespace Phylo.Stat.NJShrink

open SimpleGraph
open NJ NJ.Dissimilarity
open Phylo.Stat.CASTERNJStep

variable {X : Type u} [Fintype X] [DecidableEq X]

/-- **A1｜收缩后的顶点类型**：`T` 删掉叶 `T.leaf b` 与内部点 `w`。 -/
abbrev ShrinkV (T : Phylogram.{u, v} X) (b : X) (w : T.V) : Type v :=
  {v : T.V // v ≠ T.leaf b ∧ v ≠ w}

variable (T : Phylogram.{u, v} X)

/-- ★★ **A2｜两个不同标签的邻居 ⇒ `w` 不是叶**。

叶的度是 1，而 `degree_eq_one_iff_existsUnique_adj` 说度 1 的顶点**只有一个**邻居；
`T.leaf a` 与 `T.leaf b` 是两个不同邻居 ⇒ 矛盾。 -/
theorem not_isLeaf_of_two_adj {a b : X} (hab : a ≠ b) {w : T.V}
    (haw : T.graph.Adj (T.leaf a) w) (hbw : T.graph.Adj (T.leaf b) w) :
    ¬ T.toCladogram.IsLeaf w := by
  intro hleaf
  have hd1 : T.graph.degree w = 1 := (T.isLeaf_iff_degree_eq_one w).mp hleaf
  obtain ⟨c, _, huniq⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hd1
  have h1 : T.leaf a = c := huniq (T.leaf a) haw.symm
  have h2 : T.leaf b = c := huniq (T.leaf b) hbw.symm
  exact hab (T.leaf.injective (h1.trans h2.symm))

/-- ★★ **A3｜二叉 ⇒ 樱桃中点的度恰为 3**。 -/
theorem degree_eq_three (hbin : T.toCladogram.IsBinary) {a b : X} (hab : a ≠ b) {w : T.V}
    (haw : T.graph.Adj (T.leaf a) w) (hbw : T.graph.Adj (T.leaf b) w) :
    T.graph.degree w = 3 :=
  hbin w (not_isLeaf_of_two_adj T hab haw hbw)

/-- 樱桃中点**不是任何叶的像**（否则它的度会是 1，与度 3 矛盾）。 -/
theorem leaf_ne_midpoint (hbin : T.toCladogram.IsBinary) {a b : X} (hab : a ≠ b) {w : T.V}
    (haw : T.graph.Adj (T.leaf a) w) (hbw : T.graph.Adj (T.leaf b) w) (x : X) :
    T.leaf x ≠ w := by
  intro h
  have hleaf : T.toCladogram.IsLeaf w := ⟨x, h⟩
  have hd1 : T.graph.degree w = 1 := (T.isLeaf_iff_degree_eq_one w).mp hleaf
  have hd3 := degree_eq_three T hbin hab haw hbw
  omega

/-- ★★ **A5｜收缩后的叶嵌入** `MergeIdx X a b ↪ ShrinkV T b w`：
旧标签 `x` 映到 `⟨T.leaf x.1, ·⟩`，合并标签 `u` 映到 `⟨T.leaf a, ·⟩`。 -/
def leafShrink (hbin : T.toCladogram.IsBinary) {a b : X} (hab : a ≠ b) {w : T.V}
    (haw : T.graph.Adj (T.leaf a) w) (hbw : T.graph.Adj (T.leaf b) w) :
    MergeIdx X a b ↪ ShrinkV T b w where
  toFun
    | Sum.inl x => ⟨T.leaf x.1, by
        refine ⟨?_, leaf_ne_midpoint T hbin hab haw hbw x.1⟩
        intro h
        exact mergeOld_ne_right x (T.leaf.injective h)⟩
    | Sum.inr _ => ⟨T.leaf a, by
        refine ⟨?_, leaf_ne_midpoint T hbin hab haw hbw a⟩
        intro h
        exact hab (T.leaf.injective h)⟩
  inj' := by
    rintro (x | x) (y | y) h
    · have hxe : T.leaf x.1 = T.leaf y.1 := congrArg Subtype.val h
      have : x = y := Subtype.ext (T.leaf.injective hxe)
      rw [this]
    · have hxe : T.leaf x.1 = T.leaf a := congrArg Subtype.val h
      exact absurd (T.leaf.injective hxe) (mergeOld_ne_left x)
    · have hxe : T.leaf a = T.leaf y.1 := congrArg Subtype.val h
      exact absurd (T.leaf.injective hxe).symm (mergeOld_ne_left y)
    · exact congrArg Sum.inr (Subsingleton.elim x y)

/-- ★★ **A4｜第三邻居 `z` 及**穷尽性**。

`w` 的度是 3（A3），其邻域是三元集；`T.leaf a`、`T.leaf b` 已占两个不同位置
⇒ 三元集减去这两点后恰剩**一个**元素 `z`。结论同时给出**穷尽性**
（`w` 的每个邻居必是 `leaf a`、`leaf b`、`z` 之一）—— 连通性与无环性都要用它。 -/
theorem exists_third (hbin : T.toCladogram.IsBinary) {a b : X} (hab : a ≠ b) {w : T.V}
    (haw : T.graph.Adj (T.leaf a) w) (hbw : T.graph.Adj (T.leaf b) w) :
    ∃ z : T.V, T.graph.Adj w z ∧ z ≠ T.leaf a ∧ z ≠ T.leaf b ∧
      (∀ v : T.V, T.graph.Adj w v → v = T.leaf a ∨ v = T.leaf b ∨ v = z) := by
  have hdeg : T.graph.degree w = 3 := degree_eq_three T hbin hab haw hbw
  have hcard : (T.graph.neighborFinset w).card = 3 := by
    rw [SimpleGraph.neighborFinset, Set.toFinset_card, SimpleGraph.card_neighborSet_eq_degree, hdeg]
  obtain ⟨x, y, z, hxy, hxz, hyz, hset⟩ := Finset.card_eq_three.mp hcard
  have ha : T.leaf a ∈ ({x, y, z} : Finset T.V) := by
    rw [← hset, SimpleGraph.mem_neighborFinset]; exact haw.symm
  have hb : T.leaf b ∈ ({x, y, z} : Finset T.V) := by
    rw [← hset, SimpleGraph.mem_neighborFinset]; exact hbw.symm
  have hne : T.leaf a ≠ T.leaf b := fun h => hab (T.leaf.injective h)
  have hcard3 : ({x, y, z} : Finset T.V).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hxy, hxz]),
      Finset.card_insert_of_notMem (by simp [hyz]), Finset.card_singleton]
  have hsub : ({T.leaf a, T.leaf b} : Finset T.V) ⊆ ({x, y, z} : Finset T.V) := by
    intro v hv
    rw [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl <;> assumption
  have hsd : (({x, y, z} : Finset T.V) \ {T.leaf a, T.leaf b}).card = 1 := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsub, hcard3, Finset.card_pair hne]
  obtain ⟨z', hz'⟩ := Finset.card_eq_one.mp hsd
  have hmem : z' ∈ (({x, y, z} : Finset T.V) \ {T.leaf a, T.leaf b}) := by
    rw [hz']; exact Finset.mem_singleton_self z'
  refine ⟨z', ?_, ?_, ?_, ?_⟩
  · have hzw : z' ∈ T.graph.neighborFinset w := by
      rw [hset]; exact (Finset.mem_sdiff.mp hmem).1
    rwa [SimpleGraph.mem_neighborFinset] at hzw
  · intro h
    exact (Finset.mem_sdiff.mp hmem).2 (by rw [h]; exact Finset.mem_insert_self _ _)
  · intro h
    exact (Finset.mem_sdiff.mp hmem).2
      (by rw [h]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  · intro v hv
    have hv' : v ∈ ({x, y, z} : Finset T.V) := by
      rw [← hset, SimpleGraph.mem_neighborFinset]; exact hv
    by_cases hvv : v ∈ ({T.leaf a, T.leaf b} : Finset T.V)
    · rw [Finset.mem_insert, Finset.mem_singleton] at hvv
      rcases hvv with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · refine Or.inr (Or.inr ?_)
      have hmem2 : v ∈ (({x, y, z} : Finset T.V) \ {T.leaf a, T.leaf b}) :=
        Finset.mem_sdiff.mpr ⟨hv', hvv⟩
      rw [hz'] at hmem2
      exact Finset.mem_singleton.mp hmem2

/-! ## A6｜收缩后的图 = 诱导子图 ＋ 一条 `leaf a — z` -/

/-- ★★ **A6a｜收缩后的图**：旧边照搬（诱导子图），另加一条 `T.leaf a — z`。

（`z` 是樱桃中点的第三邻居，见 ★★ `exists_third`；`hza` 用于无自环的证明。） -/
def shrinkGraph (a b : X) (w z : T.V) (hza : z ≠ T.leaf a) :
    SimpleGraph (ShrinkV T b w) where
  Adj u v := T.graph.Adj u.1 v.1 ∨
    (u.1 = T.leaf a ∧ v.1 = z) ∨ (u.1 = z ∧ v.1 = T.leaf a)
  symm := ⟨fun u v h => by
    rcases h with h | h | h
    · exact Or.inl h.symm
    · exact Or.inr (Or.inr ⟨h.2, h.1⟩)
    · exact Or.inr (Or.inl ⟨h.2, h.1⟩)⟩
  loopless := ⟨fun u h => by
    rcases h with h | h | h
    · exact T.graph.loopless.irrefl u.1 h
    · exact hza (h.2.symm.trans h.1)
    · exact hza (h.1.symm.trans h.2)⟩

/-- ★ **A6b｜旧–旧邻接照搬**：`T.graph` 里相邻 ⇒ 收缩图里相邻。 -/
theorem shrinkGraph_adj_of_adj (a b : X) (w z : T.V) (hza : z ≠ T.leaf a)
    {u v : ShrinkV T b w} (h : T.graph.Adj u.1 v.1) :
    (shrinkGraph T a b w z hza).Adj u v :=
  Or.inl h

/-- ★★ **A6c｜反向**：收缩图里的相邻，要么是旧边，要么**恰是**新边 `leaf a — z`（两个朝向）。 -/
theorem shrinkGraph_adj_cases (a b : X) (w z : T.V) (hza : z ≠ T.leaf a)
    {u v : ShrinkV T b w} (h : (shrinkGraph T a b w z hza).Adj u v) :
    T.graph.Adj u.1 v.1 ∨ (u.1 = T.leaf a ∧ v.1 = z) ∨ (u.1 = z ∧ v.1 = T.leaf a) :=
  h

/-- ★★ **A6d｜新边确实在**：`⟨T.leaf a, ·⟩` 与 `⟨z, ·⟩` 相邻。

（两个端点都在 `ShrinkV` 里：`T.leaf a ≠ T.leaf b`（`a ≠ b`）、`T.leaf a ≠ w`、`z ≠ T.leaf b`、
`z ≠ w`（`z` 与 `w` 相邻故不等）。） -/
theorem shrinkGraph_adj_new {a b : X} (hab : a ≠ b) {w z : T.V}
    (hbin : T.toCladogram.IsBinary) (haw : T.graph.Adj (T.leaf a) w)
    (hbw : T.graph.Adj (T.leaf b) w) (hwz : T.graph.Adj w z) (hza : z ≠ T.leaf a)
    (hzb : z ≠ T.leaf b) :
    (shrinkGraph T a b w z hza).Adj
      ⟨T.leaf a, ⟨fun h => hab (T.leaf.injective h), leaf_ne_midpoint T hbin hab haw hbw a⟩⟩
      ⟨z, ⟨hzb, fun h => (T.graph.loopless.irrefl z) (h ▸ hwz)⟩⟩ :=
  Or.inr (Or.inl ⟨rfl, rfl⟩)

/-- ★★★ **A6e｜走法转移（连通性的引擎）**：若 `T` 里一条走法 `p : x → y` 的**所有顶点**都
避开 `T.leaf b` 与 `w`，则它整条落进收缩图，给出 `⟨x,·⟩ → ⟨y,·⟩` 的走法。

按走法结构归纳（`Walk.nil` / `Walk.cons`）；每个旧边用 `shrinkGraph_adj_of_adj`（`Or.inl`）搬过来。 -/
theorem exists_walk_shrink (a b : X) (w z : T.V) (hza : z ≠ T.leaf a) {x y : T.V}
    (p : T.graph.Walk x y) :
    (∀ v ∈ p.support, v ≠ T.leaf b ∧ v ≠ w) →
      ∀ (hx : x ≠ T.leaf b ∧ x ≠ w) (hy : y ≠ T.leaf b ∧ y ≠ w),
        Nonempty ((shrinkGraph T a b w z hza).Walk ⟨x, hx⟩ ⟨y, hy⟩) := by
  induction p with
  | nil => intro _ hx _; exact ⟨SimpleGraph.Walk.nil⟩
  | @cons u v w' h q ih =>
      intro hsupp hx hy
      have hsub : ∀ t ∈ q.support, t ≠ T.leaf b ∧ t ≠ w := by
        intro t ht
        exact hsupp t (by
          rw [SimpleGraph.Walk.support_cons]
          exact List.mem_cons_of_mem _ ht)
      have hv : v ≠ T.leaf b ∧ v ≠ w := by
        exact hsupp v (by
          rw [SimpleGraph.Walk.support_cons]
          exact List.mem_cons_of_mem _ (SimpleGraph.Walk.start_mem_support q))
      obtain ⟨q'⟩ := ih hsub hv hy
      exact ⟨SimpleGraph.Walk.cons (shrinkGraph_adj_of_adj T a b w z hza h) q'⟩

/-! ## A7 前置｜收缩图里「合并叶」`⟨T.leaf a, ·⟩` 的邻居只有 `⟨z, ·⟩`

这就是 `Cladogram.leaf_iff_degree_one` 在合并叶上的那一半。
（`T.leaf a` 在 `T` 里的唯一邻居是 `w`，而 `w ∉ ShrinkV` ⇒ 旧边全被删掉，只剩新边 `leaf a — z`。） -/

/-- 樱桃叶 `T.leaf a` 在 `T` 里的**唯一**邻居是 `w`。 -/
theorem leaf_a_adj_eq_midpoint {a : X} {w : T.V} (haw : T.graph.Adj (T.leaf a) w) :
    ∀ y : T.V, T.graph.Adj (T.leaf a) y → y = w := by
  have hd1 : T.graph.degree (T.leaf a) = 1 :=
    (T.isLeaf_iff_degree_eq_one (T.leaf a)).mp ⟨a, rfl⟩
  obtain ⟨c, _, hcuniq⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hd1
  have hcw : c = w := (hcuniq w haw).symm
  exact fun y hy => (hcuniq y hy).trans hcw

/-- ★★ **A7a｜收缩图里 `⟨T.leaf a, ·⟩` 只与 `⟨z, ·⟩` 相邻**（故其度为 1）。 -/
theorem shrinkGraph_adj_leaf_a_iff (a b : X) (w z : T.V) (hza : z ≠ T.leaf a)
    (haw : T.graph.Adj (T.leaf a) w)
    (ha : T.leaf a ≠ T.leaf b ∧ T.leaf a ≠ w) {v : ShrinkV T b w} :
    (shrinkGraph T a b w z hza).Adj ⟨T.leaf a, ha⟩ v ↔ v.1 = z := by
  have huniq := leaf_a_adj_eq_midpoint T haw
  constructor
  · intro h
    rcases shrinkGraph_adj_cases T a b w z hza h with h' | h' | h'
    · exact absurd (huniq v.1 h') v.2.2
    · exact h'.2
    · exact h'.2.trans h'.1
  · intro h
    have hz2 : z ≠ T.leaf b ∧ z ≠ w := by
      rw [← h]; exact v.2
    have hv : v = ⟨z, hz2⟩ := Subtype.ext h
    rw [hv]
    exact Or.inr (Or.inl ⟨rfl, rfl⟩)

/-- 被删掉的叶 `T.leaf b` 在收缩图里**不再有任何邻居**（它在 `T` 里唯一的邻居 `w` 已被删）。
这条是「删叶」这一步的**正确性**依据：`T.leaf b` 的旧边全部随 `w` 一起消失。 -/
theorem not_adj_leaf_b {b : X} {w : T.V} (hbw : T.graph.Adj (T.leaf b) w)
    {v : ShrinkV T b w} : ¬ T.graph.Adj (T.leaf b) v.1 := by
  have hd1 : T.graph.degree (T.leaf b) = 1 :=
    (T.isLeaf_iff_degree_eq_one (T.leaf b)).mp ⟨b, rfl⟩
  obtain ⟨c, _, hcuniq⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hd1
  have hcw : c = w := (hcuniq w hbw).symm
  intro h
  exact v.2.2 ((hcuniq v.1 h).trans hcw)

/-! ## A6f 前置｜度为 1 的顶点在无重复走法上只能当端点 -/

/-- ★★★ **A6f 的前置引理**：度为 1 的顶点若出现在一条**无重复**走法的支撑集里，
则它必是该走法的一个**端点**。

（这是上一轮定位出的**循环依赖**的解药：A6f 要证「`w` 的两个路径邻居 ∉ `{leaf a, leaf b}`」，
而那只因为 `leaf a`/`leaf b` 度为 1 只能当端点 —— 所以必须先**独立**证本条。）

证法：按走法结构归纳。
* `nil`：支撑集是单点集，`y = x`。
* `cons h q`（`h : Adj x0 mid`）：若 `y = x0` 成；否则 `y ∈ q.support`，由归纳假设
  `y = mid ∨ y = z0`。若 `y = z0` 成；若 `y = mid`，则 `q` 必为 `nil` ——
  否则 `q = cons h' r`，由 `y` 的唯一邻居 `c` 得 `x0 = c` 且 `m1 = c`，
  即 `x0 = m1 ∈ q.support`，与 `Nodup` 给的首元素不在尾支撑集里矛盾。 -/
theorem leaf_mem_support_eq_end (hdeg : T.graph.degree y = 1) {x z' : T.V}
    (p : T.graph.Walk x z') (hp : p.support.Nodup) (hy : y ∈ p.support) :
    y = x ∨ y = z' := by
  induction p with
  | nil => exact Or.inl (by simpa using hy)
  | @cons x0 mid z0 h q ih =>
      rw [SimpleGraph.Walk.support_cons] at hy
      obtain ⟨hx0q, hqnd⟩ := List.nodup_cons.mp hp
      rcases List.mem_cons.mp hy with hyx | hyq
      · exact Or.inl hyx
      · rcases ih hqnd hyq with h1 | h1
        · obtain ⟨c, _, hcuniq⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hdeg
          cases q with
          | nil => exact Or.inr h1
          | @cons m0 m1 m2 h' r =>
              have hxc : x0 = c := hcuniq x0 (h1 ▸ h).symm
              have hm1 : m1 = c := hcuniq m1 (h1 ▸ h')
              have hmem1 : m1 ∈ r.support := SimpleGraph.Walk.start_mem_support r
              have hmem : m1 ∈ (SimpleGraph.Walk.cons h' r).support := by
                rw [SimpleGraph.Walk.support_cons]
                exact List.mem_cons_of_mem _ hmem1
              have hx0mem : x0 ∈ (SimpleGraph.Walk.cons h' r).support := by
                simpa [hm1, hxc] using hmem
              exact absurd hx0mem hx0q
        · exact Or.inr h1

/-- ★★ **A6f 第 1 步**：度为 1 的顶点若**既不是起点也不是终点**，就不在任何无重复走法的支撑集里。

直接由 ★★★ `leaf_mem_support_eq_end` 取逆否。这条正是把 `T.leaf a`、`T.leaf b`
从「`u.1 → z` 的路径」上排除掉的工具（A4′ 的穷尽性随后才能把 `w` 的两个路径邻居逼到 `z`）。 -/
theorem not_mem_support_of_degree_one {y x z' : T.V} (hdeg : T.graph.degree y = 1)
    (p : T.graph.Walk x z') (hp : p.IsPath) (hx : x ≠ y) (hz : z' ≠ y) :
    y ∉ p.support := by
  intro hmem
  rcases leaf_mem_support_eq_end T hdeg p hp.support_nodup hmem with h | h
  · exact hx h.symm
  · exact hz h.symm

/-- 樱桃叶 `T.leaf b` 在 `T` 里的**唯一**邻居也是 `w`（`A7a` helper 的对称件）。 -/
theorem leaf_b_adj_eq_midpoint {b : X} {w : T.V} (hbw : T.graph.Adj (T.leaf b) w) :
    ∀ y : T.V, T.graph.Adj (T.leaf b) y → y = w := by
  have hd1 : T.graph.degree (T.leaf b) = 1 :=
    (T.isLeaf_iff_degree_eq_one (T.leaf b)).mp ⟨b, rfl⟩
  obtain ⟨c, _, hcuniq⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hd1
  have hcw : c = w := (hcuniq w hbw).symm
  exact fun y hy => (hcuniq y hy).trans hcw

/-- ★★ **新边确实是新的**：`T.leaf a` 与 `z` 在 `T` 里**不**相邻
（`T.leaf a` 的唯一邻居是 `w`，而 `z ≠ w`）。 -/
theorem not_adj_leaf_a_z {a : X} {w z : T.V} (haw : T.graph.Adj (T.leaf a) w) (hzw : z ≠ w) :
    ¬ T.graph.Adj (T.leaf a) z :=
  fun h => hzw (leaf_a_adj_eq_midpoint T haw z h)

/-- ★★ **新边确实是新的**（对称件）：`T.leaf b` 与 `z` 在 `T` 里不相邻。 -/
theorem not_adj_leaf_b_z {b : X} {w z : T.V} (hbw : T.graph.Adj (T.leaf b) w) (hzw : z ≠ w) :
    ¬ T.graph.Adj (T.leaf b) z :=
  fun h => hzw (leaf_b_adj_eq_midpoint T hbw z h)

/-- ★★ **A7b-a｜旧叶（非 `z`）在收缩图里的邻居就是它在 `T` 里的邻居**。

若 `T.leaf x.1 ≠ z`（`x` 是 `MergeOld`，故 `x.1 ∉ {a,b}`），则旧叶不碰新边：
新边的两个端点分别是 `T.leaf a`（会逼迫 `x.1 = a`，与 `MergeOld` 矛盾）与 `z`（被 `hzx` 排除）。
⇒ 邻域完全由旧边决定 —— `no_degree_two` 与 `leaf_iff_degree_one` 都靠它。 -/
theorem shrinkGraph_adj_leaf_old (a b : X) (w z : T.V) (hza : z ≠ T.leaf a)
    (x : MergeOld X a b) (hx : T.leaf x.1 ≠ T.leaf b ∧ T.leaf x.1 ≠ w)
    (hzx : T.leaf x.1 ≠ z) {v : ShrinkV T b w} :
    (shrinkGraph T a b w z hza).Adj ⟨T.leaf x.1, hx⟩ v ↔ T.graph.Adj (T.leaf x.1) v.1 := by
  constructor
  · intro h
    rcases shrinkGraph_adj_cases T a b w z hza h with h' | h' | h'
    · exact h'
    · exact absurd (T.leaf.injective h'.1) (mergeOld_ne_left x)
    · exact absurd h'.1 hzx
  · intro h
    exact shrinkGraph_adj_of_adj T a b w z hza h

/-! ## A8 前置｜归约后的**新垂枝**严格正 -/

/-- ★★ **A8 前置**：归约后「合并标签 `u` 到旧标签 `x`」的距离**严格正**
（`= ½·δ(x,a) + ½·δ(x,b)`，两个正数之和）。

这正是 `HasPosReal (mergeStep δ a b)` 里**新垂枝**那一项的正性：
收缩树的合并垂枝权取 `½(w_a+w_b) + w(w,z)`，其第一项由本条保证为正。 -/
theorem mergeStep_val_merged_pos (δ : Dissimilarity X)
    (hpos : ∀ x y : X, x ≠ y → 0 < δ.val x y) {a b : X} (hab : a ≠ b)
    {x : X} (hx : x ≠ a) (hx' : x ≠ b) :
    0 < (mergeStep δ a b).val (mergeQ a b x) (mergeQ a b b) := by
  rw [mergeStep_val_merged δ a b hx hx']
  have h1 : 0 < δ.val x a := hpos x a hx
  have h2 : 0 < δ.val x b := hpos x b hx'
  nlinarith

/-! ## A6f 第 2 步｜樱桃中点 `w` 不在「`x → z`」的路径上 -/

/-- ★★★ **A6f 的核心**：若 `x ∉ {leaf a, leaf b, w}`、`z ∉ {leaf a, leaf b, w}` 且 `Adj w z`，
则 `w` 不在任何 `x → z` 的**简单**路径的支撑集里。

证法（`getVert` 定位路线 —— 本步的关键器械）：
令 `i := idxOf w p.support`，则 `p.getVert i = w`，且 `0 < i < p.length`（否则 `w = x` 或 `w = z`）。
取 `a₀ := p.getVert (i-1)`、`a₁ := p.getVert (i+1)`：
* `Adj a₀ w`（`adj_getVert_succ` 在 `i-1`）与 `Adj w a₁`（在 `i`）；
* 二者都在 `p.support` 里（`getVert_mem_support`）⇒ 由 ★★ `not_mem_support_of_degree_one`
  都 `≠ leaf a, leaf b`；
* 由 A4′ 的**穷尽性** ⇒ 二者都 `= z`；
* 于是 `p.getVert (i-1) = p.getVert (i+1)`，由 `IsPath.getVert_injOn` 得 `i-1 = i+1` —— 矛盾。 -/
theorem midpoint_not_mem_support (hbin : T.toCladogram.IsBinary) {a b : X} (hab : a ≠ b)
    {w z : T.V} (haw : T.graph.Adj (T.leaf a) w) (hbw : T.graph.Adj (T.leaf b) w)
    (hwz : T.graph.Adj w z) (hza : z ≠ T.leaf a) (hzb : z ≠ T.leaf b) (hzw : z ≠ w)
    {x : T.V} (hxa : x ≠ T.leaf a) (hxb : x ≠ T.leaf b) (hxw : x ≠ w)
    (p : T.graph.Walk x z) (hp : p.IsPath) : w ∉ p.support := by
  intro hw
  obtain ⟨z₀, hz₀adj, hz₀a, hz₀b, hexh⟩ := exists_third T hbin hab haw hbw
  have hzz₀ : z = z₀ := by
    rcases hexh z hwz with h | h | h
    · exact absurd h hza
    · exact absurd h hzb
    · exact h
  subst hzz₀
  have hda : T.graph.degree (T.leaf a) = 1 :=
    (T.isLeaf_iff_degree_eq_one (T.leaf a)).mp ⟨a, rfl⟩
  have hdb : T.graph.degree (T.leaf b) = 1 :=
    (T.isLeaf_iff_degree_eq_one (T.leaf b)).mp ⟨b, rfl⟩
  have hla : T.leaf a ∉ p.support :=
    not_mem_support_of_degree_one T hda p hp hxa hza
  have hlb : T.leaf b ∉ p.support :=
    not_mem_support_of_degree_one T hdb p hp hxb hzb
  set i := List.idxOf w p.support with hi
  have hlen : p.support.length = p.length + 1 := SimpleGraph.Walk.length_support p
  have hilt : i < p.support.length := List.idxOf_lt_length_iff.mpr hw
  have hile : i ≤ p.length := by omega
  have hwi : p.getVert i = w := by
    rw [SimpleGraph.Walk.getVert_eq_support_getElem p hile, List.getElem_idxOf hilt]
  have hi0 : 0 < i := by
    rcases Nat.eq_zero_or_pos i with h | h
    · rw [h, SimpleGraph.Walk.getVert_zero] at hwi
      exact absurd hwi hxw
    · exact h
  have hilen : i < p.length := by
    rcases lt_or_eq_of_le hile with h | h
    · exact h
    · rw [h, SimpleGraph.Walk.getVert_length] at hwi
      exact absurd hwi hzw
  have hadj0 : T.graph.Adj (p.getVert (i - 1)) w := by
    have h := SimpleGraph.Walk.adj_getVert_succ p (i := i - 1) (by omega)
    rwa [Nat.sub_add_cancel hi0, hwi] at h
  have hadj1 : T.graph.Adj w (p.getVert (i + 1)) := by
    have h := SimpleGraph.Walk.adj_getVert_succ p (i := i) (by omega)
    rwa [hwi] at h
  have hm0 : p.getVert (i - 1) ∈ p.support := SimpleGraph.Walk.getVert_mem_support p _
  have hm1 : p.getVert (i + 1) ∈ p.support := SimpleGraph.Walk.getVert_mem_support p _
  have h0 : p.getVert (i - 1) = z := by
    rcases hexh _ hadj0.symm with h | h | h
    · exact absurd (h ▸ hm0) hla
    · exact absurd (h ▸ hm0) hlb
    · exact h
  have h1 : p.getVert (i + 1) = z := by
    rcases hexh _ hadj1 with h | h | h
    · exact absurd (h ▸ hm1) hla
    · exact absurd (h ▸ hm1) hlb
    · exact h
  have hinj : p.getVert (i - 1) = p.getVert (i + 1) := h0.trans h1.symm
  have heq : i - 1 = i + 1 :=
    hp.getVert_injOn (by omega : i - 1 ≤ p.length) (by omega : i + 1 ≤ p.length) hinj
  omega

/-! ## A6f｜收缩图**连通** -/

/-- ★★★ **A6f `Connected`**：收缩图连通。

路线：**每个顶点都能走到合并叶 `⟨T.leaf a, ·⟩`** ——
* `u = ⟨T.leaf a, ·⟩`：平凡；
* 否则取 `T` 里 `u.1 → z` 的**唯一**简单路径 `p`：`w ∉ p.support`（★★★ `midpoint_not_mem_support`）、
  `T.leaf b ∉ p.support`（★★ `not_mem_support_of_degree_one`）⇒ 由 ★★★ `exists_walk_shrink`
  得 `u → ⟨z, ·⟩` 的走法，再走新边 `⟨z, ·⟩ — ⟨T.leaf a, ·⟩`。
最后 `Preconnected` 由「两段接到同一个汇点」拼出。 -/
theorem shrinkGraph_connected (hbin : T.toCladogram.IsBinary) {a b : X} (hab : a ≠ b)
    {w z : T.V} (haw : T.graph.Adj (T.leaf a) w) (hbw : T.graph.Adj (T.leaf b) w)
    (hwz : T.graph.Adj w z) (hza : z ≠ T.leaf a) (hzb : z ≠ T.leaf b) (hzw : z ≠ w) :
    (shrinkGraph T a b w z hza).Connected := by
  have hza_mem : T.leaf a ≠ T.leaf b ∧ T.leaf a ≠ w :=
    ⟨fun h => hab (T.leaf.injective h), leaf_ne_midpoint T hbin hab haw hbw a⟩
  have hz_mem : z ≠ T.leaf b ∧ z ≠ w := ⟨hzb, hzw⟩
  have hedge : (shrinkGraph T a b w z hza).Adj ⟨z, hz_mem⟩ ⟨T.leaf a, hza_mem⟩ :=
    Or.inr (Or.inr ⟨rfl, rfl⟩)
  have hdb : T.graph.degree (T.leaf b) = 1 :=
    (T.isLeaf_iff_degree_eq_one (T.leaf b)).mp ⟨b, rfl⟩
  -- 每个顶点都能走到合并叶
  have hhub : ∀ u : ShrinkV T b w,
      Nonempty ((shrinkGraph T a b w z hza).Walk u ⟨T.leaf a, hza_mem⟩) := by
    intro u
    by_cases hua : u.1 = T.leaf a
    · have hud : u = ⟨T.leaf a, hza_mem⟩ := Subtype.ext hua
      rw [hud]
      exact ⟨SimpleGraph.Walk.nil⟩
    · obtain ⟨p, hp, _⟩ := T.toCladogram.existsUnique_path u.1 z
      have hlb : T.leaf b ∉ p.support := not_mem_support_of_degree_one T hdb p hp u.2.1 hzb
      have hw : w ∉ p.support :=
        midpoint_not_mem_support T hbin hab haw hbw hwz hza hzb hzw hua u.2.1 u.2.2 p hp
      have hsupp : ∀ v ∈ p.support, v ≠ T.leaf b ∧ v ≠ w :=
        fun v hv => ⟨fun h => hlb (h ▸ hv), fun h => hw (h ▸ hv)⟩
      obtain ⟨q⟩ := exists_walk_shrink T a b w z hza p hsupp ⟨u.2.1, u.2.2⟩ hz_mem
      exact ⟨q.append (SimpleGraph.Walk.cons hedge SimpleGraph.Walk.nil)⟩
  rw [SimpleGraph.connected_iff]
  refine ⟨?_, ⟨⟨T.leaf a, hza_mem⟩⟩⟩
  intro u v
  obtain ⟨q1⟩ := hhub u
  obtain ⟨q2⟩ := hhub v
  exact ⟨q1.append q2.reverse⟩

/-! ## A6g 器械｜**反向搬移**（`G`-走法 → `T`-走法） -/

/-- ★★★ **反向搬移**：若收缩图里一条走法的支撑集**不含** `⟨T.leaf a, ·⟩`，则它完全由旧边组成，
可以搬回 `T`。

理由：新边 `leaf a — z` 的端点必含 `T.leaf a`（`shrinkGraph_adj_cases` 的另两支），
被支撑集条件排掉 ⇒ 每一步都是 `T`-边。

这是 ★★★ `exists_walk_shrink`（`T → G`）的严格对称件；无环性（A6g）与
`dist` 对齐（A8 的旧–旧部分）都要用它。 -/
theorem exists_walk_of_shrink (a b : X) (w z : T.V) (hza : z ≠ T.leaf a) :
    ∀ {U V : ShrinkV T b w} (p : (shrinkGraph T a b w z hza).Walk U V),
      (∀ v ∈ p.support, v.1 ≠ T.leaf a) → Nonempty (T.graph.Walk U.1 V.1) := by
  intro U V p
  induction p with
  | nil => exact fun _ => ⟨SimpleGraph.Walk.nil⟩
  | @cons U0 M V0 h q ih =>
      intro hav
      have hsub : ∀ v ∈ q.support, v.1 ≠ T.leaf a := fun v hv =>
        hav v (by rw [SimpleGraph.Walk.support_cons]; exact List.mem_cons_of_mem _ hv)
      have hU : U0.1 ≠ T.leaf a :=
        hav U0 (by rw [SimpleGraph.Walk.support_cons]; exact List.mem_cons_self)
      have hM : M.1 ≠ T.leaf a :=
        hav M (by
          rw [SimpleGraph.Walk.support_cons]
          exact List.mem_cons_of_mem _ (SimpleGraph.Walk.start_mem_support q))
      obtain ⟨q'⟩ := ih hsub
      have htedge : T.graph.Adj U0.1 M.1 := by
        rcases shrinkGraph_adj_cases T a b w z hza h with h' | h' | h'
        · exact h'
        · exact absurd h'.1 hU
        · exact absurd h'.2 hM
      exact ⟨SimpleGraph.Walk.cons htedge q'⟩

/-! ## A6g 前置｜顶点计数（边数记账的那一半） -/

/-- ★★ **A6g 前置**：`ShrinkV` 比 `T.V` 少**两个**顶点。

（`ShrinkV T b w = {v // v ≠ leaf b ∧ v ≠ w}`；与 `univ \ {leaf b, w}` 建立显式等价后数基数。） -/
theorem card_shrinkV {b : X} {w : T.V} (hne : T.leaf b ≠ w) :
    Fintype.card (ShrinkV T b w) + 2 = Fintype.card T.V := by
  have hset : (Finset.univ.filter (fun v : T.V => v ≠ T.leaf b ∧ v ≠ w))
      = (Finset.univ : Finset T.V) \ {T.leaf b, w} := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff,
      Finset.mem_insert, Finset.mem_singleton, not_or]
  rw [Fintype.card_subtype, hset, Finset.card_sdiff,
    Finset.inter_eq_left.mpr (Finset.subset_univ _), Finset.card_univ, Finset.card_pair hne]
  have h2 : 2 ≤ Fintype.card T.V := by
    have h := Finset.card_le_univ ({T.leaf b, w} : Finset T.V)
    have h1 : ({T.leaf b, w} : Finset T.V).card = 2 := Finset.card_pair hne
    have h3 : (Finset.univ : Finset T.V).card = Fintype.card T.V := Finset.card_univ
    omega
  omega

/-! ## A6g｜收缩图**无环**（`sup_edge_of_not_reachable` 路线） -/

/-- ★★★ **A6g `IsAcyclic`**：收缩图无环。

`shrinkGraph` 的定义正是「诱导 ＋ 一条边」，于是：
* `IsAcyclic.induce`：诱导子图继承 `T` 的无环性；
* `⟨T.leaf a, ·⟩` 在诱导子图里是**孤点**（唯一的 `T`-邻居 `w` 已被删）⇒ 与 `⟨z, ·⟩` 不连通
  （对走法 `cases`：`nil` 要求两端相等（与 `z ≠ leaf a` 矛盾），`cons` 要求 `⟨leaf a⟩` 有邻居（与孤点矛盾））；
* `IsAcyclic.sup_edge_of_not_reachable`：往无环图里加一条「两端不连通」的边仍无环。 -/
theorem shrinkGraph_isAcyclic (hbin : T.toCladogram.IsBinary) {a b : X} (hab : a ≠ b)
    {w z : T.V} (haw : T.graph.Adj (T.leaf a) w) (hbw : T.graph.Adj (T.leaf b) w)
    (hza : z ≠ T.leaf a) (hzb : z ≠ T.leaf b) (hzw : z ≠ w) :
    (shrinkGraph T a b w z hza).IsAcyclic := by
  have hza_mem : T.leaf a ≠ T.leaf b ∧ T.leaf a ≠ w :=
    ⟨fun h => hab (T.leaf.injective h), leaf_ne_midpoint T hbin hab haw hbw a⟩
  have hz_mem : z ≠ T.leaf b ∧ z ≠ w := ⟨hzb, hzw⟩
  have hEq : shrinkGraph T a b w z hza
      = (T.graph.induce {v : T.V | v ≠ T.leaf b ∧ v ≠ w})
        ⊔ SimpleGraph.edge ⟨T.leaf a, hza_mem⟩ ⟨z, hz_mem⟩ := by
    ext u v
    simp only [shrinkGraph, SimpleGraph.sup_adj, SimpleGraph.induce_adj, SimpleGraph.edge_adj,
      Subtype.ext_iff]
    aesop
  have hiso : ∀ v : ShrinkV T b w,
      ¬ (T.graph.induce {v : T.V | v ≠ T.leaf b ∧ v ≠ w}).Adj ⟨T.leaf a, hza_mem⟩ v := by
    intro v hv
    rw [SimpleGraph.induce_adj] at hv
    exact v.2.2 (leaf_a_adj_eq_midpoint T haw v.1 hv)
  have hnr : ¬ (T.graph.induce {v : T.V | v ≠ T.leaf b ∧ v ≠ w}).Reachable
      ⟨T.leaf a, hza_mem⟩ ⟨z, hz_mem⟩ := by
    rintro ⟨p⟩
    cases p with
    | nil => exact absurd rfl hza
    | cons h _ => exact hiso _ h
  rw [hEq]
  exact SimpleGraph.IsAcyclic.sup_edge_of_not_reachable hnr
    (T.toCladogram.isTree.isAcyclic.induce _)

/-! ## 实例｜`shrinkGraph` 的 `DecidableRel`（A7b/A8 数度、数边的前提） -/

/-- ★★ **`shrinkGraph` 的 `DecidableRel` 实例**：`shrinkGraph` 是 `def` 出来的图，
Lean **不会**自动为它的 `Adj` 找可判定性 —— 而 A7b/A8 数度、数边都要它（第 29 轮实测卡在这里）。

`Adj` 展开后是 `T.Adj _ _ ∨ (两个等式 ∧ …)`，可判定性由 `T.decAdj` 与 `DecidableEq` 给出。 -/
instance shrinkGraph_decidableRel (a b : X) (w z : T.V) (hza : z ≠ T.leaf a) :
    DecidableRel (shrinkGraph T a b w z hza).Adj :=
  fun u v => by
    unfold shrinkGraph
    infer_instance

/-! ## A7b｜收缩图的**度数不变**：`deg_G v = deg_T v.1`

收缩对每个**存活顶点**只做「删一条旧边、补一条新边」的局部平衡：

| `v` | `T` 里丢的邻居 | 补上的新边 | 度 |
|---|---|---|---|
| `T.leaf a` | `w` | `z` | 不变（恒 `1`）|
| `z` | `w` | `T.leaf a` | 不变（`1` 或 `3`）|
| 其余 | 无（`N_T v ⊆ S`）| 无 | 不变 |

⇒ `Cladogram` 的两个度字段（`leaf_iff_degree_one`、`no_degree_two`）可以**整体**从 `T` 搬过来，
不必逐点重建。三支都用 `Finset.card_bij`（显式双射比 Finset 的 `attach/map/∩` 运算稳）。 -/

/-- ★★ **A7b-0｜中点邻居的穷尽性**（把 ★★ `exists_third` 里那个「存在」的 `z` 钉在**给定**的
`z` 上，便于下游按 `z` 分情形）。 -/
theorem adj_midpoint_cases (hbin : T.toCladogram.IsBinary) {a b : X} (hab : a ≠ b) {w z : T.V}
    (haw : T.graph.Adj (T.leaf a) w) (hbw : T.graph.Adj (T.leaf b) w)
    (hwz : T.graph.Adj w z) (hza : z ≠ T.leaf a) (hzb : z ≠ T.leaf b) :
    ∀ y : T.V, T.graph.Adj w y → y = T.leaf a ∨ y = T.leaf b ∨ y = z := by
  obtain ⟨z', _, hz'a, hz'b, hexh⟩ := exists_third T hbin hab haw hbw
  have hzz : z' = z := by
    rcases hexh z hwz with h | h | h
    · exact absurd h hza
    · exact absurd h hzb
    · exact h.symm
  intro y hy
  rcases hexh y hy with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (h.trans hzz))

/-- ★★ **A7b-a｜合并叶 `⟨T.leaf a, ·⟩` 的度仍是 `1`**：`T` 里唯一的邻居 `w` 被删，
新边补上 `z`，一进一出。 -/
theorem degree_shrink_leaf_a (a b : X) (w z : T.V) (hza : z ≠ T.leaf a)
    (haw : T.graph.Adj (T.leaf a) w)
    (ha : T.leaf a ≠ T.leaf b ∧ T.leaf a ≠ w) (hz : z ≠ T.leaf b ∧ z ≠ w) :
    (shrinkGraph T a b w z hza).degree ⟨T.leaf a, ha⟩ = 1 := by
  have hG : (shrinkGraph T a b w z hza).neighborFinset ⟨T.leaf a, ha⟩ = {⟨z, hz⟩} := by
    refine Finset.eq_singleton_iff_unique_mem.mpr ⟨?_, ?_⟩
    · rw [SimpleGraph.mem_neighborFinset, shrinkGraph_adj_leaf_a_iff T a b w z hza haw ha]
    · intro y hy
      rw [SimpleGraph.mem_neighborFinset, shrinkGraph_adj_leaf_a_iff T a b w z hza haw ha] at hy
      exact Subtype.ext hy
  rw [show (shrinkGraph T a b w z hza).degree ⟨T.leaf a, ha⟩
      = ((shrinkGraph T a b w z hza).neighborFinset ⟨T.leaf a, ha⟩).card from rfl, hG]
  simp

/-- ★★ **A7b-b｜其余顶点：邻居照搬**（`N_T v ⊆ S`，新边不碰 `v`）。

双射取**恒等**：`u ↦ ⟨u, ·⟩`。两件事要证：`N_T v` 里没有 `leaf b`（叶 `b` 的唯一邻居是 `w`）、
没有 `w`（`w` 的邻居只有 `leaf a`、`leaf b`、`z`，而 `v ∉ {leaf a, z}`）。 -/
theorem degree_shrink_other (hbin : T.toCladogram.IsBinary) {a b : X} (hab : a ≠ b) {w z : T.V}
    (haw : T.graph.Adj (T.leaf a) w) (hbw : T.graph.Adj (T.leaf b) w) (hza : z ≠ T.leaf a)
    (hzb : z ≠ T.leaf b) (hwz : T.graph.Adj w z) {v : ShrinkV T b w}
    (hva : v.1 ≠ T.leaf a) (hvz : v.1 ≠ z) :
    (shrinkGraph T a b w z hza).degree v = T.graph.degree v.1 := by
  have hcases := adj_midpoint_cases T hbin hab haw hbw hwz hza hzb
  have hS : ∀ u : T.V, T.graph.Adj v.1 u → u ≠ T.leaf b ∧ u ≠ w := by
    intro u hu
    refine ⟨?_, ?_⟩
    · intro h
      exact v.2.2 (leaf_b_adj_eq_midpoint T hbw v.1 (h ▸ hu).symm)
    · intro h
      rcases hcases v.1 (h ▸ hu).symm with h1 | h1 | h1
      · exact hva h1
      · exact v.2.1 h1
      · exact hvz h1
  have hcard : (T.graph.neighborFinset v.1).card
      = ((shrinkGraph T a b w z hza).neighborFinset v).card := by
    refine Finset.card_bij (fun u hu => (⟨u, hS u ((SimpleGraph.mem_neighborFinset T.graph v.1 u).mp hu)⟩ :
      ShrinkV T b w)) ?_ ?_ ?_
    · intro u hu
      rw [SimpleGraph.mem_neighborFinset]
      exact Or.inl ((SimpleGraph.mem_neighborFinset T.graph v.1 u).mp hu)
    · intro u1 _ u2 _ h
      exact congrArg Subtype.val h
    · intro y hy
      have hadj : (shrinkGraph T a b w z hza).Adj v y :=
        (SimpleGraph.mem_neighborFinset (shrinkGraph T a b w z hza) v y).mp hy
      rcases shrinkGraph_adj_cases T a b w z hza hadj with h' | h' | h'
      · exact ⟨y.1, (SimpleGraph.mem_neighborFinset T.graph v.1 y.1).mpr h', Subtype.ext rfl⟩
      · exact absurd h'.1 hva
      · exact absurd h'.1 hvz
  change ((shrinkGraph T a b w z hza).neighborFinset v).card = (T.graph.neighborFinset v.1).card
  exact hcard.symm

/-- ★★ **A7b-c｜`v = z`：度也不变**。`w` 这条边被删、新边 `T.leaf a — z` 补上，一进一出。

双射：把 `N_T z` 里的 `w` 换成 `T.leaf a`，其余照搬。
（注意 `z` **可以**是叶 —— 3 个 taxon 时整棵树就是「`w` 带 3 个叶」；
此时 `deg_G z = deg_T z = 1`，所以本条**不能**写成 `deg = 3`。） -/
theorem degree_shrink_z (hbin : T.toCladogram.IsBinary) {a b : X} (hab : a ≠ b) {w z : T.V}
    (haw : T.graph.Adj (T.leaf a) w) (hbw : T.graph.Adj (T.leaf b) w) (hza : z ≠ T.leaf a)
    (hzb : z ≠ T.leaf b) (hwz : T.graph.Adj w z)
    (ha : T.leaf a ≠ T.leaf b ∧ T.leaf a ≠ w) (hz : z ≠ T.leaf b ∧ z ≠ w) :
    (shrinkGraph T a b w z hza).degree ⟨z, hz⟩ = T.graph.degree z := by
  have hnota : ¬ T.graph.Adj z (T.leaf a) := fun h => not_adj_leaf_a_z T haw hz.2 h.symm
  have hb_ne : ∀ u : T.V, T.graph.Adj z u → u ≠ T.leaf b := by
    intro u hu hb
    exact hz.2 (leaf_b_adj_eq_midpoint T hbw z (hb ▸ hu).symm)
  have hwNT : w ∈ T.graph.neighborFinset z := by
    rw [SimpleGraph.mem_neighborFinset]; exact hwz.symm
  have hcard : (T.graph.neighborFinset z).card
      = ((shrinkGraph T a b w z hza).neighborFinset ⟨z, hz⟩).card := by
    refine Finset.card_bij (fun u hu => if h : u = w then (⟨T.leaf a, ha⟩ : ShrinkV T b w)
      else ⟨u, ⟨hb_ne u ((SimpleGraph.mem_neighborFinset T.graph z u).mp hu), h⟩⟩) ?_ ?_ ?_
    · intro u hu
      rw [SimpleGraph.mem_neighborFinset]
      by_cases h : u = w
      · rw [dif_pos h]
        exact Or.inr (Or.inr ⟨rfl, rfl⟩)
      · rw [dif_neg h]
        exact Or.inl ((SimpleGraph.mem_neighborFinset T.graph z u).mp hu)
    · intro u1 hu1 u2 hu2 heq
      by_cases h1 : u1 = w
      · by_cases h2 : u2 = w
        · exact h1.trans h2.symm
        · rw [dif_pos h1, dif_neg h2] at heq
          have hval : u2 = T.leaf a := (congrArg Subtype.val heq).symm
          have hu2adj : T.graph.Adj z u2 := (SimpleGraph.mem_neighborFinset T.graph z u2).mp hu2
          rw [hval] at hu2adj
          exact absurd hu2adj hnota
      · by_cases h2 : u2 = w
        · rw [dif_neg h1, dif_pos h2] at heq
          have hval : u1 = T.leaf a := congrArg Subtype.val heq
          have hu1adj : T.graph.Adj z u1 := (SimpleGraph.mem_neighborFinset T.graph z u1).mp hu1
          rw [hval] at hu1adj
          exact absurd hu1adj hnota
        · rw [dif_neg h1, dif_neg h2] at heq
          exact congrArg Subtype.val heq
    · intro y hy
      have hadj : (shrinkGraph T a b w z hza).Adj ⟨z, hz⟩ y :=
        (SimpleGraph.mem_neighborFinset (shrinkGraph T a b w z hza) ⟨z, hz⟩ y).mp hy
      rcases shrinkGraph_adj_cases T a b w z hza hadj with h' | h' | h'
      · refine ⟨y.1, (SimpleGraph.mem_neighborFinset T.graph z y.1).mpr h', ?_⟩
        rw [dif_neg y.2.2]
      · exact absurd h'.1 hza
      · refine ⟨w, hwNT, ?_⟩
        rw [dif_pos rfl]
        exact Subtype.ext h'.2.symm
  change ((shrinkGraph T a b w z hza).neighborFinset ⟨z, hz⟩).card = (T.graph.neighborFinset z).card
  exact hcard.symm

/-- ★★★ **A7b｜收缩图**逐顶点**度数不变**（三支合流）。 -/
theorem degree_shrinkGraph (hbin : T.toCladogram.IsBinary) {a b : X} (hab : a ≠ b) {w z : T.V}
    (haw : T.graph.Adj (T.leaf a) w) (hbw : T.graph.Adj (T.leaf b) w) (hza : z ≠ T.leaf a)
    (hzb : z ≠ T.leaf b) (hwz : T.graph.Adj w z) :
    ∀ v : ShrinkV T b w, (shrinkGraph T a b w z hza).degree v = T.graph.degree v.1 := by
  have hla : T.leaf a ≠ T.leaf b ∧ T.leaf a ≠ w :=
    ⟨fun h => hab (T.leaf.injective h), leaf_ne_midpoint T hbin hab haw hbw a⟩
  have hzm : z ≠ T.leaf b ∧ z ≠ w := ⟨hzb, fun h => T.graph.loopless.irrefl z (h ▸ hwz)⟩
  intro v
  by_cases hva : v.1 = T.leaf a
  · have hv : v = ⟨T.leaf a, hla⟩ := Subtype.ext hva
    rw [hv, degree_shrink_leaf_a T a b w z hza haw hla hzm]
    exact ((T.isLeaf_iff_degree_eq_one (T.leaf a)).mp ⟨a, rfl⟩).symm
  · by_cases hvz : v.1 = z
    · have hv : v = ⟨z, hzm⟩ := Subtype.ext hvz
      rw [hv, degree_shrink_z T hbin hab haw hbw hza hzb hwz hla hzm]
    · exact degree_shrink_other T hbin hab haw hbw hza hzb hwz hva hvz

/-! ## A7′｜把 `Cladogram` 的两个**度字段**从 `T` 搬过来

有了 ★★★ `degree_shrinkGraph`，`leaf_iff_degree_one` 与 `no_degree_two` 各只剩「翻译」：
前者要用 `leafShrink` 的像是否就是 `T` 的叶（`MergeOld` 的成员恰好排除 `a`、`b`），
后者是 `T.toCladogram.no_degree_two` 的直接搬运。 -/

/-- ★★★ **A7′a｜叶 ⟺ 度 1**（即 `Cladogram.leaf_iff_degree_one` 字段）。

* `⟸`：`deg_G v = 1` ⇒ `deg_T v.1 = 1`（★ `degree_shrinkGraph`）⇒ `v.1` 是 `T` 的叶 `leaf x`；
  `x ≠ b`（因 `v ≠ leaf b`）；若 `x = a` 则 `v = ⟨leaf a, ·⟩ = leafShrink (inr ())`，
  否则 `x ∈ MergeOld` 且 `v = leafShrink (inl ⟨x, ·⟩)`。
* `⟹`：合并叶的度 `1`（★ `degree_shrink_leaf_a`），旧叶的度就是 `T` 里的 `1`。 -/
theorem shrinkGraph_leaf_iff_degree_one (hbin : T.toCladogram.IsBinary) {a b : X} (hab : a ≠ b)
    {w z : T.V} (haw : T.graph.Adj (T.leaf a) w) (hbw : T.graph.Adj (T.leaf b) w)
    (hza : z ≠ T.leaf a) (hzb : z ≠ T.leaf b) (hwz : T.graph.Adj w z) (v : ShrinkV T b w) :
    (∃ u : MergeIdx X a b, leafShrink T hbin hab haw hbw u = v)
      ↔ (shrinkGraph T a b w z hza).degree v = 1 := by
  have hdeg := degree_shrinkGraph T hbin hab haw hbw hza hzb hwz
  constructor
  · rintro ⟨u, rfl⟩
    cases u with
    | inl x =>
        rw [hdeg]
        exact (T.isLeaf_iff_degree_eq_one (T.leaf x.1)).mp ⟨x.1, rfl⟩
    | inr u =>
        cases u
        rw [hdeg]
        exact (T.isLeaf_iff_degree_eq_one (T.leaf a)).mp ⟨a, rfl⟩
  · intro h
    have hT1 : T.graph.degree v.1 = 1 := by
      have hv := hdeg v
      rw [hv] at h
      exact h
    obtain ⟨x, hx⟩ := (T.isLeaf_iff_degree_eq_one v.1).mpr hT1
    have hxb : x ≠ b := by
      intro h'
      have h2 : T.leaf b = v.1 := by
        rw [h'] at hx
        exact hx
      exact v.2.1 h2.symm
    by_cases hax : x = a
    · refine ⟨Sum.inr (), ?_⟩
      subst hax
      exact Subtype.ext hx
    · exact ⟨Sum.inl ⟨x, by simp [Finset.mem_sdiff, hax, hxb]⟩, Subtype.ext hx⟩

/-- ★★★ **A7′b｜无度 2 顶点**（即 `Cladogram.no_degree_two` 字段）：`T` 里没有，收缩后也不会有。 -/
theorem shrinkGraph_no_degree_two (hbin : T.toCladogram.IsBinary) {a b : X} (hab : a ≠ b)
    {w z : T.V} (haw : T.graph.Adj (T.leaf a) w) (hbw : T.graph.Adj (T.leaf b) w)
    (hza : z ≠ T.leaf a) (hzb : z ≠ T.leaf b) (hwz : T.graph.Adj w z) (v : ShrinkV T b w) :
    (shrinkGraph T a b w z hza).degree v ≠ 2 := by
  rw [degree_shrinkGraph T hbin hab haw hbw hza hzb hwz v]
  exact T.toCladogram.no_degree_two v.1

/-! ## A8 前置 A8-0｜**一般化**的中点避开引理（第二个端点不再是 `z`）

★★★ `midpoint_not_mem_support` 的第二个端点被钉死在 `z`（那是「走到 `z`」的语境）。
A8 的**旧–旧距离**要对**任意**两片非 `{a, b}` 的叶用这条，于是把它一般化成
「两端都 ∉ `{leaf a, leaf b, w}`」。证法是同一段 `getVert` 论证，只把
`z ≠ w`／`z ≠ leaf a`／`z ≠ leaf b` 换成终点 `y` 的三条同类事实。 -/
theorem midpoint_not_mem_support_gen (hbin : T.toCladogram.IsBinary) {a b : X} (hab : a ≠ b)
    {w z : T.V} (haw : T.graph.Adj (T.leaf a) w) (hbw : T.graph.Adj (T.leaf b) w)
    (hwz : T.graph.Adj w z) (hza : z ≠ T.leaf a) (hzb : z ≠ T.leaf b) (hzw : z ≠ w)
    {x y : T.V} (hxa : x ≠ T.leaf a) (hxb : x ≠ T.leaf b) (hxw : x ≠ w)
    (hya : y ≠ T.leaf a) (hyb : y ≠ T.leaf b) (hyw : y ≠ w)
    (p : T.graph.Walk x y) (hp : p.IsPath) : w ∉ p.support := by
  intro hw
  obtain ⟨z₀, hz₀adj, hz₀a, hz₀b, hexh⟩ := exists_third T hbin hab haw hbw
  have hzz₀ : z = z₀ := by
    rcases hexh z hwz with h | h | h
    · exact absurd h hza
    · exact absurd h hzb
    · exact h
  subst hzz₀
  have hda : T.graph.degree (T.leaf a) = 1 :=
    (T.isLeaf_iff_degree_eq_one (T.leaf a)).mp ⟨a, rfl⟩
  have hdb : T.graph.degree (T.leaf b) = 1 :=
    (T.isLeaf_iff_degree_eq_one (T.leaf b)).mp ⟨b, rfl⟩
  have hla : T.leaf a ∉ p.support :=
    not_mem_support_of_degree_one T hda p hp hxa hya
  have hlb : T.leaf b ∉ p.support :=
    not_mem_support_of_degree_one T hdb p hp hxb hyb
  set i := List.idxOf w p.support with hi
  have hlen : p.support.length = p.length + 1 := SimpleGraph.Walk.length_support p
  have hilt : i < p.support.length := List.idxOf_lt_length_iff.mpr hw
  have hile : i ≤ p.length := by omega
  have hwi : p.getVert i = w := by
    rw [SimpleGraph.Walk.getVert_eq_support_getElem p hile, List.getElem_idxOf hilt]
  have hi0 : 0 < i := by
    rcases Nat.eq_zero_or_pos i with h | h
    · rw [h, SimpleGraph.Walk.getVert_zero] at hwi
      exact absurd hwi hxw
    · exact h
  have hilen : i < p.length := by
    rcases lt_or_eq_of_le hile with h | h
    · exact h
    · rw [h, SimpleGraph.Walk.getVert_length] at hwi
      exact absurd hwi hyw
  have hadj0 : T.graph.Adj (p.getVert (i - 1)) w := by
    have h := SimpleGraph.Walk.adj_getVert_succ p (i := i - 1) (by omega)
    rwa [Nat.sub_add_cancel hi0, hwi] at h
  have hadj1 : T.graph.Adj w (p.getVert (i + 1)) := by
    have h := SimpleGraph.Walk.adj_getVert_succ p (i := i) (by omega)
    rwa [hwi] at h
  have hm0 : p.getVert (i - 1) ∈ p.support := SimpleGraph.Walk.getVert_mem_support p _
  have hm1 : p.getVert (i + 1) ∈ p.support := SimpleGraph.Walk.getVert_mem_support p _
  have h0 : p.getVert (i - 1) = z := by
    rcases hexh _ hadj0.symm with h | h | h
    · exact absurd (h ▸ hm0) hla
    · exact absurd (h ▸ hm0) hlb
    · exact h
  have h1 : p.getVert (i + 1) = z := by
    rcases hexh _ hadj1 with h | h | h
    · exact absurd (h ▸ hm1) hla
    · exact absurd (h ▸ hm1) hlb
    · exact h
  have hinj : p.getVert (i - 1) = p.getVert (i + 1) := h0.trans h1.symm
  have heq : i - 1 = i + 1 :=
    hp.getVert_injOn (by omega : i - 1 ≤ p.length) (by omega : i + 1 ≤ p.length) hinj
  omega

/-! ## A8 前置 A8-1｜把 `njStep` 变成**树层**的「这是一对樱桃」

`njStep` 是度量侧的 `Q`-最小性；A8 的构造需要**树层**的 `T.IsCherry a b`（公共邻居 `w`）。
桥全部现成：
* ★★ `Q_eq_neg_two_z`：`Q = −2z` ⇒ `Q` 最小 ⇔ `δ.z` 最大；
* ★★★ `z_eq_dist_add_pathLeafStatus`（Weller eq (3)）：`δ.z u v = d(u,v) + ℓ_T(p_uv)`
  ⇒ `δ.z` 的最大性**逐字**搬成树层 `d + ℓ_T` 的最大性；
* ★★★ `Cladogram.exists_isCherry_of_max_z`（Weller Thm 2）：树层最大的那对叶是樱桃。 -/
theorem isCherry_of_njStep (δ : NJ.Dissimilarity X) {T : Phylogram.{u, v} X}
    (hpos : ∀ e : Edge T.toCladogram, 0 < T.w e)
    (hT : ∀ x y : X, T.dist (T.leaf x) (T.leaf y) = δ.val x y)
    (hcard : 3 ≤ Fintype.card X) {a b : X} (h : njStep δ a b) : T.IsCherry a b := by
  have hab : a ≠ b := h.1
  have hmax : ∀ i j : X, i ≠ j → δ.z i j ≤ δ.z a b := by
    intro i j hij
    have h1 := h.2 i j hij
    rw [Q_eq_neg_two_z δ, Q_eq_neg_two_z δ] at h1
    linarith
  have hmaxT : ∀ p q : X, p ≠ q →
      T.dist (T.leaf p) (T.leaf q) + T.pathLeafStatus (T.leaf p) (T.leaf q)
        ≤ T.dist (T.leaf a) (T.leaf b) + T.pathLeafStatus (T.leaf a) (T.leaf b) := by
    intro p q hpq
    have hz := hmax p q hpq
    rwa [z_eq_dist_add_pathLeafStatus δ hpos hT hpq,
      z_eq_dist_add_pathLeafStatus δ hpos hT hab] at hz
  exact Cladogram.exists_isCherry_of_max_z hpos hcard hab hmaxT

/-! ## A8｜收缩后的 `Phylogram`：`Cladogram`（字段已齐）＋ 边权

`Cladogram` 六个字段全部到手（见 A1–A7′），本节补 `Phylogram` 的 `w` 与其非负性。
`dist` 对齐留到 A8-3。 -/

/-- ★★ **A8a｜新边的权**：`½·(d(a,w) + d(b,w)) + d(w,z)`。

来由：「新叶 `u` 挂在 `w` 上、垂枝 `½(w_a+w_b)`」给出 `d(u,x) = ½(w_a+w_b) + d(w,x)`；
再把 `w` 抑制掉（`w` 的第三邻居是 `z`），`d(w,x) = d(w,z) + d(z,x)` ⇒
`d(u,x) = [½(w_a+w_b) + d(w,z)] + d(z,x)`，方括号就是新边 `⟨leaf a⟩ — ⟨z⟩` 的权。 -/
noncomputable def shrinkNewW (a b : X) (w z : T.V) : ℝ :=
  (1 / 2) * (T.dist (T.leaf a) w + T.dist (T.leaf b) w) + T.dist w z

/-- ★★ **A8a′｜新边权严格正**：`d(a,w)`、`d(b,w)`、`d(w,z)` 三条边权都正 ⇒ 加权和正。 -/
theorem shrinkNewW_pos {a b : X} {w z : T.V} (haw : T.graph.Adj (T.leaf a) w)
    (hbw : T.graph.Adj (T.leaf b) w) (hwz : T.graph.Adj w z)
    (hpos : ∀ e : Edge T.toCladogram, 0 < T.w e) : 0 < shrinkNewW T a b w z := by
  have h1 : 0 < T.dist (T.leaf a) w := by
    rw [Phylo.TreeDist.dist_eq_w_of_adj T haw]; exact hpos _
  have h2 : 0 < T.dist (T.leaf b) w := by
    rw [Phylo.TreeDist.dist_eq_w_of_adj T hbw]; exact hpos _
  have h3 : 0 < T.dist w z := by
    rw [Phylo.TreeDist.dist_eq_w_of_adj T hwz]
    exact hpos _
  unfold shrinkNewW
  linarith

/-- ★★ **A8b｜收缩后的边权**（作用在 `Sym2 (ShrinkV)` 上；与 `Phylogram.wExt` 同构）。
新边 `⟨leaf a⟩ — ⟨z⟩` 取 ★★ `shrinkNewW`，其余旧边取原树对应边的 `T.wExt`。 -/
noncomputable def shrinkW (a b : X) (w z : T.V) (hza : z ≠ T.leaf a)
    (ha : T.leaf a ≠ T.leaf b ∧ T.leaf a ≠ w) (hz : z ≠ T.leaf b ∧ z ≠ w)
    (e : Sym2 (ShrinkV T b w)) : ℝ :=
  if e = s((⟨T.leaf a, ha⟩ : ShrinkV T b w), ⟨z, hz⟩) then shrinkNewW T a b w z
  else T.wExt (e.map (Function.Embedding.subtype (fun v : T.V => v ≠ T.leaf b ∧ v ≠ w)))

/-- ★★ **A8b′｜旧边的权就是原树的边权**（新边的判定必然失败：`T` 里 `leaf a` 与 `z` 不相邻）。

这条是 A8-3 里「走法搬移保持 `walkDist`」的**唯一**边权支点。 -/
theorem shrinkW_old (a b : X) (w z : T.V) (hza : z ≠ T.leaf a)
    (haw : T.graph.Adj (T.leaf a) w)
    (ha : T.leaf a ≠ T.leaf b ∧ T.leaf a ≠ w) (hz : z ≠ T.leaf b ∧ z ≠ w)
    (hzw : z ≠ w) {u v : T.V} (huv : T.graph.Adj u v)
    (hu : u ≠ T.leaf b ∧ u ≠ w) (hv : v ≠ T.leaf b ∧ v ≠ w) :
    shrinkW T a b w z hza ha hz s((⟨u, hu⟩ : ShrinkV T b w), ⟨v, hv⟩) = T.wExt s(u, v) := by
  have hne : s((⟨u, hu⟩ : ShrinkV T b w), ⟨v, hv⟩) ≠ s((⟨T.leaf a, ha⟩ : ShrinkV T b w),
      ⟨z, hz⟩) := by
    intro h
    rcases Sym2.eq_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have h1' : u = T.leaf a := congrArg Subtype.val h1
      have h2' : v = z := congrArg Subtype.val h2
      exact not_adj_leaf_a_z T haw hzw (h2' ▸ h1' ▸ huv)
    · have h1' : u = z := congrArg Subtype.val h1
      have h2' : v = T.leaf a := congrArg Subtype.val h2
      exact not_adj_leaf_a_z T haw hzw ((h1' ▸ h2' ▸ huv).symm)
  unfold shrinkW
  rw [if_neg hne, Sym2.map_mk]
  rfl

/-- ★★ **A8b″｜收缩后的权非负**。 -/
theorem shrinkW_nonneg (a b : X) (w z : T.V) (hza : z ≠ T.leaf a)
    (haw : T.graph.Adj (T.leaf a) w) (hbw : T.graph.Adj (T.leaf b) w) (hwz : T.graph.Adj w z)
    (ha : T.leaf a ≠ T.leaf b ∧ T.leaf a ≠ w) (hz : z ≠ T.leaf b ∧ z ≠ w)
    (hpos : ∀ e : Edge T.toCladogram, 0 < T.w e) (e : Sym2 (ShrinkV T b w)) :
    0 ≤ shrinkW T a b w z hza ha hz e := by
  unfold shrinkW
  split
  · exact le_of_lt (shrinkNewW_pos T haw hbw hwz hpos)
  · exact Phylo.TreeDist.wExt_nonneg T _

/-! ## A8-1′｜收缩后的 `Cladogram` 与 `Phylogram` -/

/-- ★★★ **A8c｜收缩后的 `Cladogram`**：顶点 `ShrinkV`、图 `shrinkGraph`、叶 `leafShrink`，
树性用 ★★★ `shrinkGraph_connected` ＋ ★★★ `shrinkGraph_isAcyclic`，
两个度字段用 ★★★ `shrinkGraph_leaf_iff_degree_one` ＋ ★★★ `shrinkGraph_no_degree_two`。 -/
noncomputable def shrinkCladogram (hbin : T.toCladogram.IsBinary) {a b : X} (hab : a ≠ b)
    {w z : T.V} (haw : T.graph.Adj (T.leaf a) w) (hbw : T.graph.Adj (T.leaf b) w)
    (hza : z ≠ T.leaf a) (hzb : z ≠ T.leaf b) (hwz : T.graph.Adj w z) :
    Cladogram (MergeIdx X a b) where
  V := ShrinkV T b w
  fintypeV := inferInstance
  decEqV := inferInstance
  graph := shrinkGraph T a b w z hza
  decAdj := shrinkGraph_decidableRel T a b w z hza
  isTree := ⟨shrinkGraph_connected T hbin hab haw hbw hwz hza hzb
      (fun h => T.graph.loopless.irrefl z (h ▸ hwz)),
    shrinkGraph_isAcyclic T hbin hab haw hbw hza hzb
      (fun h => T.graph.loopless.irrefl z (h ▸ hwz))⟩
  leaf := leafShrink T hbin hab haw hbw
  leaf_iff_degree_one := fun v =>
    shrinkGraph_leaf_iff_degree_one T hbin hab haw hbw hza hzb hwz v
  no_degree_two := fun v =>
    shrinkGraph_no_degree_two T hbin hab haw hbw hza hzb hwz v

/-- ★★★ **A8d｜收缩后的 `Phylogram`**：拓扑取 ★★★ `shrinkCladogram`，边权取 ★★ `shrinkW`。

**它就是要交给 `HasPosReal (mergeStep δ a b)` 的那棵树** —— 只差 A8-3 的 `dist` 对齐。 -/
noncomputable def shrinkPhylogram (hbin : T.toCladogram.IsBinary) {a b : X} (hab : a ≠ b)
    {w z : T.V} (haw : T.graph.Adj (T.leaf a) w) (hbw : T.graph.Adj (T.leaf b) w)
    (hza : z ≠ T.leaf a) (hzb : z ≠ T.leaf b) (hwz : T.graph.Adj w z)
    (hpos : ∀ e : Edge T.toCladogram, 0 < T.w e) :
    Phylogram (MergeIdx X a b) where
  toCladogram := shrinkCladogram T hbin hab haw hbw hza hzb hwz
  w := fun e => shrinkW T a b w z hza
    ⟨fun h => hab (T.leaf.injective h), leaf_ne_midpoint T hbin hab haw hbw a⟩
    ⟨hzb, fun h => T.graph.loopless.irrefl z (h ▸ hwz)⟩ e.1
  w_nonneg := fun e => shrinkW_nonneg T a b w z hza haw hbw hwz
    ⟨fun h => hab (T.leaf.injective h), leaf_ne_midpoint T hbin hab haw hbw a⟩
    ⟨hzb, fun h => T.graph.loopless.irrefl z (h ▸ hwz)⟩ hpos e.1

-- `V`／`graph` 投影要能在 `reducible` 透明层归约，才能与 `Sym2 (ShrinkV T b w)` 上的
-- 陈述自由互转（与 `Phylo.BunemanGraft` 对 `graftCladogram`/`graftPhylogram` 的处理一致）。
attribute [reducible] shrinkCladogram shrinkPhylogram

/-! ## A8-3 前置｜`walkDist` 的**搬移**（两个方向）

A8-3 要把「`G` 里的路径」与「`T` 里的路径」的**边权和**对上。三件器械：
① ★★ `shrinkPhylogram_wExt_eq`：`wExt` 落到 `shrinkW`；
② ★★ `shrinkPhylogram_walkDist_eq`：走法的 `walkDist` 就是 `shrinkW` 沿边表求和；
③ ★★★ 两个搬移引理（`T → G`、`G → T`），**同时**给出走法与边权和 —— 边权支点是
★★ `shrinkW_old`。 -/

/-- ★★ **A8-3a｜`wExt` 与 `shrinkW` 的桥**（`e` 是收缩图的一条边）。 -/
theorem shrinkPhylogram_wExt_eq (hbin : T.toCladogram.IsBinary) {a b : X} (hab : a ≠ b)
    {w z : T.V} (haw : T.graph.Adj (T.leaf a) w) (hbw : T.graph.Adj (T.leaf b) w)
    (hza : z ≠ T.leaf a) (hzb : z ≠ T.leaf b) (hwz : T.graph.Adj w z)
    (hpos : ∀ e : Edge T.toCladogram, 0 < T.w e) (e : Sym2 (ShrinkV T b w))
    (he : e ∈ (shrinkGraph T a b w z hza).edgeSet) :
    (shrinkPhylogram T hbin hab haw hbw hza hzb hwz hpos).wExt e
      = shrinkW T a b w z hza ⟨fun h => hab (T.leaf.injective h),
          leaf_ne_midpoint T hbin hab haw hbw a⟩
        ⟨hzb, fun h => T.graph.loopless.irrefl z (h ▸ hwz)⟩ e := by
  rw [Phylogram.wExt, dif_pos he]

/-- ★★ **A8-3b｜走法的 `walkDist` = `shrinkW` 沿边表求和**。 -/
theorem shrinkPhylogram_walkDist_eq (hbin : T.toCladogram.IsBinary) {a b : X} (hab : a ≠ b)
    {w z : T.V} (haw : T.graph.Adj (T.leaf a) w) (hbw : T.graph.Adj (T.leaf b) w)
    (hza : z ≠ T.leaf a) (hzb : z ≠ T.leaf b) (hwz : T.graph.Adj w z)
    (hpos : ∀ e : Edge T.toCladogram, 0 < T.w e) {U V : ShrinkV T b w}
    (q : (shrinkGraph T a b w z hza).Walk U V) :
    (shrinkPhylogram T hbin hab haw hbw hza hzb hwz hpos).walkDist q
      = (q.edges.map (shrinkW T a b w z hza ⟨fun h => hab (T.leaf.injective h),
          leaf_ne_midpoint T hbin hab haw hbw a⟩
        ⟨hzb, fun h => T.graph.loopless.irrefl z (h ▸ hwz)⟩)).sum := by
  rw [Phylogram.walkDist]
  congr 1
  refine List.map_congr_left ?_
  intro e he
  exact shrinkPhylogram_wExt_eq T hbin hab haw hbw hza hzb hwz hpos e (q.edges_subset_edgeSet he)

/-- ★★★ **A8-3c｜走法搬移 `T → G`（带边权和）**：若 `T` 里走法 `p` 的所有顶点都避开
`T.leaf b` 与 `w`，则它整条落进收缩图，且**边权和不变**（每步用 ★★ `shrinkW_old`）。

这是「旧–旧距离 `T' ≤ T`」那一半的引擎。 -/
theorem exists_walk_shrink_sum (a b : X) (w z : T.V) (hza : z ≠ T.leaf a)
    (haw : T.graph.Adj (T.leaf a) w) (hzw : z ≠ w)
    (ha : T.leaf a ≠ T.leaf b ∧ T.leaf a ≠ w) (hz : z ≠ T.leaf b ∧ z ≠ w) :
    ∀ {x y : T.V} (p : T.graph.Walk x y), (∀ v ∈ p.support, v ≠ T.leaf b ∧ v ≠ w) →
      ∀ (hx : x ≠ T.leaf b ∧ x ≠ w) (hy : y ≠ T.leaf b ∧ y ≠ w),
        ∃ q : (shrinkGraph T a b w z hza).Walk (⟨x, hx⟩ : ShrinkV T b w) ⟨y, hy⟩,
          (q.edges.map (shrinkW T a b w z hza ha hz)).sum = (p.edges.map T.wExt).sum := by
  intro x y p
  induction p with
  | nil => intro _ hx hy; exact ⟨SimpleGraph.Walk.nil, rfl⟩
  | @cons u v x' h q ih =>
      intro hsupp hx hy
      have hsub : ∀ t ∈ q.support, t ≠ T.leaf b ∧ t ≠ w := by
        intro t ht
        exact hsupp t (by rw [SimpleGraph.Walk.support_cons]; exact List.mem_cons_of_mem _ ht)
      have hv : v ≠ T.leaf b ∧ v ≠ w :=
        hsupp v (by
          rw [SimpleGraph.Walk.support_cons]
          exact List.mem_cons_of_mem _ (SimpleGraph.Walk.start_mem_support q))
      obtain ⟨q', hq'⟩ := ih hsub hv hy
      refine ⟨SimpleGraph.Walk.cons (shrinkGraph_adj_of_adj T a b w z hza h) q', ?_⟩
      rw [SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_cons, List.map_cons, List.sum_cons,
        List.map_cons, List.sum_cons, shrinkW_old T a b w z hza haw ha hz hzw h hx hv, hq']

/-- ★★★ **A8-3d｜走法搬移 `G → T`（带边权和）**：若收缩图里走法 `q` 的支撑集**不含**
`⟨T.leaf a, ·⟩`，则它完全由旧边组成，可搬回 `T` 且**边权和不变**。

这是「旧–旧距离 `T' ≥ T`」那一半的引擎（`⟨leaf a⟩` 在 `G` 里度为 `1`，
故任何以别的顶点为端点的**路径**都不会经过它 —— 由 ★★ `not_mem_support_of_degree_one`）。 -/
theorem exists_walk_of_shrink_sum (a b : X) (w z : T.V) (hza : z ≠ T.leaf a)
    (haw : T.graph.Adj (T.leaf a) w) (hzw : z ≠ w)
    (ha : T.leaf a ≠ T.leaf b ∧ T.leaf a ≠ w) (hz : z ≠ T.leaf b ∧ z ≠ w) :
    ∀ {U V : ShrinkV T b w} (q : (shrinkGraph T a b w z hza).Walk U V),
      (∀ v ∈ q.support, v.1 ≠ T.leaf a) →
        ∃ p : T.graph.Walk U.1 V.1,
          (q.edges.map (shrinkW T a b w z hza ha hz)).sum = (p.edges.map T.wExt).sum := by
  intro U V q
  induction q with
  | nil => intro _; exact ⟨SimpleGraph.Walk.nil, rfl⟩
  | @cons U0 M V0 h q ih =>
      intro hsupp
      have hsub : ∀ v ∈ q.support, v.1 ≠ T.leaf a := fun v hv =>
        hsupp v (by rw [SimpleGraph.Walk.support_cons]; exact List.mem_cons_of_mem _ hv)
      have hU : U0.1 ≠ T.leaf a :=
        hsupp U0 (by rw [SimpleGraph.Walk.support_cons]; exact List.mem_cons_self)
      have hM : M.1 ≠ T.leaf a :=
        hsupp M (by
          rw [SimpleGraph.Walk.support_cons]
          exact List.mem_cons_of_mem _ (SimpleGraph.Walk.start_mem_support q))
      obtain ⟨q', hq'⟩ := ih hsub
      have htedge : T.graph.Adj U0.1 M.1 := by
        rcases shrinkGraph_adj_cases T a b w z hza h with h' | h' | h'
        · exact h'
        · exact absurd h'.1 hU
        · exact absurd h'.2 hM
      refine ⟨SimpleGraph.Walk.cons htedge q', ?_⟩
      rw [SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_cons, List.map_cons, List.sum_cons,
        List.map_cons, List.sum_cons, shrinkW_old T a b w z hza haw ha hz hzw htedge U0.2 M.2, hq']

/-! ## A8-3｜`dist` 对齐（三支）

目标：`T'.dist (leaf' u) (leaf' v) = (mergeStep δ a b).val u v`。
三支分别是「旧–旧」（路径不过 `w`，两边走法互搬、边权和不变）、「新–旧」
（★★★ `StrictCherry.mergeStep_val_eq` 的算术核 ＋ `w` 在路径上）、「新–新」（`dist_self`）。 -/

/-- ★★★ **A8-3e｜旧–旧距离（一般形式）**：若 `u, v` 都**不是**合并叶的像
（`u.1, v.1 ≠ T.leaf a`），则 `T'.dist u v = T.dist u.1 v.1`。

两个方向：
* `≤`：`T` 里 `u.1 → v.1` 的路径**避开** `leaf b`（度 1）与 `w`（★★ 一般化中点避开），
  整条搬进 `G`，边权和不变（★★★ `exists_walk_shrink_sum`）⇒ `dist' ≤ walkDist = dist_T`；
* `≥`：`G` 里那条唯一路径**不含** `⟨leaf a⟩`（它在 `G` 里度为 1，且不是端点 ⇒
  ★★ `not_mem_support_of_degree_one`），搬回 `T` 得一条 `u.1 → v.1` 的走法
  ⇒ `dist_T ≤ walkDist ≤ dist'`。

这一支是 `dist` 对齐的地基：新–旧那支要用 `u = ⟨z, ·⟩`（`z` 不是叶标签的像）。 -/
theorem shrinkPhylogram_dist_old (hbin : T.toCladogram.IsBinary) {a b : X} (hab : a ≠ b)
    {w z : T.V} (haw : T.graph.Adj (T.leaf a) w) (hbw : T.graph.Adj (T.leaf b) w)
    (hza : z ≠ T.leaf a) (hzb : z ≠ T.leaf b) (hwz : T.graph.Adj w z)
    (hpos : ∀ e : Edge T.toCladogram, 0 < T.w e) {u v : ShrinkV T b w}
    (hua : u.1 ≠ T.leaf a) (hva : v.1 ≠ T.leaf a) :
    (shrinkPhylogram T hbin hab haw hbw hza hzb hwz hpos).dist u v = T.dist u.1 v.1 := by
  have hzw : z ≠ w := fun h => T.graph.loopless.irrefl z (h ▸ hwz)
  have ha : T.leaf a ≠ T.leaf b ∧ T.leaf a ≠ w :=
    ⟨fun h => hab (T.leaf.injective h), leaf_ne_midpoint T hbin hab haw hbw a⟩
  have hz : z ≠ T.leaf b ∧ z ≠ w := ⟨hzb, hzw⟩
  by_cases huv : u.1 = v.1
  · have hsub : u = v := Subtype.ext huv
    rw [hsub]
    simp only [Phylogram.dist_self]
  · have h1 : (shrinkPhylogram T hbin hab haw hbw hza hzb hwz hpos).dist u v
        ≤ T.dist u.1 v.1 := by
      set P := (T.existsUnique_path u.1 v.1).choose with hPdef
      have hPpath : P.IsPath := (T.existsUnique_path u.1 v.1).choose_spec.1
      have hwP : w ∉ P.support :=
        midpoint_not_mem_support_gen T hbin hab haw hbw hwz hza hzb hzw hua u.2.1 u.2.2
          hva v.2.1 v.2.2 P hPpath
      have hdb : T.graph.degree (T.leaf b) = 1 :=
        (T.isLeaf_iff_degree_eq_one (T.leaf b)).mp ⟨b, rfl⟩
      have hbP : T.leaf b ∉ P.support :=
        not_mem_support_of_degree_one T hdb P hPpath u.2.1 v.2.1
      have hsupp : ∀ t ∈ P.support, t ≠ T.leaf b ∧ t ≠ w := by
        intro t ht
        exact ⟨fun h => hbP (h ▸ ht), fun h => hwP (h ▸ ht)⟩
      obtain ⟨q, hq⟩ := exists_walk_shrink_sum T a b w z hza haw hzw ha hz P hsupp u.2 v.2
      have hqw : (shrinkPhylogram T hbin hab haw hbw hza hzb hwz hpos).walkDist q
          = T.dist u.1 v.1 := by
        have hsum : (P.edges.map T.wExt).sum = T.dist u.1 v.1 := by
          have hwalk : (P.edges.map T.wExt).sum = T.walkDist P := rfl
          rw [hwalk, ← Phylo.TreeDist.dist_eq_walkDist_of_isPath T P hPpath]
        rw [shrinkPhylogram_walkDist_eq T hbin hab haw hbw hza hzb hwz hpos q, hq]
        exact hsum
      have hdw : (shrinkPhylogram T hbin hab haw hbw hza hzb hwz hpos).dist u v
          ≤ (shrinkPhylogram T hbin hab haw hbw hza hzb hwz hpos).walkDist q :=
        Phylo.Contract.dist_le_walkDist
          (shrinkPhylogram T hbin hab haw hbw hza hzb hwz hpos) q
      linarith
    have h2 : T.dist u.1 v.1 ≤ (shrinkPhylogram T hbin hab haw hbw hza hzb hwz hpos).dist u v := by
      obtain ⟨q', hq'path, -⟩ :=
        (shrinkPhylogram T hbin hab haw hbw hza hzb hwz hpos).existsUnique_path u v
      have hdeg : (shrinkPhylogram T hbin hab haw hbw hza hzb hwz hpos).graph.degree
          (⟨T.leaf a, ha⟩ : ShrinkV T b w) = 1 :=
        degree_shrink_leaf_a T a b w z hza haw ha hz
      have hqa : (⟨T.leaf a, ha⟩ : ShrinkV T b w) ∉ q'.support :=
        not_mem_support_of_degree_one
          (T := shrinkPhylogram T hbin hab haw hbw hza hzb hwz hpos) hdeg q' hq'path
          (fun h => hua (congrArg Subtype.val h))
          (fun h => hva (congrArg Subtype.val h))
      obtain ⟨p, hp⟩ := exists_walk_of_shrink_sum T a b w z hza haw hzw ha hz q'
        (fun t ht hcon => hqa (by
          have hteq : t = (⟨T.leaf a, ha⟩ : ShrinkV T b w) := Subtype.ext hcon
          rwa [hteq] at ht))
      have e1 : T.dist u.1 v.1 ≤ T.walkDist p := Phylo.Contract.dist_le_walkDist T p
      have e3 : T.walkDist p = (q'.edges.map (shrinkW T a b w z hza ha hz)).sum := hp.symm
      have e4 : (q'.edges.map (shrinkW T a b w z hza ha hz)).sum
          = (shrinkPhylogram T hbin hab haw hbw hza hzb hwz hpos).walkDist q' :=
        (shrinkPhylogram_walkDist_eq T hbin hab haw hbw hza hzb hwz hpos q').symm
      have e5 : (shrinkPhylogram T hbin hab haw hbw hza hzb hwz hpos).walkDist q'
          = (shrinkPhylogram T hbin hab haw hbw hza hzb hwz hpos).dist u v :=
        (Phylo.TreeDist.dist_eq_walkDist_of_isPath _ q' hq'path).symm
      linarith
    exact le_antisymm h1 h2

/-- ★★★ **A8-3e′｜旧–旧距离（叶标签形式）**：`x, y ∉ {a,b}` 时
`T'.dist (leaf' x) (leaf' y) = δ(x,y)`。由 ★★★ `shrinkPhylogram_dist_old` ＋ 实现树的 `hT`。 -/
theorem shrinkPhylogram_dist_inl_inl (δ : NJ.Dissimilarity X) (hbin : T.toCladogram.IsBinary)
    {a b : X} (hab : a ≠ b) {w z : T.V} (haw : T.graph.Adj (T.leaf a) w)
    (hbw : T.graph.Adj (T.leaf b) w) (hza : z ≠ T.leaf a) (hzb : z ≠ T.leaf b)
    (hwz : T.graph.Adj w z) (hpos : ∀ e : Edge T.toCladogram, 0 < T.w e)
    (hT : ∀ x y : X, T.dist (T.leaf x) (T.leaf y) = δ.val x y) (x y : MergeOld X a b) :
    (shrinkPhylogram T hbin hab haw hbw hza hzb hwz hpos).dist
        ((shrinkCladogram T hbin hab haw hbw hza hzb hwz).leaf (Sum.inl x))
        ((shrinkCladogram T hbin hab haw hbw hza hzb hwz).leaf (Sum.inl y))
      = δ.val x.1 y.1 := by
  have hxa : T.leaf x.1 ≠ T.leaf a := fun h => mergeOld_ne_left x (T.leaf.injective h)
  have hya : T.leaf y.1 ≠ T.leaf a := fun h => mergeOld_ne_left y (T.leaf.injective h)
  have hxb : T.leaf x.1 ≠ T.leaf b := fun h => mergeOld_ne_right x (T.leaf.injective h)
  have hyb : T.leaf y.1 ≠ T.leaf b := fun h => mergeOld_ne_right y (T.leaf.injective h)
  have hxw : T.leaf x.1 ≠ w := leaf_ne_midpoint T hbin hab haw hbw x.1
  have hyw : T.leaf y.1 ≠ w := leaf_ne_midpoint T hbin hab haw hbw y.1
  have hxu : ((shrinkCladogram T hbin hab haw hbw hza hzb hwz).leaf (Sum.inl x))
      = (⟨T.leaf x.1, ⟨hxb, hxw⟩⟩ : ShrinkV T b w) := Subtype.ext rfl
  have hyu : ((shrinkCladogram T hbin hab haw hbw hza hzb hwz).leaf (Sum.inl y))
      = (⟨T.leaf y.1, ⟨hyb, hyw⟩⟩ : ShrinkV T b w) := Subtype.ext rfl
  rw [hxu, hyu, shrinkPhylogram_dist_old T hbin hab haw hbw hza hzb hwz hpos hxa hya]
  exact hT x.1 y.1

/-- ★★★ **A8-3f｜新–旧距离**：`x ∉ {a,b}` 时
`T'.dist (leaf' u) (leaf' x) = ½·δ(a,x) + ½·δ(b,x)`（`u` 是合并标签）。

三步：
1. 在 `G` 里 `⟨leaf a, ·⟩` 的**唯一邻居**是 `⟨z, ·⟩`（★★ `shrinkGraph_adj_leaf_a_iff`）
   ⇒ 路径第一步必到 `⟨z, ·⟩` ⇒ `dist' = wExt(新边) + dist' ⟨z⟩ ⟨leaf x⟩ = shrinkNewW + …`；
2. `dist' ⟨z⟩ ⟨leaf x⟩ = d_T(z, x)`（★★★ `shrinkPhylogram_dist_old`：两者都 ≠ `leaf a`）；
3. 算术：★★★ `StrictCherry.mergeStep_val_eq` 给 `½δ(x,a)+½δ(x,b) = ½(w_a+w_b) + d(w,x)`，
   而 `d(w,x) = d(w,z) + d(z,x)`（`w` 到非樱桃叶的路径第一步必到 `z`）⇒ 与 `shrinkNewW` 相符。 -/
theorem shrinkPhylogram_dist_inr_inl (δ : NJ.Dissimilarity X) (hbin : T.toCladogram.IsBinary)
    {a b : X} (hab : a ≠ b) {w z : T.V} (haw : T.graph.Adj (T.leaf a) w)
    (hbw : T.graph.Adj (T.leaf b) w) (hza : z ≠ T.leaf a) (hzb : z ≠ T.leaf b)
    (hwz : T.graph.Adj w z) (hpos : ∀ e : Edge T.toCladogram, 0 < T.w e)
    (hc : T.IsCherry a b) (hT : ∀ x y : X, T.dist (T.leaf x) (T.leaf y) = δ.val x y)
    (x : MergeOld X a b) :
    (shrinkPhylogram T hbin hab haw hbw hza hzb hwz hpos).dist
        ((shrinkCladogram T hbin hab haw hbw hza hzb hwz).leaf (Sum.inr ()))
        ((shrinkCladogram T hbin hab haw hbw hza hzb hwz).leaf (Sum.inl x))
      = (1 / 2) * δ.val a x.1 + (1 - 1 / 2) * δ.val b x.1 := by
  have hzw : z ≠ w := fun h => T.graph.loopless.irrefl z (h ▸ hwz)
  have ha : T.leaf a ≠ T.leaf b ∧ T.leaf a ≠ w :=
    ⟨fun h => hab (T.leaf.injective h), leaf_ne_midpoint T hbin hab haw hbw a⟩
  have hz : z ≠ T.leaf b ∧ z ≠ w := ⟨hzb, hzw⟩
  have hxa : T.leaf x.1 ≠ T.leaf a := fun h => mergeOld_ne_left x (T.leaf.injective h)
  have hxb : T.leaf x.1 ≠ T.leaf b := fun h => mergeOld_ne_right x (T.leaf.injective h)
  have hxw : T.leaf x.1 ≠ w := leaf_ne_midpoint T hbin hab haw hbw x.1
  -- 端点的规范形式
  have hu : ((shrinkCladogram T hbin hab haw hbw hza hzb hwz).leaf (Sum.inr ()))
      = (⟨T.leaf a, ha⟩ : ShrinkV T b w) := Subtype.ext rfl
  have hxu : ((shrinkCladogram T hbin hab haw hbw hza hzb hwz).leaf (Sum.inl x))
      = (⟨T.leaf x.1, ⟨hxb, hxw⟩⟩ : ShrinkV T b w) := Subtype.ext rfl
  rw [hu, hxu]
  -- ① 路径第一步必到 `⟨z, ·⟩`
  have hstep : (shrinkPhylogram T hbin hab haw hbw hza hzb hwz hpos).dist
      (⟨T.leaf a, ha⟩ : ShrinkV T b w) ⟨T.leaf x.1, ⟨hxb, hxw⟩⟩
      = shrinkNewW T a b w z
        + (shrinkPhylogram T hbin hab haw hbw hza hzb hwz hpos).dist
            (⟨z, hz⟩ : ShrinkV T b w) ⟨T.leaf x.1, ⟨hxb, hxw⟩⟩ := by
    have hne : (⟨T.leaf a, ha⟩ : ShrinkV T b w) ≠ ⟨T.leaf x.1, ⟨hxb, hxw⟩⟩ := by
      intro h
      exact hxa (congrArg Subtype.val h).symm
    obtain ⟨P, hPpath, -⟩ :=
      (shrinkPhylogram T hbin hab haw hbw hza hzb hwz hpos).existsUnique_path
        (⟨T.leaf a, ha⟩ : ShrinkV T b w) ⟨T.leaf x.1, ⟨hxb, hxw⟩⟩
    obtain ⟨v', hv', P', hsplit⟩ := SimpleGraph.Walk.exists_eq_cons_of_ne hne P
    have hv'z : v' = (⟨z, hz⟩ : ShrinkV T b w) := by
      have h1 : v'.1 = z := by
        rw [shrinkGraph_adj_leaf_a_iff T a b w z hza haw ha] at hv'
        exact hv'
      exact Subtype.ext h1
    subst hv'z
    have hP'path : P'.IsPath := by
      rw [hsplit] at hPpath
      exact SimpleGraph.Walk.IsPath.of_cons hPpath
    have hnew : (shrinkPhylogram T hbin hab haw hbw hza hzb hwz hpos).wExt
        s((⟨T.leaf a, ha⟩ : ShrinkV T b w), ⟨z, hz⟩) = shrinkNewW T a b w z := by
      rw [shrinkPhylogram_wExt_eq T hbin hab haw hbw hza hzb hwz hpos _
        (by rw [SimpleGraph.mem_edgeSet]; exact Or.inr (Or.inl ⟨rfl, rfl⟩))]
      unfold shrinkW
      rw [if_pos rfl]
    rw [Phylo.TreeDist.dist_eq_walkDist_of_isPath _ P hPpath, hsplit,
      Phylogram.walkDist, SimpleGraph.Walk.edges_cons, List.map_cons, List.sum_cons, hnew,
      ← Phylogram.walkDist, ← Phylo.TreeDist.dist_eq_walkDist_of_isPath _ P' hP'path]
  rw [hstep]
  -- ② `⟨z⟩ → ⟨leaf x⟩` 是旧–旧
  have hzold : (shrinkPhylogram T hbin hab haw hbw hza hzb hwz hpos).dist
      (⟨z, hz⟩ : ShrinkV T b w) ⟨T.leaf x.1, ⟨hxb, hxw⟩⟩ = T.dist z (T.leaf x.1) :=
    shrinkPhylogram_dist_old T hbin hab haw hbw hza hzb hwz hpos hza hxa
  rw [hzold]
  -- ③ 算术：`d(w,x) = d(w,z) + d(z,x)`
  have hbw' : T.leaf b ≠ w := leaf_ne_midpoint T hbin hab haw hbw b
  have hsplit2 : T.dist w (T.leaf x.1) = T.dist w z + T.dist z (T.leaf x.1) := by
    have hne : w ≠ T.leaf x.1 := hxw.symm
    obtain ⟨P, hPpath, -⟩ := T.existsUnique_path w (T.leaf x.1)
    obtain ⟨v', hv', P', hsplit⟩ := SimpleGraph.Walk.exists_eq_cons_of_ne hne P
    have hcases := adj_midpoint_cases T hbin hab haw hbw hwz hza hzb
    have hda : T.graph.degree (T.leaf a) = 1 :=
      (T.isLeaf_iff_degree_eq_one (T.leaf a)).mp ⟨a, rfl⟩
    have hdb : T.graph.degree (T.leaf b) = 1 :=
      (T.isLeaf_iff_degree_eq_one (T.leaf b)).mp ⟨b, rfl⟩
    have hfirst : v' ∈ P.support := by
      rw [hsplit, SimpleGraph.Walk.support_cons]
      exact List.mem_cons_of_mem _ (SimpleGraph.Walk.start_mem_support P')
    have hv'z : v' = z := by
      rcases hcases v' hv' with h | h | h
      · exfalso
        have hmem : T.leaf a ∈ P.support := by rwa [h] at hfirst
        rcases leaf_mem_support_eq_end T hda P hPpath.support_nodup hmem with h' | h'
        · exact ha.2 h'
        · exact hxa h'.symm
      · exfalso
        have hmem : T.leaf b ∈ P.support := by rwa [h] at hfirst
        rcases leaf_mem_support_eq_end T hdb P hPpath.support_nodup hmem with h' | h'
        · exact hbw' h'
        · exact hxb h'.symm
      · exact h
    subst v'
    have hP'path : P'.IsPath := by
      rw [hsplit] at hPpath
      exact SimpleGraph.Walk.IsPath.of_cons hPpath
    have hwz' : T.dist w z = T.wExt s((w : T.V), (z : T.V)) :=
      Phylo.TreeDist.dist_eq_wExt_of_adj T hv'
    rw [Phylo.TreeDist.dist_eq_walkDist_of_isPath T P hPpath, hsplit,
      Phylogram.walkDist, SimpleGraph.Walk.edges_cons, List.map_cons, List.sum_cons, hwz',
      ← Phylogram.walkDist, ← Phylo.TreeDist.dist_eq_walkDist_of_isPath _ P' hP'path]
  obtain ⟨w', haw', hbw'', hEq⟩ := Phylo.Stat.StrictCherry.mergeStep_val_eq δ hT hc (mergeOld_ne_left x) (mergeOld_ne_right x)
  have hw'w : w' = w := leaf_a_adj_eq_midpoint T haw w' haw'
  subst hw'w
  have hs1 : δ.val a x.1 = δ.val x.1 a := δ.symm a x.1
  have hs2 : δ.val b x.1 = δ.val x.1 b := δ.symm b x.1
  have hhalf : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
  unfold shrinkNewW
  linarith

/-- ★★★ **A8-3h｜收缩后每条边权都严格正**（`HasPosReal` 的最后一块）。

新边取 ★★ `shrinkNewW`（★ `shrinkNewW_pos` 给正性）；旧边取 `T.wExt (像)`，
★★ `shrinkGraph_adj_cases` 保证它不是新边那两支 ⇒ 像确实是 `T`-边 ⇒ 用 `hpos`。 -/
theorem shrinkW_pos (hbin : T.toCladogram.IsBinary) {a b : X} (hab : a ≠ b) {w z : T.V}
    (haw : T.graph.Adj (T.leaf a) w) (hbw : T.graph.Adj (T.leaf b) w) (hza : z ≠ T.leaf a)
    (hzb : z ≠ T.leaf b) (hwz : T.graph.Adj w z)
    (hpos : ∀ e : Edge T.toCladogram, 0 < T.w e)
    (ha : T.leaf a ≠ T.leaf b ∧ T.leaf a ≠ w) (hz : z ≠ T.leaf b ∧ z ≠ w)
    {u v : ShrinkV T b w} (huv : (shrinkGraph T a b w z hza).Adj u v) :
    0 < shrinkW T a b w z hza ha hz s(u, v) := by
  unfold shrinkW
  by_cases hnew : s(u, v) = s((⟨T.leaf a, ha⟩ : ShrinkV T b w), ⟨z, hz⟩)
  · rw [if_pos hnew]
    exact shrinkNewW_pos T haw hbw hwz hpos
  · rw [if_neg hnew, Sym2.map_mk]
    have htedge : T.graph.Adj u.1 v.1 := by
      rcases shrinkGraph_adj_cases T a b w z hza huv with h' | h' | h'
      · exact h'
      · exfalso
        exact hnew (by
          rw [show u = (⟨T.leaf a, ha⟩ : ShrinkV T b w) from Subtype.ext h'.1,
            show v = (⟨z, hz⟩ : ShrinkV T b w) from Subtype.ext h'.2])
      · exfalso
        exact hnew (by
          rw [show u = (⟨z, hz⟩ : ShrinkV T b w) from Subtype.ext h'.1,
            show v = (⟨T.leaf a, ha⟩ : ShrinkV T b w) from Subtype.ext h'.2, Sym2.eq_swap])
    change 0 < T.wExt s(u.1, v.1)
    rw [Phylo.TreeDist.wExt_eq_w T ((SimpleGraph.mem_edgeSet T.graph).mpr htedge)]
    exact hpos _

/-- ★★★ **A8-3i｜`dist` 对齐（三支合流）**：
`∀ u v : MergeIdx X a b，T'.dist (leaf' u) (leaf' v) = (mergeStep δ a b).val u v`。 -/
theorem shrinkPhylogram_dist (δ : NJ.Dissimilarity X) (hbin : T.toCladogram.IsBinary)
    {a b : X} (hab : a ≠ b) {w z : T.V} (haw : T.graph.Adj (T.leaf a) w)
    (hbw : T.graph.Adj (T.leaf b) w) (hza : z ≠ T.leaf a) (hzb : z ≠ T.leaf b)
    (hwz : T.graph.Adj w z) (hpos : ∀ e : Edge T.toCladogram, 0 < T.w e)
    (hc : T.IsCherry a b) (hT : ∀ x y : X, T.dist (T.leaf x) (T.leaf y) = δ.val x y) :
    ∀ u v : MergeIdx X a b,
      (shrinkPhylogram T hbin hab haw hbw hza hzb hwz hpos).dist
          ((shrinkCladogram T hbin hab haw hbw hza hzb hwz).leaf u)
          ((shrinkCladogram T hbin hab haw hbw hza hzb hwz).leaf v)
        = (mergeStep δ a b).val u v := by
  have hzw : z ≠ w := fun h => T.graph.loopless.irrefl z (h ▸ hwz)
  intro u v
  cases u with
  | inl x =>
      cases v with
      | inl y =>
          rw [shrinkPhylogram_dist_inl_inl T δ hbin hab haw hbw hza hzb hwz hpos hT x y]
          rfl
      | inr y =>
          cases y
          rw [Phylo.TreeDist.dist_comm,
            shrinkPhylogram_dist_inr_inl T δ hbin hab haw hbw hza hzb hwz hpos hc hT x]
          simp only [mergeStep, mergeDissim, mergeVal]
  | inr x =>
      cases x
      cases v with
      | inl y =>
          rw [shrinkPhylogram_dist_inr_inl T δ hbin hab haw hbw hza hzb hwz hpos hc hT y]
          simp only [mergeStep, mergeDissim, mergeVal]
      | inr y =>
          cases y
          rw [Phylogram.dist_self]
          rfl

/-- ★★★ **A8-3j｜收缩后的树仍是 binary**（`HasPosRealBinary` 的**归纳不变式**要这条）。

`IsBinary T := ∀ v, ¬ IsLeaf v → degree v = 3`。用 ★★★ `degree_shrinkGraph`
（`deg_G v = deg_T v.1`）把度数搬回 `T`；叶性判据走反证：
若 `v.1` 是 `T` 的叶则 `deg_T = 1 ⇒ deg_G = 1`，由 ★★★ `shrinkGraph_leaf_iff_degree_one`
得 `v` 是收缩树的叶，与假设矛盾。 -/
theorem shrinkPhylogram_isBinary (hbin : T.toCladogram.IsBinary) {a b : X} (hab : a ≠ b)
    {w z : T.V} (haw : T.graph.Adj (T.leaf a) w) (hbw : T.graph.Adj (T.leaf b) w)
    (hza : z ≠ T.leaf a) (hzb : z ≠ T.leaf b) (hwz : T.graph.Adj w z)
    (hpos : ∀ e : Edge T.toCladogram, 0 < T.w e) :
    (shrinkPhylogram T hbin hab haw hbw hza hzb hwz hpos).toCladogram.IsBinary := by
  intro v hv
  have hdeg := degree_shrinkGraph T hbin hab haw hbw hza hzb hwz v
  have hnotleaf : ¬ T.toCladogram.IsLeaf v.1 := by
    intro hleaf
    have h1 : T.graph.degree v.1 = 1 := (T.isLeaf_iff_degree_eq_one v.1).mp hleaf
    have h2 : (shrinkGraph T a b w z hza).degree v = 1 := by
      rw [hdeg, h1]
    exact hv ((shrinkGraph_leaf_iff_degree_one T hbin hab haw hbw hza hzb hwz v).mpr h2)
  rw [hdeg]
  exact hbin v.1 hnotleaf

end Phylo.Stat.NJShrink
