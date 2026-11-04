/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.Stat.CASTERNJStep

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
| A4 | 第三邻居 `z` 的存在 | ⏳ 下一步 |
| A6 | 图（诱导 ＋ 一条边）与 `IsTree` | ⏳ |
| A7 | `leaf_iff_degree_one` / `no_degree_two` | ⏳ |
| A8 | 边权、`dist` 对齐、`HasPosReal` 收口 | ⏳ |

**纪律**：零 sorry / axiom / opaque。本文件只加新声明，不动任何既有定理。

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

end Phylo.Stat.NJShrink
