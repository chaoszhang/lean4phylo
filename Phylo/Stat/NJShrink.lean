/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.AttesonRadius

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
-/

noncomputable section

universe u v

namespace Phylo.Stat.NJShrink

open SimpleGraph
open NJ NJ.Dissimilarity

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

end Phylo.Stat.NJShrink
