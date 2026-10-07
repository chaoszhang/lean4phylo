/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.Buneman

/-!
# `Phylo.BunemanGraft` —— Buneman 归纳步的**图手术**（挂两片叶）

**文献**：P. Buneman, *A Note on the Metric Properties of Trees*,
J. Combinatorial Theory (B) **17** (1974) 48–50，
`references/md/Buneman1974_MetricPropertiesOfTrees.md` **第 74–121 行**（Theorem 2 的归纳证明）。

**转录 vs 改编**：本文件是**改编**。`Phylo/Buneman.lean` 已把第 78–121 行的**全部算术**做完
（选极大三元组、扩张相异度 `δ'`、挂叶恒等式 (2a)/(2b)）；本文件补第 119–121 行
「*p and q can then be attached by edges of weight `d(p,t)` and `d(q,t)`*」的**图论内容**：
把一棵 `Phylogram` 的一片叶 `t` 改造成度 3 的内部顶点，接上两片新叶。

顶点编码用 `V ⊕ Fin 2`：`Sum.inl v` = 旧顶点，`Sum.inr i` = 第 `i` 片新叶。
旧顶点之间的邻接 `(graftGraph G t).Adj (Sum.inl a) (Sum.inl b) ↔ G.Adj a b`
（★ `Phylo.graftGraph_adj_inl_inl`），故 `graftGraph G t` 是把 `G` 原样嵌入、再加两条挂边。

## ★ 已证内容（本文件）

* **★★★ `Phylo.graftGraph`** —— 挂叶手术的**图**（`SimpleGraph (V ⊕ Fin 2)`）。
* **★★★ `Phylo.graftGraph_adj_inl_inl`** —— 旧顶点之间的邻接**与原图一致**（挂叶不动旧边）。
* **★★★ `Phylo.graftGraph_adj_inl_inr`** / **★★★ `Phylo.graftGraph_adj_inr_inl`** ——
  两条挂边：`Sum.inl x` 与第 `i` 片新叶相邻 **⟺** `x = t`。
* **★★★ `Phylo.graftGraph_adj_not_inr_inr`** —— 两片新叶之间**无边**（这正是「新叶度 1、
  故 `leaf_iff_degree_one` 成立」的来源）。
* **★★★ `Phylo.graftGraph_isTree`** —— **挂叶保持树性**：`G.IsTree → (graftGraph G t).IsTree`
  （对**任意**顶点 `t`，不要求 `t` 是叶；要成为树只需连通 + 边数计数）。
* **★★★ `Phylo.graftGraph_connected`** —— 挂叶保持连通（`G.Connected → (graftGraph G t).Connected`）。
* **★★★ `Phylo.graftGraph_edgeSet_subset`** —— 边集分解：
  `(graftGraph G t).edgeSet ⊆ graftOldEdges G ∪ graftNewEdges t`
  （每条边或是旧边、或是两条新挂边之一）。
* **★★ `Phylo.graftOldEdges`** / **★★ `Phylo.graftNewEdges`** —— 旧边的像、两条新挂边（`Set (Sym2 _)`）。
* **★★ `Phylo.graftGraphHom`** —— 把 `G` 嵌入 `graftGraph G t` 的图同态（`x ↦ Sum.inl x`）。
* **★★ `Phylo.ncard_graftOldEdges`** / **★★ `Phylo.ncard_graftNewEdges`** ——
  `Sym2.map Sum.inl` 在 `G.edgeSet` 上单射（`Sym2.map.injective`），故旧边**不重复**；
  两条新挂边不同，故新边恰 **2** 条。
* **★★ `Phylo.ncard_edgeSet_eq_natCard`** —— `Set.ncard` 与 `Nat.card` 的桥
  （`Nat.card ↑H.edgeSet = H.edgeSet.ncard`）。
* **★★ `Phylo.card_edgeSet_graftGraph_le`** —— **边数上界**：
  `Nat.card ↑(graftGraph G t).edgeSet ≤ Nat.card ↑G.edgeSet + 2`（挂叶最多加两条边）。

**`graftGraph_isTree` 的证法（已落地的路线）**：不直接做「环 → 桥」的图论论证，而是
`SimpleGraph.isTree_iff_connected_and_card`：
连通性由 ★★★ `Phylo.graftGraph_connected` 给出；计数一侧用
`Connected.card_vert_le_card_edgeSet_add_one` 得下界
`Nat.card (V ⊕ Fin 2) ≤ Nat.card ↑(graftGraph G t).edgeSet + 1`，
另一侧用 ★★ `Phylo.card_edgeSet_graftGraph_le` 加上 `G.IsTree` 的
`Nat.card ↑G.edgeSet + 1 = Nat.card V` 得上界
`Nat.card ↑(graftGraph G t).edgeSet + 1 ≤ Nat.card (V ⊕ Fin 2)`，
两侧夹逼即得树所要求的**精确计数** `|E| + 1 = |V|`。

## ⬜ 诚实边界（本文件**不**声称的）

* **⬜ `Phylo.graftCladogram`** / **⬜ `Phylo.graftPhylogram`**（`no_degree_two` /
  `leaf_iff_degree_one`）、**⬜ `Phylo.graftPhylogram_dist_leaf`**（`dist` 记账：
  旧点到旧点不变，`p`、`q` 到旧点用 `Dissimilarity.attach_left` / `attach_right`
  分解为 `ρ + T'.dist (T'.leaf t) ·`）—— 均**尚未**落地（本文件目前只有图、邻接接口与
  ★★★ `Phylo.graftGraph_isTree`；无 `sorry`、无 `axiom`）。

* **⬜ `Dissimilarity.InductiveAssembly` 与 `Phylo/Buneman.lean` 的缺口 —— 精确边界**：

  Buneman 第 116–121 行的收缩把**新点 `t`** 加进较小集合 `S' = S ∖ {p,q} ∪ {t}`，
  于是 `t` 是较小问题的**标签**，在 `Cladogram`（`leaf_iff_degree_one` + `no_degree_two`）
  下 `t` 必是较小树 `T'` 的**叶**（度 1）。**计数核对**：`T'` 有 `|V'|` 个顶点、
  `|E'| = |V'| − 1` 条边；`graftGraph` 加 2 个顶点、2 条边，得
  `|E(graftGraph)| = |V'| + 1 = |V(graftGraph)| − 1` —— **恰是树所要求的计数**
  （已由 ★★★ `Phylo.graftGraph_isTree` 严格证实），
  且新叶度 1、`t` 由 1 变 3、其余旧点度数不变：故**本文件选定的「挂到 `t` 本身」是正确手术**
  （挂到别的旧点上会让 `t` 变孤立点或度 2，反而破坏 `IsTree` / `no_degree_two`）。

  真正未闭合的是 `InductiveAssembly` 对**小基数**的要求：`t` 由 (2a)/(2b) 只在
  `S ∖ {p,q}` 上被**距离数据**确定，而 `Cladogram` 的顶点集必须**恰好**承载
  `leaf_iff_degree_one`（每个度 1 顶点都是标签）。当 `|S| = 3` 时 `S' = {t, r}`
  只有 2 个标签，`T'` 是单单一条边、`t` 是它的叶；挂上 `p`、`q` 后 `t` 度 3，
  得到的是**三点星形** `K_{1,3}`（`p, q, r` 三个标签共用一个非标签中心 `t`）——
  它不是任何 `Phylogram X` 的「叶恰为 `X`」形式。这正是 Buneman 第 74 行
  「For any metric on a set of order three it is easy to construct the appropriate tree」
  必须**单独**处理的基例，故 `InductiveAssembly` 的完整证明需要
  `|Y| = 3`（三点星形）与 `|Y| = 4`（四点星形）两个基例 + 本文件的挂叶手术。
-/

noncomputable section

open SimpleGraph

universe u

namespace Phylo

variable {V : Type*}

/-- ★★★ **挂叶图**（Buneman 第 119–121 行的图手术）：在 `G` 上把两片新叶
`Sum.inr 0`、`Sum.inr 1` 接到旧顶点 `Sum.inl t` 上，旧顶点之间的邻接与 `G` 完全一致。 -/
def graftGraph (G : SimpleGraph V) (t : V) : SimpleGraph (V ⊕ Fin 2) where
  Adj a b :=
    (∃ x y : V, G.Adj x y ∧ a = Sum.inl x ∧ b = Sum.inl y) ∨
    (a = Sum.inl t ∧ (b = Sum.inr 0 ∨ b = Sum.inr 1)) ∨
    (b = Sum.inl t ∧ (a = Sum.inr 0 ∨ a = Sum.inr 1))
  symm := Std.Symm.mk fun a b h => by
    rcases h with ⟨x, y, hxy, rfl, rfl⟩ | ⟨rfl, h | h⟩ | ⟨rfl, h | h⟩
    · exact Or.inl ⟨y, x, hxy.symm, rfl, rfl⟩
    · exact Or.inr (Or.inr ⟨rfl, Or.inl h⟩)
    · exact Or.inr (Or.inr ⟨rfl, Or.inr h⟩)
    · exact Or.inr (Or.inl ⟨rfl, Or.inl h⟩)
    · exact Or.inr (Or.inl ⟨rfl, Or.inr h⟩)
  loopless := Std.Irrefl.mk fun a h => by
    rcases h with ⟨x, y, hxy, ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
    · rw [ha] at hb
      exact hxy.ne (Sum.inl.inj hb)
    · subst ha
      rcases hb with h | h
      · exact nomatch h
      · exact nomatch h
    · subst ha
      rcases hb with h | h
      · exact nomatch h
      · exact nomatch h

/-- ★★★ 旧顶点之间的邻接与原图一致（挂叶不动旧边）。 -/
@[simp] theorem graftGraph_adj_inl_inl {G : SimpleGraph V} {t x y : V} :
    (graftGraph G t).Adj (Sum.inl x) (Sum.inl y) ↔ G.Adj x y := by
  constructor
  · intro h
    rcases h with ⟨x', y', hxy, h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact (Sum.inl.inj h1) ▸ (Sum.inl.inj h2) ▸ hxy
    · rcases h2 with h | h <;> exact nomatch h
    · rcases h2 with h | h <;> exact nomatch h
  · intro h
    exact Or.inl ⟨x, y, h, rfl, rfl⟩

/-- ★★★ **挂边**：`Sum.inl x` 与第 `i` 片新叶相邻 ⟺ `x = t`。 -/
@[simp] theorem graftGraph_adj_inl_inr {G : SimpleGraph V} {t x : V} {i : Fin 2} :
    (graftGraph G t).Adj (Sum.inl x) (Sum.inr i) ↔ x = t := by
  constructor
  · intro h
    rcases h with ⟨x', y', _, h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · simp_all
    · exact Sum.inl.inj h1
    · simp_all
  · intro h
    subst h
    fin_cases i
    · exact Or.inr (Or.inl ⟨rfl, Or.inl rfl⟩)
    · exact Or.inr (Or.inl ⟨rfl, Or.inr rfl⟩)

/-- ★★★ 挂边的对称形式。 -/
@[simp] theorem graftGraph_adj_inr_inl {G : SimpleGraph V} {t y : V} {i : Fin 2} :
    (graftGraph G t).Adj (Sum.inr i) (Sum.inl y) ↔ y = t := by
  rw [SimpleGraph.adj_comm]
  exact graftGraph_adj_inl_inr

/-- ★★ 两片新叶之间**没有**边（这正是「度 1」的来源）。 -/
theorem graftGraph_adj_not_inr_inr {G : SimpleGraph V} {t : V} {i j : Fin 2} :
    ¬(graftGraph G t).Adj (Sum.inr i) (Sum.inr j) := by
  intro h
  rcases h with ⟨x', y', _, h1, _⟩ | ⟨h1, _⟩ | ⟨h1, _⟩
  · simp_all
  · simp_all
  · simp_all

/-! ### 边集分解与计数（`graftGraph_isTree` 的地基） -/

/-- ★★ **旧边的像**：把 `G.edgeSet` 沿 `Sum.inl` 搬进 `V ⊕ Fin 2`
（`Sym2.map (Sum.inl : V → V ⊕ Fin 2)`）。 -/
def graftOldEdges (G : SimpleGraph V) : Set (Sym2 (V ⊕ Fin 2)) :=
  Sym2.map (Sum.inl : V → V ⊕ Fin 2) '' (G.edgeSet : Set (Sym2 V))

/-- ★★ **两条新挂边** `{inl t, inr 0}`、`{inl t, inr 1}`（Buneman 第 119–121 行）。 -/
def graftNewEdges (t : V) : Set (Sym2 (V ⊕ Fin 2)) :=
  {s(Sum.inl t, Sum.inr 0), s(Sum.inl t, Sum.inr 1)}

/-- ★★ 把 `G` 嵌入 `graftGraph G t` 的**图同态**（旧顶点 `x ↦ Sum.inl x`）。 -/
def graftGraphHom (G : SimpleGraph V) (t : V) : G →g graftGraph G t :=
  ⟨fun v => Sum.inl v, fun {_ _} h => (graftGraph_adj_inl_inl).mpr h⟩

/-- ★★★ **挂叶保持连通**（`G.Connected → (graftGraph G t).Connected`）。

每个新叶 `Sum.inr i` 与 `Sum.inl t` 相邻（`graftGraph_adj_inr_inl`），而每个旧点
`Sum.inl x` 沿 ★★ `Phylo.graftGraphHom` 从 `G` 的连通性到达 `Sum.inl t`。 -/
theorem graftGraph_connected {G : SimpleGraph V} (hG : G.Connected) (t : V) :
    (graftGraph G t).Connected where
  preconnected := by
    intro a b
    have key : ∀ c : V ⊕ Fin 2, (graftGraph G t).Reachable c (Sum.inl t) := by
      rintro (x | i)
      · exact Reachable.map (graftGraphHom G t) (hG.preconnected x t)
      · exact Adj.reachable ((graftGraph_adj_inr_inl).mpr rfl)
    exact (key a).trans (key b).symm
  nonempty := ⟨Sum.inl t⟩

/-- ★★★ **边集分解**：`graftGraph G t` 的每条边或是**旧边**、或是两条**新挂边**之一。
（不含 `Sym2.map` 的任何单射性：只是逐点验证三种邻接情形。） -/
theorem graftGraph_edgeSet_subset (G : SimpleGraph V) (t : V) :
    (graftGraph G t).edgeSet ⊆ graftOldEdges G ∪ graftNewEdges t := by
  intro e he
  revert he
  refine Sym2.inductionOn e ?_
  intro a b he
  simp only [SimpleGraph.mem_edgeSet] at he
  rcases a with x | i <;> rcases b with y | j
  · exact Or.inl ⟨s(x, y), (SimpleGraph.mem_edgeSet G).mpr ((graftGraph_adj_inl_inl).mp he), rfl⟩
  · obtain rfl : x = t := (graftGraph_adj_inl_inr).mp he
    fin_cases j
    · exact Or.inr (by simp [graftNewEdges])
    · exact Or.inr (by simp [graftNewEdges])
  · obtain rfl : y = t := (graftGraph_adj_inr_inl).mp he
    rw [Sym2.eq_swap]
    fin_cases i
    · exact Or.inr (by simp [graftNewEdges])
    · exact Or.inr (by simp [graftNewEdges])
  · exact absurd he graftGraph_adj_not_inr_inr

/-- ★★ **旧边不重复**：`Sym2.map Sum.inl` 全局单射（`Sym2.map.injective`），
故在 `G.edgeSet` 上单射，旧边的像与 `G.edgeSet` 等势。 -/
theorem ncard_graftOldEdges (G : SimpleGraph V) :
    (graftOldEdges G).ncard = (G.edgeSet : Set (Sym2 V)).ncard :=
  Set.ncard_image_of_injective _ (Sym2.map.injective Sum.inl_injective)

/-- ★★ **恰有 2 条新挂边**（两条不同的无序对）。 -/
theorem ncard_graftNewEdges (t : V) : (graftNewEdges t).ncard = 2 := by
  rw [graftNewEdges, Set.ncard_pair]
  intro h
  exact Fin.zero_ne_one (Sum.inr.inj (Sym2.congr_right.mp h))

/-- ★★ `Set.ncard` 与 `Nat.card` 的桥（`H.edgeSet` 作为子类型）。 -/
theorem ncard_edgeSet_eq_natCard (H : SimpleGraph V) [Fintype V] :
    (H.edgeSet : Set (Sym2 V)).ncard = Nat.card ↑H.edgeSet := by
  classical
  rw [Set.ncard_eq_toFinset_card', Set.toFinset_card, Nat.card_eq_fintype_card]

/-- ★★ **边数上界**：挂叶最多加两条边，
`Nat.card ↑(graftGraph G t).edgeSet ≤ Nat.card ↑G.edgeSet + 2`。 -/
theorem card_edgeSet_graftGraph_le [Fintype V] (G : SimpleGraph V) (t : V) :
    Nat.card ↑(graftGraph G t).edgeSet ≤ Nat.card ↑G.edgeSet + 2 := by
  classical
  calc Nat.card ↑(graftGraph G t).edgeSet
      = ((graftGraph G t).edgeSet : Set (Sym2 (V ⊕ Fin 2))).ncard :=
        (ncard_edgeSet_eq_natCard _).symm
    _ ≤ (graftOldEdges G ∪ graftNewEdges t).ncard :=
        Set.ncard_le_ncard (graftGraph_edgeSet_subset G t)
    _ ≤ (graftOldEdges G).ncard + (graftNewEdges t).ncard := Set.ncard_union_le _ _
    _ = (G.edgeSet : Set (Sym2 V)).ncard + 2 := by
        rw [ncard_graftOldEdges, ncard_graftNewEdges]
    _ = Nat.card ↑G.edgeSet + 2 := by rw [ncard_edgeSet_eq_natCard]

/-- ★★★ **挂叶保持树性**（Buneman 第 119–121 行的图手术正确性）：
若 `G` 是树，则把两片新叶挂到**任意**顶点 `t` 上仍是树。

**注**：这里**不**需要 `t` 是叶 —— `IsTree` 只需「连通 + `|E| + 1 = |V|`」；
`t` 是叶这一假设只在 ★★★ `Phylo.graftGraph_isTree` 的下游用途
（`t` 的度由 1 变 3、故 `Cladogram.no_degree_two` 保持）中出现。

证法（计数路线，避免环路/桥的图论论证）：`SimpleGraph.isTree_iff_connected_and_card`。
* 连通：★★★ `Phylo.graftGraph_connected`；
* 下界：`Connected.card_vert_le_card_edgeSet_add_one`；
* 上界：★★ `Phylo.card_edgeSet_graftGraph_le` 加 `G.IsTree` 的精确计数；
* 两侧夹逼得 `Nat.card ↑(graftGraph G t).edgeSet + 1 = Nat.card (V ⊕ Fin 2)`。 -/
theorem graftGraph_isTree [Fintype V] {G : SimpleGraph V} (t : V) (hG : G.IsTree) :
    (graftGraph G t).IsTree := by
  classical
  have hconn := graftGraph_connected hG.connected t
  refine SimpleGraph.isTree_iff_connected_and_card.mpr ⟨hconn, ?_⟩
  have hGcard : Nat.card ↑G.edgeSet + 1 = Nat.card V :=
    (SimpleGraph.isTree_iff_connected_and_card.mp hG).2
  have hV2 : Nat.card (V ⊕ Fin 2) = Nat.card V + 2 := by
    rw [Nat.card_sum]
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin]
  have hlow : Nat.card (V ⊕ Fin 2) ≤ Nat.card ↑(graftGraph G t).edgeSet + 1 :=
    SimpleGraph.Connected.card_vert_le_card_edgeSet_add_one hconn
  have hup : Nat.card ↑(graftGraph G t).edgeSet + 1 ≤ Nat.card (V ⊕ Fin 2) := by
    have h1 := card_edgeSet_graftGraph_le G t
    omega
  omega

end Phylo
