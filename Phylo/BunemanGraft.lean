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

**图与邻接层**

* **★★★ `Phylo.graftGraph`** —— 挂叶手术的**图**（`SimpleGraph (V ⊕ Fin 2)`）。
* **★★★ `Phylo.graftGraph_adj_inl_inl`** —— 旧顶点之间的邻接**与原图一致**（挂叶不动旧边）。
* **★★★ `Phylo.graftGraph_adj_inl_inr`** / **★★★ `Phylo.graftGraph_adj_inr_inl`** ——
  两条挂边：`Sum.inl x` 与第 `i` 片新叶相邻 **⟺** `x = t`。
* **★★★ `Phylo.graftGraph_adj_not_inr_inr`** —— 两片新叶之间**无边**。
* **★★ `Phylo.graftGraphHom`** —— 把 `G` 嵌入 `graftGraph G t` 的图同态（`x ↦ Sum.inl x`）。

**树性（TASK 1，Buneman 第 119–121 行手术的正确性）**

* **★★★ `Phylo.graftGraph_isTree`** —— **挂叶保持树性**：`G.IsTree → (graftGraph G t).IsTree`，
  对**任意**顶点 `t`，**不要求 `t` 是叶**。
* **★★★ `Phylo.graftGraph_connected`** —— 挂叶保持连通。
* **★★★ `Phylo.graftGraph_edgeSet_subset`** —— 边集分解：
  `(graftGraph G t).edgeSet ⊆ graftOldEdges G ∪ graftNewEdges t`。
* **★★ `Phylo.graftOldEdges`** / **★★ `Phylo.graftNewEdges`** —— 旧边的像、两条新挂边。
* **★★ `Phylo.ncard_graftOldEdges`** / **★★ `Phylo.ncard_graftNewEdges`** ——
  `Sym2.map Sum.inl` 单射（`Sym2.map.injective`）故旧边不重复；新挂边恰 **2** 条。
* **★★ `Phylo.ncard_edgeSet_eq_natCard`** —— `Set.ncard` 与 `Nat.card` 的桥。
* **★★ `Phylo.card_edgeSet_graftGraph_le`** —— 边数上界
  `Nat.card ↑(graftGraph G t).edgeSet ≤ Nat.card ↑G.edgeSet + 2`。

**度数层（TASK 2 的地基）**

* **★★ `Phylo.graftGraph_neighborSet_inr`** / **`_inl_ne`** / **`_inl_self`** —— 邻域集的三条等式。
* **★★ `Phylo.graftGraph_ncard_neighborSet_inr`** / **`_inl_ne`** / **`_inl_self`** ——
  对应的 `Set.ncard` 形式（**不含任何实例参数**，可跨实例复用）。
* **★★★ `Phylo.graftGraph_degree_inr`**（新叶度 1）、
  **★★★ `Phylo.graftGraph_degree_inl_ne`**（旧点度不变）、
  **★★★ `Phylo.graftGraph_degree_inl_self`**（中心 `t` 的度 `+2`，叶情形即 `1 → 3`）。

**`Cladogram` / `Phylogram` 层（TASK 2）**

* **★★★ `Phylo.graftLeafFun`** —— 标签映射：`p ↦ Sum.inr 0`、`q ↦ Sum.inr 1`、
  其余 `y ↦ Sum.inl (T'.leaf (Sum.inl ⟨y,·,·⟩))`。
* **★★ `Phylo.graftLeafFun_eq_inr_zero`** / **`_eq_inr_one`** / **`_eq_inl`** 及其
  **`_iff`** 形式 —— 三种取值的刻画（单射性的全部内容）。
* **★★★ `Phylo.graftLeaf`** —— 标签**嵌入** `Y ↪ T'.V ⊕ Fin 2`。
* **★★★ `Phylo.graftCladogram`** —— **挂叶的 cladogram**：
  `V := T'.V ⊕ Fin 2`、`graph := graftGraph T'.graph (T'.leaf (Sum.inr ()))`，
  并证 `IsTree`、`leaf_iff_degree_one`、`no_degree_two`。
* **★★ `Phylo.graftOldEdge_exists`** / **★★ `Phylo.graftOldEdge`** ——
  非挂边的旧边来源（用 ★★★ `Phylo.graftGraph_edgeSet_subset` + `Classical.choose`）。
* **★★★ `Phylo.graftPhylogram`** —— **挂叶的 phylogram**：旧边沿用 `T'.w`，
  两条新挂边取 `δ.rho p q r`、`δ.rho q p r`（第 94、119–121 行），非负性用
  `Dissimilarity.rho_nonneg`。

**`graftGraph_isTree` 的证法（已落地的路线）**：不直接做「环 → 桥」的图论论证，而是
`SimpleGraph.isTree_iff_connected_and_card`：
连通性由 ★★★ `Phylo.graftGraph_connected` 给出；计数一侧用
`Connected.card_vert_le_card_edgeSet_add_one` 得下界
`Nat.card (V ⊕ Fin 2) ≤ Nat.card ↑(graftGraph G t).edgeSet + 1`，
另一侧用 ★★ `Phylo.card_edgeSet_graftGraph_le` 加上 `G.IsTree` 的
`Nat.card ↑G.edgeSet + 1 = Nat.card V` 得上界
`Nat.card ↑(graftGraph G t).edgeSet + 1 ≤ Nat.card (V ⊕ Fin 2)`，
两侧夹逼即得树所要求的**精确计数** `|E| + 1 = |V|`。

**实现注记**：本文件在 `namespace Phylo` 内注册
`attribute [local instance] Classical.propDecidable`，使 `SimpleGraph.degree` 出现在
**定理陈述**里时也能通过类型类搜索（`Cladogram` 的 `decAdj`/`fintypeV` 是结构字段，
在结构字面量中不自动作为实例）。凡需要跨实例复用的度数引理都另外给出
`Set.ncard` 形式（`graftGraph_ncard_neighborSet_*`），`graftCladogram` 的证明只经由
`Set.ncard`，从而绕开 `Set.toFinset` 的 `Fintype` 实例不 defeq 的问题
（同 `Phylo/InternalEdge.lean` 的 `degree_induce_eq_card_inter` 的教训）。

## ⬜ 诚实边界（本文件**不**声称的）

* **⬜ `Phylo.graftPhylogram_dist`**（`dist` 记账：旧点到旧点不变；`p`、`q` 到旧点用
  `Dissimilarity.attach_left` / `attach_right` 分解为
  `ρ(p;q,r) + T'.dist (T'.leaf t) (T'.leaf x)`；`p`—`q` 距离为 `ρ + ρ`）——
  **尚未**落地。★ `Phylo.graftPhylogram` 只给出**权重与拓扑**，
  `Phylogram.dist`（沿唯一路径的边权和）的**计算**仍缺（本文件无 `sorry`、无 `axiom`）。

* **⬜ `Dissimilarity.InductiveAssembly` 与 `Phylo/Buneman.lean` 的缺口 —— 精确边界**：

  Buneman 第 116–121 行的收缩把**新点 `t`** 加进较小集合 `S' = S ∖ {p,q} ∪ {t}`，
  于是 `t` 是较小问题的**标签**，在 `Cladogram`（`leaf_iff_degree_one` + `no_degree_two`）
  下 `t` 必是较小树 `T'` 的**叶**（度 1）。**计数核对**：`T'` 有 `|V'|` 个顶点、
  `|E'| = |V'| − 1` 条边；`graftGraph` 加 2 个顶点、2 条边，得
  `|E(graftGraph)| = |V'| + 1 = |V(graftGraph)| − 1` —— **恰是树所要求的计数**
  （已由 ★★★ `Phylo.graftGraph_isTree` 严格证实），
  且新叶度 1、`t` 由 1 变 3（★★★ `Phylo.graftGraph_degree_inl_self`）、
  其余旧点度数不变（★★★ `Phylo.graftGraph_degree_inl_ne`）：故**本文件选定的
  「挂到 `t` 本身」是正确手术**（挂到别的旧点上会让 `t` 变孤立点或度 2，
  反而破坏 `IsTree` / `no_degree_two`）。这些度数记账现已由
  ★★★ `Phylo.graftCladogram` 的 `no_degree_two` / `leaf_iff_degree_one` 字段严格落地。

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

attribute [local instance] Classical.propDecidable

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
（不依赖 `Sym2.map` 的单射性：只是逐点验证三种邻接情形。） -/
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
`t` 是叶这一假设只在 ★★★ `Phylo.graftCladogram` 的 `no_degree_two`
（`t` 的度由 1 变 3）中用到。

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

/-! ### 度数层（TASK 2 的地基）

新叶度 1、中心 `t` 的度 `+2`、其余旧点度不变 —— 这三条就是
`Cladogram.no_degree_two` 与 `Cladogram.leaf_iff_degree_one` 的全部内容。

`Set.ncard` 形式（★ `Phylo.graftGraph_ncard_neighborSet_*`）**不含实例参数**，
是 `graftCladogram` 实际使用的版本；`degree` 形式便于使用者陈述。 -/

/-- ★★ 新叶的**邻域集是单点集** `{Sum.inl t}`。 -/
theorem graftGraph_neighborSet_inr (G : SimpleGraph V) (t : V) (i : Fin 2) :
    (graftGraph G t).neighborSet (Sum.inr i) = {Sum.inl t} := by
  ext w
  rcases w with y | j
  · rw [SimpleGraph.mem_neighborSet, Set.mem_singleton_iff, graftGraph_adj_inr_inl, Sum.inl.injEq]
  · rw [SimpleGraph.mem_neighborSet, Set.mem_singleton_iff]
    exact ⟨fun h => absurd h graftGraph_adj_not_inr_inr, fun h => by simp at h⟩

/-- ★★ 旧点（**非中心**）的邻域集是原图邻域集的 `Sum.inl` 像。 -/
theorem graftGraph_neighborSet_inl_ne (G : SimpleGraph V) {t v : V} (h : v ≠ t) :
    (graftGraph G t).neighborSet (Sum.inl v) = Sum.inl '' (G.neighborSet v) := by
  ext w
  rcases w with y | i
  · rw [SimpleGraph.mem_neighborSet, Set.mem_image, graftGraph_adj_inl_inl]
    constructor
    · intro hy; exact ⟨y, hy, rfl⟩
    · rintro ⟨y', hy', he⟩
      rw [Sum.inl.injEq] at he
      exact he ▸ hy'
  · rw [SimpleGraph.mem_neighborSet, Set.mem_image, graftGraph_adj_inl_inr]
    constructor
    · intro hv; exact absurd hv h
    · rintro ⟨y', _, he⟩; exact absurd he (by simp)

/-- ★★ **中心** `t` 的邻域集 = 原邻域集的像 **并** 两片新叶。 -/
theorem graftGraph_neighborSet_inl_self (G : SimpleGraph V) (t : V) :
    (graftGraph G t).neighborSet (Sum.inl t) =
      Sum.inl '' (G.neighborSet t) ∪ {Sum.inr 0, Sum.inr 1} := by
  ext w
  rcases w with y | i
  · rw [SimpleGraph.mem_neighborSet, Set.mem_union, Set.mem_image, Set.mem_insert_iff,
      Set.mem_singleton_iff, graftGraph_adj_inl_inl]
    constructor
    · intro hy; exact Or.inl ⟨y, hy, rfl⟩
    · rintro (⟨y', hy', he⟩ | ⟨he | he⟩)
      · rw [Sum.inl.injEq] at he
        exact he ▸ hy'
      · exact absurd he (by simp)
      · exact absurd he (by simp)
  · fin_cases i <;>
      rw [SimpleGraph.mem_neighborSet, Set.mem_union, Set.mem_image, Set.mem_insert_iff,
        Set.mem_singleton_iff, graftGraph_adj_inl_inr]
    · exact ⟨fun _ => Or.inr (Or.inl rfl), fun _ => rfl⟩
    · exact ⟨fun _ => Or.inr (Or.inr rfl), fun _ => rfl⟩

/-- ★★ 新叶邻域集的基数（`Set.ncard` 形式，无实例参数）。 -/
theorem graftGraph_ncard_neighborSet_inr (G : SimpleGraph V) (t : V) (i : Fin 2) :
    ((graftGraph G t).neighborSet (Sum.inr i)).ncard = 1 := by
  rw [graftGraph_neighborSet_inr, Set.ncard_singleton]

/-- ★★ 非中心旧点邻域集的基数（`Set.ncard` 形式）。 -/
theorem graftGraph_ncard_neighborSet_inl_ne (G : SimpleGraph V) {t v : V} (h : v ≠ t) :
    ((graftGraph G t).neighborSet (Sum.inl v)).ncard = (G.neighborSet v).ncard := by
  rw [graftGraph_neighborSet_inl_ne G h]
  exact Set.ncard_image_of_injective _ Sum.inl_injective

/-- ★★ 中心邻域集的基数 = 原基数 `+ 2`（`Set.ncard` 形式）。 -/
theorem graftGraph_ncard_neighborSet_inl_self [Finite V] (G : SimpleGraph V) (t : V) :
    ((graftGraph G t).neighborSet (Sum.inl t)).ncard = (G.neighborSet t).ncard + 2 := by
  have hdisj : Disjoint (Sum.inl '' (G.neighborSet t))
      ({Sum.inr 0, Sum.inr 1} : Set (V ⊕ Fin 2)) := by
    rw [Set.disjoint_left]
    rintro e ⟨y, -, rfl⟩ (h | h) <;> exact absurd h (by simp)
  rw [graftGraph_neighborSet_inl_self, Set.ncard_union_eq hdisj, Set.ncard_pair (by simp),
    Set.ncard_image_of_injective _ Sum.inl_injective]

/-- ★★★ 新叶的度是 **1**（两片新叶都是叶）。 -/
theorem graftGraph_degree_inr [Fintype V] (G : SimpleGraph V) (t : V) (i : Fin 2) :
    (graftGraph G t).degree (Sum.inr i) = 1 := by
  rw [← SimpleGraph.ncard_neighborSet, graftGraph_ncard_neighborSet_inr]

/-- ★★★ **旧点度不变**（`v ≠ t`；这正是 `no_degree_two` 的保持）。 -/
theorem graftGraph_degree_inl_ne [Fintype V] (G : SimpleGraph V) {t v : V} (h : v ≠ t) :
    (graftGraph G t).degree (Sum.inl v) = G.degree v := by
  rw [← SimpleGraph.ncard_neighborSet, ← SimpleGraph.ncard_neighborSet,
    graftGraph_ncard_neighborSet_inl_ne G h]

/-- ★★★ **中心的度 `+2`**：`t` 若是 `G` 的叶（度 1），挂叶后度为 **3**
（Buneman 第 119–121 行「`t` 变成内部顶点」的精确内容）。 -/
theorem graftGraph_degree_inl_self [Fintype V] (G : SimpleGraph V) (t : V) :
    (graftGraph G t).degree (Sum.inl t) = G.degree t + 2 := by
  rw [← SimpleGraph.ncard_neighborSet, ← SimpleGraph.ncard_neighborSet,
    graftGraph_ncard_neighborSet_inl_self G t]

/-! ### 标签嵌入与 `Cladogram` / `Phylogram` 打包（TASK 2）

归纳步的较小问题定义在 `BunemanShrink p q = {x // x ≠ p ∧ x ≠ q} ⊕ Unit` 上，
新点 `t := Sum.inr ()` 是**标签**，故是较小树 `T'` 的**叶**。
`V := T'.V ⊕ Fin 2`：`Sum.inl v` 是 `T'` 的旧顶点，`Sum.inr 0`／`Sum.inr 1` 是 `p`／`q`。 -/

section Fresh

open NJ.Dissimilarity

variable {Y : Type u} [DecidableEq Y] {p q : Y}

/-- ★★★ **标签映射**：`p ↦ Sum.inr 0`、`q ↦ Sum.inr 1`，
其余 `y ↦ Sum.inl (T'.leaf (Sum.inl ⟨y, ·, ·⟩))`。 -/
noncomputable def graftLeafFun (T' : Cladogram (BunemanShrink p q)) (y : Y) : T'.V ⊕ Fin 2 :=
  if hy : y = p then Sum.inr 0
  else if hq : y = q then Sum.inr 1
  else Sum.inl (T'.leaf (Sum.inl ⟨y, hy, hq⟩))

/-- ★★ `graftLeafFun` 在 `y = p` 处取 `Sum.inr 0`。 -/
theorem graftLeafFun_eq_inr_zero (T' : Cladogram (BunemanShrink p q)) {y : Y} (hy : y = p) :
    graftLeafFun T' y = Sum.inr 0 := by
  rw [graftLeafFun, dite_eq_left hy]

/-- ★★ `graftLeafFun` 在 `y = q`（且 `y ≠ p`）处取 `Sum.inr 1`。 -/
theorem graftLeafFun_eq_inr_one (T' : Cladogram (BunemanShrink p q)) {y : Y}
    (hy : y ≠ p) (hq : y = q) : graftLeafFun T' y = Sum.inr 1 := by
  rw [graftLeafFun, dite_eq_right hy, dite_eq_left hq]

/-- ★★ 其余情形 `graftLeafFun y = Sum.inl (T'.leaf …)`。 -/
theorem graftLeafFun_eq_inl (T' : Cladogram (BunemanShrink p q)) {y : Y}
    (hy : y ≠ p) (hq : y ≠ q) :
    graftLeafFun T' y = Sum.inl (T'.leaf (Sum.inl ⟨y, hy, hq⟩)) := by
  rw [graftLeafFun, dite_eq_right hy, dite_eq_right hq]

/-- ★★ 取 `Sum.inr 0` ⟺ `y = p`。 -/
theorem graftLeafFun_eq_inr_zero_iff (T' : Cladogram (BunemanShrink p q)) (y : Y) :
    graftLeafFun T' y = Sum.inr 0 ↔ y = p := by
  by_cases hy : y = p
  · exact iff_of_true (graftLeafFun_eq_inr_zero T' hy) hy
  · by_cases hq : y = q
    · exact iff_of_false (by rw [graftLeafFun_eq_inr_one T' hy hq]; simp) hy
    · exact iff_of_false (by rw [graftLeafFun_eq_inl T' hy hq]; simp) hy

/-- ★★ 取 `Sum.inr 1` ⟺ `y = q`（需 `p ≠ q`）。 -/
theorem graftLeafFun_eq_inr_one_iff (hpq : p ≠ q) (T' : Cladogram (BunemanShrink p q))
    (y : Y) : graftLeafFun T' y = Sum.inr 1 ↔ y = q := by
  by_cases hy : y = p
  · refine iff_of_false (by rw [graftLeafFun_eq_inr_zero T' hy]; simp) ?_
    intro hq
    exact hpq (hy.symm.trans hq)
  · by_cases hq : y = q
    · exact iff_of_true (graftLeafFun_eq_inr_one T' hy hq) hq
    · exact iff_of_false (by rw [graftLeafFun_eq_inl T' hy hq]; simp) hq

/-- ★★ `graftLeafFun y = Sum.inl v` ⟺ `v` 是 `y` 对应的旧叶。 -/
theorem graftLeafFun_eq_inl_iff (T' : Cladogram (BunemanShrink p q)) {y : Y}
    (hy : y ≠ p) (hq : y ≠ q) {v : T'.V} :
    graftLeafFun T' y = Sum.inl v ↔ T'.leaf (Sum.inl ⟨y, hy, hq⟩) = v := by
  rw [graftLeafFun_eq_inl T' hy hq, Sum.inl.injEq]

/-- ★★★ **标签嵌入** `Y ↪ T'.V ⊕ Fin 2`（三个 `_iff` 引理给出单射性的全部内容）。 -/
noncomputable def graftLeaf (hpq : p ≠ q) (T' : Cladogram (BunemanShrink p q)) :
    Y ↪ (T'.V ⊕ Fin 2) where
  toFun := graftLeafFun T'
  inj' := by
    intro y z h
    by_cases hyp : y = p
    · have hz0 : graftLeafFun T' z = Sum.inr 0 := by
        rw [← h]; exact graftLeafFun_eq_inr_zero T' hyp
      have hz : z = p := (graftLeafFun_eq_inr_zero_iff T' z).mp hz0
      rw [hyp, hz]
    · by_cases hyq : y = q
      · have hz1 : graftLeafFun T' z = Sum.inr 1 := by
          rw [← h]; exact graftLeafFun_eq_inr_one T' hyp hyq
        have hz : z = q := (graftLeafFun_eq_inr_one_iff hpq T' z).mp hz1
        rw [hyq, hz]
      · have hyi : graftLeafFun T' y = Sum.inl (T'.leaf (Sum.inl ⟨y, hyp, hyq⟩)) :=
          graftLeafFun_eq_inl T' hyp hyq
        have hzi : graftLeafFun T' z = Sum.inl (T'.leaf (Sum.inl ⟨y, hyp, hyq⟩)) := by
          rw [← h]; exact hyi
        by_cases hzp : z = p
        · exact absurd ((graftLeafFun_eq_inr_zero T' hzp).symm.trans hzi) (by simp)
        · by_cases hzq : z = q
          · exact absurd ((graftLeafFun_eq_inr_one T' hzp hzq).symm.trans hzi) (by simp)
          · have hzj : T'.leaf (Sum.inl ⟨z, hzp, hzq⟩) = T'.leaf (Sum.inl ⟨y, hyp, hyq⟩) := by
              rw [graftLeafFun_eq_inl T' hzp hzq] at hzi
              exact Sum.inl.inj hzi
            exact (Subtype.ext_iff.mp (Sum.inl.inj (T'.leaf.injective hzj))).symm

end Fresh

section Clad

open NJ.Dissimilarity

variable {Y : Type u} [Fintype Y] [DecidableEq Y] {p q : Y}

/-- ★★★ **挂叶的 cladogram**：把 `p`、`q`（及其标签）作为两片新叶挂到 `T'` 的叶 `t`
（`t := T'.leaf (Sum.inr ())`）上。

* `V := T'.V ⊕ Fin 2`；
* `graph := graftGraph T'.graph t`（★★★ `Phylo.graftGraph_isTree` 给出 `IsTree`）；
* `leaf := graftLeaf hpq T'`（★★★）；
* `no_degree_two` / `leaf_iff_degree_one` 由 ★★★ `Phylo.graftGraph_degree_inr`、
  ★★★ `Phylo.graftGraph_degree_inl_ne`、★★★ `Phylo.graftGraph_degree_inl_self`
  配合 `Set.ncard` 版本夹出（旧点度不变、中心 `1 → 3`、新叶度 1）。 -/
noncomputable def graftCladogram (hpq : p ≠ q) (T' : Cladogram (BunemanShrink p q)) :
    Cladogram Y := by
  classical
  letI : Fintype (T'.V ⊕ Fin 2) := inferInstance
  letI : DecidableEq (T'.V ⊕ Fin 2) := inferInstance
  letI : DecidableRel (graftGraph T'.graph (T'.leaf (Sum.inr ()))).Adj :=
    fun a b => Classical.propDecidable _
  have hcenter : (T'.graph.neighborSet (T'.leaf (Sum.inr ()))).ncard = 1 := by
    have h : T'.graph.degree (T'.leaf (Sum.inr ())) = 1 :=
      (T'.leaf_iff_degree_one (T'.leaf (Sum.inr ()))).mp ⟨Sum.inr (), rfl⟩
    rwa [← SimpleGraph.ncard_neighborSet] at h
  exact
    { V := T'.V ⊕ Fin 2
      fintypeV := inferInstance
      decEqV := inferInstance
      graph := graftGraph T'.graph (T'.leaf (Sum.inr ()))
      decAdj := inferInstance
      isTree := graftGraph_isTree (T'.leaf (Sum.inr ())) T'.isTree
      leaf := graftLeaf hpq T'
      leaf_iff_degree_one := by
        intro x
        rw [← SimpleGraph.ncard_neighborSet]
        rcases x with v | i
        · by_cases hv : v = T'.leaf (Sum.inr ())
          · rw [hv, graftGraph_ncard_neighborSet_inl_self]
            refine iff_of_false ?_ (by omega)
            rintro ⟨y, hy⟩
            have hyp : y ≠ p := fun h =>
              absurd ((graftLeafFun_eq_inr_zero T' h).symm.trans hy) (by simp)
            have hyq : y ≠ q := fun h =>
              absurd ((graftLeafFun_eq_inr_one T' hyp h).symm.trans hy) (by simp)
            exact absurd ((graftLeafFun_eq_inl_iff T' hyp hyq).mp hy) (by simp)
          · have hleaf : (∃ u : BunemanShrink p q, T'.leaf u = v) ↔
                (T'.graph.neighborSet v).ncard = 1 := by
              rw [T'.leaf_iff_degree_one v, ← SimpleGraph.ncard_neighborSet]
            rw [graftGraph_ncard_neighborSet_inl_ne _ hv, ← hleaf]
            constructor
            · rintro ⟨y, hy⟩
              have hyp : y ≠ p := fun h =>
                absurd ((graftLeafFun_eq_inr_zero T' h).symm.trans hy) (by simp)
              have hyq : y ≠ q := fun h =>
                absurd ((graftLeafFun_eq_inr_one T' hyp h).symm.trans hy) (by simp)
              exact ⟨Sum.inl ⟨y, hyp, hyq⟩, (graftLeafFun_eq_inl_iff T' hyp hyq).mp hy⟩
            · rintro ⟨u, hu⟩
              rcases u with u | u
              · refine ⟨u.1, ?_⟩
                change graftLeafFun T' u.1 = Sum.inl v
                rw [graftLeafFun_eq_inl T' u.2.1 u.2.2]
                exact congrArg Sum.inl hu
              · exact absurd (hu.symm.trans
                  (congrArg T'.leaf (congrArg Sum.inr (Subsingleton.elim u ())))) hv
        · rw [graftGraph_ncard_neighborSet_inr]
          fin_cases i
          · exact iff_of_true ⟨p, graftLeafFun_eq_inr_zero T' rfl⟩ rfl
          · exact iff_of_true ⟨q, graftLeafFun_eq_inr_one T' hpq.symm rfl⟩ rfl
      no_degree_two := by
        intro x
        rcases x with v | i
        · by_cases hv : v = T'.leaf (Sum.inr ())
          · rw [hv]
            intro hx
            rw [← SimpleGraph.ncard_neighborSet] at hx
            rw [graftGraph_ncard_neighborSet_inl_self] at hx
            omega
          · intro hx
            rw [← SimpleGraph.ncard_neighborSet] at hx
            rw [graftGraph_ncard_neighborSet_inl_ne _ hv] at hx
            exact T'.no_degree_two v (by rw [← SimpleGraph.ncard_neighborSet]; exact hx)
        · intro hx
          rw [← SimpleGraph.ncard_neighborSet] at hx
          rw [graftGraph_ncard_neighborSet_inr] at hx
          omega }

end Clad

section Phyl

open NJ.Dissimilarity

variable {Y : Type u} [Fintype Y] [DecidableEq Y] {p q r : Y}

omit [Fintype Y] [DecidableEq Y] in
/-- ★★ **非挂边的来源**：`graftGraph` 中不是两条新挂边的边必是旧边的像
（★★★ `Phylo.graftGraph_edgeSet_subset` 的直接推论）。 -/
theorem graftOldEdge_exists (T' : Cladogram (BunemanShrink p q)) {e : Sym2 (T'.V ⊕ Fin 2)}
    (he : e ∈ (graftGraph T'.graph (T'.leaf (Sum.inr ()))).edgeSet)
    (h0 : e ≠ s(Sum.inl (T'.leaf (Sum.inr ())), Sum.inr 0))
    (h1 : e ≠ s(Sum.inl (T'.leaf (Sum.inr ())), Sum.inr 1)) :
    ∃ e' ∈ T'.graph.edgeSet, Sym2.map (Sum.inl : T'.V → T'.V ⊕ Fin 2) e' = e := by
  rcases graftGraph_edgeSet_subset T'.graph (T'.leaf (Sum.inr ())) he with h | h
  · exact h
  · rcases h with h | h
    · exact absurd h h0
    · exact absurd h h1

/-- ★★ 非挂边所对应的 `T'` 的边（`Classical.choose`，权重取自 `T'.w`）。 -/
noncomputable def graftOldEdge (T' : Cladogram (BunemanShrink p q)) {e : Sym2 (T'.V ⊕ Fin 2)}
    (he : e ∈ (graftGraph T'.graph (T'.leaf (Sum.inr ()))).edgeSet)
    (h0 : e ≠ s(Sum.inl (T'.leaf (Sum.inr ())), Sum.inr 0))
    (h1 : e ≠ s(Sum.inl (T'.leaf (Sum.inr ())), Sum.inr 1)) : Edge T' :=
  ⟨Classical.choose (graftOldEdge_exists T' he h0 h1),
    (Classical.choose_spec (graftOldEdge_exists T' he h0 h1)).1⟩

/-- ★★★ **挂叶的 phylogram**：旧边沿用 `T'.w`，两条新挂边取
`δ.rho p q r` 与 `δ.rho q p r`（Buneman 第 94、119–121 行）。
非负性由 `Dissimilarity.rho_nonneg` 与 `Phylogram.w_nonneg` 给出。 -/
noncomputable def graftPhylogram (δ : NJ.Dissimilarity Y) (hfp : δ.FourPoint) (p q r : Y)
    (hpq : p ≠ q) (T' : Phylogram (BunemanShrink p q)) : Phylogram Y where
  toCladogram := graftCladogram hpq T'.toCladogram
  w := fun e =>
    if h0 : e.1 = s(Sum.inl (T'.leaf (Sum.inr ())), Sum.inr 0) then δ.rho p q r
    else if h1 : e.1 = s(Sum.inl (T'.leaf (Sum.inr ())), Sum.inr 1) then δ.rho q p r
    else T'.w (graftOldEdge T'.toCladogram e.2 h0 h1)
  w_nonneg := by
    intro e
    split_ifs with h0 h1
    · exact δ.rho_nonneg hfp p q r
    · exact δ.rho_nonneg hfp q p r
    · exact T'.w_nonneg _

end Phyl

end Phylo
