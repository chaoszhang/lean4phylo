/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.Laminar
import Phylo.Stat.NJst

/-!
# `Phylo.Stat.NJstWitness` —— `|X| = 4` 上**非退化**的 `NJstData` 见证

`Phylo/Stat/NJst.lean` 里的唯一见证 `njstDataFin2` 是**退化**的：`|X| = 2` 的树上没有内部顶点，
故 `hT_binary` **空真**。本文件消掉这个空真风险，给出 `|X| = 4` 上的**非退化**见证：

* 实现树 = **各边权 `1` 的 `12|34` 二叉树**（`0,1` 挂在内部顶点 `Uv` 上，`2,3` 挂在内部顶点 `Qv` 上，
  `Uv—Qv` 一条内部边）；6 顶点、5 边、度数 `3,3,1,1,1,1`；
* 拓扑由**镶嵌族建树** `Phylo.toCladogram` 给出（镶嵌族 `F1234 = {univ, {2,3}}`），
  于是 `Cladogram` 的五个字段（`isTree` / `leaf_iff_degree_one` / `no_degree_two` …）
  全部由 `Phylo/Laminar.lean` 的现成定理免费提供；
* `T1234_isBinary`（两个内部顶点度**恰为** `3`）与 `T1234_displaysQuartet`
  （该树**真的**展示 quartet `01|23`）都是**非空真**的证书。

## 本文件的主要声明

* `F1234` —— 镶嵌族 `{{0,1,2,3}, {2,3}}`；
* `C1234` —— 由 `F1234` 经 `Phylo.toCladogram` 得到的 `Cladogram (Fin 4)`；
* `T1234` —— 各边权 `1` 的 `Phylogram (Fin 4)`；内部顶点 `Uv`、`Qv`；
* `T1234_isBinary` · `T1234_dist` · `T1234_displaysQuartet`；
* `njstDataFin4` —— ★★★ `|X| = 4` 上 `NJstData` 的**非退化**可居留实例。

## 距离记账

`T1234` 各边权为 `1`，故 `walkDist` 就是**边数**（`walkDist_eq_edges_length`），
于是 `Phylo.TreeDist.dist_eq_walkDist_of_isPath` 把「算权和」降成「造一条 `IsPath` walk + 数边数」；
树距离表（`T1234_dist`）为：同标签 `0`、`01` 与 `23` 为 `2`、跨侧为 `3`。
-/

open NJ
open Phylo
open Classical

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## 1. 镶嵌族 `{{0,1,2,3}, {2,3}}` -/

/-- 各边权 `1` 的 `12|34` 二叉树的镶嵌族：全簇 `univ = {0,1,2,3}` 与 `{2,3}`。 -/
def F1234 : Finset (Finset (Fin 4)) := {Finset.univ, ({2, 3} : Finset (Fin 4))}

theorem mem_F1234 {A : Finset (Fin 4)} :
    A ∈ F1234 ↔ A = Finset.univ ∨ A = ({2, 3} : Finset (Fin 4)) := by
  simp [F1234]

theorem univ_mem_F1234 : (Finset.univ : Finset (Fin 4)) ∈ F1234 := by
  rw [mem_F1234]; exact Or.inl rfl

theorem pair_mem_F1234 : ({2, 3} : Finset (Fin 4)) ∈ F1234 := by
  rw [mem_F1234]; exact Or.inr rfl

theorem card_pair_F1234 : (({2, 3} : Finset (Fin 4))).card = 2 := by decide

theorem two_le_card_pair_F1234 : 2 ≤ (({2, 3} : Finset (Fin 4))).card := by
  rw [card_pair_F1234]

theorem pair_ne_univ_F1234 : ({2, 3} : Finset (Fin 4)) ≠ Finset.univ := by decide

theorem nonempty_pair_F1234 : (({2, 3} : Finset (Fin 4))).Nonempty := by decide

theorem laminar_F1234 : LaminarFamily F1234 := by
  intro A hA B hB
  rw [mem_F1234] at hA hB
  rcases hA with rfl | rfl <;> rcases hB with rfl | rfl
  · exact Or.inl (Finset.Subset.refl _)
  · exact Or.inr (Or.inl (Finset.subset_univ _))
  · exact Or.inl (Finset.subset_univ _)
  · exact Or.inl (Finset.Subset.refl _)

theorem nonempty_F1234 : ∀ B ∈ F1234, B.Nonempty := by
  intro B hB
  rw [mem_F1234] at hB
  rcases hB with rfl | rfl
  · exact Finset.univ_nonempty
  · exact nonempty_pair_F1234

theorem card_mem_F1234 : ∀ B ∈ F1234, B = Finset.univ ∨ 2 ≤ B.card := by
  intro B hB
  rw [mem_F1234] at hB
  rcases hB with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr two_le_card_pair_F1234

/-! ## 2. `toCladogram` 的第五个前置条件 `hroot`（根度 ≥ 3）

`|univ 的孩子| = |{{2,3}}| = 1`、`|univ 的直接元素| = |{0,1}| = 2`，故和为 `3`。
两个 `Finset` 基数各自单独证出。 -/

theorem isParentOf_pair_univ_F1234 :
    IsParentOf F1234 ({2, 3} : Finset (Fin 4)) Finset.univ := by
  refine ⟨univ_mem_F1234, ?_, ?_⟩
  · exact Finset.ssubset_iff_subset_ne.mpr
      ⟨Finset.subset_univ _, fun h => pair_ne_univ_F1234 h⟩
  · intro C hC hlt
    rw [mem_F1234] at hC
    rcases hC with rfl | rfl
    · exact Finset.Subset.refl _
    · exact absurd hlt.1 hlt.2

theorem isChildOf_univ_pair_F1234 :
    IsChildOf F1234 Finset.univ ({2, 3} : Finset (Fin 4)) := by
  refine ⟨pair_mem_F1234, ?_, ?_⟩
  · exact Finset.ssubset_iff_subset_ne.mpr
      ⟨Finset.subset_univ _, fun h => pair_ne_univ_F1234 h⟩
  · intro C hC hlt
    rw [mem_F1234] at hC
    rcases hC with rfl | rfl
    · intro h
      exact absurd h.1 h.2
    · exact absurd hlt.1 hlt.2

theorem card_filter_isChildOf_F1234 :
    (F1234.filter fun B => IsChildOf F1234 Finset.univ B).card = 1 := by
  rw [Finset.card_eq_one]
  refine ⟨({2, 3} : Finset (Fin 4)), ?_⟩
  ext B
  rw [Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro ⟨hB, hchild⟩
    rw [mem_F1234] at hB
    rcases hB with rfl | rfl
    · exact absurd (Finset.Subset.refl _) hchild.2.1.2
    · rfl
  · intro hB
    rw [hB]
    exact ⟨pair_mem_F1234, isChildOf_univ_pair_F1234⟩

theorem directElems_univ_F1234 :
    directElems F1234 (Finset.univ : Finset (Fin 4)) = ({0, 1} : Finset (Fin 4)) := by
  ext x
  rw [mem_directElems]
  constructor
  · rintro ⟨-, hx⟩
    fin_cases x
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    · exfalso
      exact absurd (hx ({2, 3} : Finset (Fin 4)) pair_mem_F1234 (by decide)
        (Finset.mem_univ (0 : Fin 4))) (by decide)
    · exfalso
      exact absurd (hx ({2, 3} : Finset (Fin 4)) pair_mem_F1234 (by decide)
        (Finset.mem_univ (0 : Fin 4))) (by decide)
  · intro hx
    refine ⟨Finset.mem_univ x, ?_⟩
    intro B hB hxB
    rw [mem_F1234] at hB
    rcases hB with rfl | rfl
    · exact Finset.Subset.refl _
    · exfalso
      fin_cases x
      · exact absurd hxB (by decide)
      · exact absurd hxB (by decide)
      · exact absurd hx (by decide)
      · exact absurd hx (by decide)

theorem card_directElems_univ_F1234 :
    (directElems F1234 (Finset.univ : Finset (Fin 4))).card = 2 := by
  rw [directElems_univ_F1234]
  decide

theorem hroot_F1234 : 3 ≤ (F1234.filter fun B => IsChildOf F1234 Finset.univ B).card
    + (directElems F1234 Finset.univ).card := by
  rw [card_filter_isChildOf_F1234, card_directElems_univ_F1234]

/-! ## 3. 树 `C1234` 与各边权 `1` 的 `Phylogram T1234` -/

/-- 由镶嵌族 `F1234` 经 `Phylo.toCladogram` 得到的树（6 顶点）。 -/
def C1234 : Cladogram (Fin 4) :=
  toCladogram laminar_F1234 nonempty_F1234 univ_mem_F1234 card_mem_F1234 hroot_F1234

/-- ★ 各边权 `1` 的 `12|34` 二叉树（`0,1 | 2,3`），实现树即 `C1234`。 -/
def T1234 : Phylogram.{0, 0} (Fin 4) where
  toCladogram := C1234
  w := fun _ => 1
  w_nonneg := fun _ => by norm_num

/-- 内部顶点 `Uv`（全簇 `{0,1,2,3}`，邻居恰为 `Qv, 0, 1`）。 -/
abbrev Uv : LaminarVertex F1234 := Sum.inl (⟨Finset.univ, univ_mem_F1234⟩ : ↥F1234)

/-- 内部顶点 `Qv`（簇 `{2,3}`，邻居恰为 `Uv, 2, 3`）。 -/
abbrev Qv : LaminarVertex F1234 :=
  Sum.inl (⟨({2, 3} : Finset (Fin 4)), pair_mem_F1234⟩ : ↥F1234)

theorem leaf_zero_eq : T1234.leaf (0 : Fin 4) = Sum.inr (0 : Fin 4) := rfl

theorem leaf_one_eq : T1234.leaf (1 : Fin 4) = Sum.inr (1 : Fin 4) := rfl

theorem leaf_two_eq : T1234.leaf (2 : Fin 4) = Sum.inr (2 : Fin 4) := rfl

theorem leaf_three_eq : T1234.leaf (3 : Fin 4) = Sum.inr (3 : Fin 4) := rfl

/-! ### 邻接（由 `laminarAdj` 的定义直接算） -/

theorem isMinClusterOf_zero_F1234 : IsMinClusterOf F1234 (0 : Fin 4) Finset.univ := by
  refine ⟨univ_mem_F1234, Finset.mem_univ _, ?_⟩
  intro C hC hxC
  rw [mem_F1234] at hC
  rcases hC with rfl | rfl
  · exact Finset.Subset.refl _
  · exact absurd hxC (by decide)

theorem isMinClusterOf_one_F1234 : IsMinClusterOf F1234 (1 : Fin 4) Finset.univ := by
  refine ⟨univ_mem_F1234, Finset.mem_univ _, ?_⟩
  intro C hC hxC
  rw [mem_F1234] at hC
  rcases hC with rfl | rfl
  · exact Finset.Subset.refl _
  · exact absurd hxC (by decide)

theorem isMinClusterOf_two_F1234 :
    IsMinClusterOf F1234 (2 : Fin 4) ({2, 3} : Finset (Fin 4)) := by
  refine ⟨pair_mem_F1234, by decide, ?_⟩
  intro C hC _
  rw [mem_F1234] at hC
  rcases hC with rfl | rfl
  · exact Finset.subset_univ _
  · exact Finset.Subset.refl _

theorem isMinClusterOf_three_F1234 :
    IsMinClusterOf F1234 (3 : Fin 4) ({2, 3} : Finset (Fin 4)) := by
  refine ⟨pair_mem_F1234, by decide, ?_⟩
  intro C hC _
  rw [mem_F1234] at hC
  rcases hC with rfl | rfl
  · exact Finset.subset_univ _
  · exact Finset.Subset.refl _

theorem adj_Uv_Qv : (treeGraph F1234).Adj Uv Qv :=
  (treeGraph_adj_inl_inl F1234 (⟨Finset.univ, univ_mem_F1234⟩ : ↥F1234)
      (⟨({2, 3} : Finset (Fin 4)), pair_mem_F1234⟩ : ↥F1234)).mpr
    (Or.inr isParentOf_pair_univ_F1234)

theorem adj_leaf0_Uv : (treeGraph F1234).Adj (Sum.inr (0 : Fin 4)) Uv :=
  (treeGraph_adj_inr_inl F1234 (0 : Fin 4) (⟨Finset.univ, univ_mem_F1234⟩ : ↥F1234)).mpr
    isMinClusterOf_zero_F1234

theorem adj_leaf1_Uv : (treeGraph F1234).Adj (Sum.inr (1 : Fin 4)) Uv :=
  (treeGraph_adj_inr_inl F1234 (1 : Fin 4) (⟨Finset.univ, univ_mem_F1234⟩ : ↥F1234)).mpr
    isMinClusterOf_one_F1234

theorem adj_leaf2_Qv : (treeGraph F1234).Adj (Sum.inr (2 : Fin 4)) Qv :=
  (treeGraph_adj_inr_inl F1234 (2 : Fin 4)
      (⟨({2, 3} : Finset (Fin 4)), pair_mem_F1234⟩ : ↥F1234)).mpr
    isMinClusterOf_two_F1234

theorem adj_leaf3_Qv : (treeGraph F1234).Adj (Sum.inr (3 : Fin 4)) Qv :=
  (treeGraph_adj_inr_inl F1234 (3 : Fin 4)
      (⟨({2, 3} : Finset (Fin 4)), pair_mem_F1234⟩ : ↥F1234)).mpr
    isMinClusterOf_three_F1234

/-! ### 度：`Uv` 与 `Qv` 的邻居各恰三个

下界由库内定理 `Phylo.three_le_degree_rootV` / `Phylo.three_le_degree_treeGraph` 给出，
上界由把 `neighborFinset` 夹进显式三元素集合（`Finset.card_le_three`）给出。 -/

theorem degree_Uv_le_three : (treeGraph F1234).degree Uv ≤ 3 := by
  have hsub : (treeGraph F1234).neighborFinset Uv ⊆
      ({Qv, Sum.inr (0 : Fin 4), Sum.inr (1 : Fin 4)} : Finset (LaminarVertex F1234)) := by
    intro u hu
    rw [SimpleGraph.mem_neighborFinset] at hu
    rcases u with B | x
    · rw [treeGraph_adj_inl_inl] at hu
      rcases hu with h1 | h2
      · exact absurd (Finset.subset_univ B.1) h1.2.1.2
      · have hBne : B.1 ≠ Finset.univ := by
          intro h
          rw [h] at h2
          exact absurd (Finset.Subset.refl _) h2.2.1.2
        have hBmem : B.1 ∈ F1234 := B.2
        rw [mem_F1234] at hBmem
        have hBeq : B = (⟨({2, 3} : Finset (Fin 4)), pair_mem_F1234⟩ : ↥F1234) := by
          refine Subtype.ext ?_
          rcases hBmem with hb | hb
          · exact absurd hb hBne
          · exact hb
        exact Finset.mem_insert.mpr (Or.inl (congrArg Sum.inl hBeq))
    · rw [treeGraph_adj_inl_inr] at hu
      have hx : x = 0 ∨ x = 1 := by
        fin_cases x
        · exact Or.inl rfl
        · exact Or.inr rfl
        · exfalso
          exact absurd (hu.2.2 ({2, 3} : Finset (Fin 4)) pair_mem_F1234 (by decide)
            (Finset.mem_univ (0 : Fin 4))) (by decide)
        · exfalso
          exact absurd (hu.2.2 ({2, 3} : Finset (Fin 4)) pair_mem_F1234 (by decide)
            (Finset.mem_univ (0 : Fin 4))) (by decide)
      rcases hx with hx | hx
      · rw [hx]
        exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
      · rw [hx]
        exact Finset.mem_insert_of_mem
          (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  calc (treeGraph F1234).degree Uv
      = ((treeGraph F1234).neighborFinset Uv).card :=
        (SimpleGraph.card_neighborFinset_eq_degree _ _).symm
    _ ≤ ({Qv, Sum.inr (0 : Fin 4), Sum.inr (1 : Fin 4)} :
          Finset (LaminarVertex F1234)).card := Finset.card_le_card hsub
    _ ≤ 3 := Finset.card_le_three

theorem degree_Qv_le_three : (treeGraph F1234).degree Qv ≤ 3 := by
  have hsub : (treeGraph F1234).neighborFinset Qv ⊆
      ({Uv, Sum.inr (2 : Fin 4), Sum.inr (3 : Fin 4)} : Finset (LaminarVertex F1234)) := by
    intro u hu
    rw [SimpleGraph.mem_neighborFinset] at hu
    rcases u with B | x
    · rw [treeGraph_adj_inl_inl] at hu
      have hBmem : B.1 ∈ F1234 := B.2
      rw [mem_F1234] at hBmem
      have hBuniv : B.1 = Finset.univ := by
        rcases hu with h1 | h2
        · rcases hBmem with hb | hb
          · exact hb
          · exfalso
            rw [hb] at h1
            exact absurd h1.2.1.1 h1.2.1.2
        · rcases hBmem with hb | hb
          · exact hb
          · exfalso
            rw [hb] at h2
            exact absurd h2.2.1.1 h2.2.1.2
      exact Finset.mem_insert.mpr
        (Or.inl (congrArg Sum.inl (Subtype.ext hBuniv)))
    · rw [treeGraph_adj_inl_inr] at hu
      have hx : x = 2 ∨ x = 3 := by
        have hmem := hu.2.1
        fin_cases x
        · exfalso; exact absurd hmem (by decide)
        · exfalso; exact absurd hmem (by decide)
        · exact Or.inl rfl
        · exact Or.inr rfl
      rcases hx with hx | hx
      · rw [hx]
        exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
      · rw [hx]
        exact Finset.mem_insert_of_mem
          (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  calc (treeGraph F1234).degree Qv
      = ((treeGraph F1234).neighborFinset Qv).card :=
        (SimpleGraph.card_neighborFinset_eq_degree _ _).symm
    _ ≤ ({Uv, Sum.inr (2 : Fin 4), Sum.inr (3 : Fin 4)} :
          Finset (LaminarVertex F1234)).card := Finset.card_le_card hsub
    _ ≤ 3 := Finset.card_le_three

theorem three_le_degree_Uv : 3 ≤ (treeGraph F1234).degree Uv :=
  three_le_degree_rootV laminar_F1234 nonempty_F1234 univ_mem_F1234 hroot_F1234

theorem three_le_degree_Qv : 3 ≤ (treeGraph F1234).degree Qv :=
  three_le_degree_treeGraph laminar_F1234 nonempty_F1234 univ_mem_F1234
    (A := (⟨({2, 3} : Finset (Fin 4)), pair_mem_F1234⟩ : ↥F1234))
    pair_ne_univ_F1234 two_le_card_pair_F1234

/-- ★★ **拓扑是 binary**：两个内部顶点度**恰为** `3`（四个叶顶点度 `1`）。

⚠️ 这正是 `njstDataFin2` **空真**掉的那条（`|X| = 2` 时没有内部顶点）—— 本文件在 `|X| = 4` 上真证。 -/
theorem T1234_isBinary : T1234.toCladogram.IsBinary := by
  intro v hv
  rcases v with A | x
  · have hA := A.2
    rw [mem_F1234] at hA
    rcases hA with hA | hA
    · have hAeq : A = (⟨Finset.univ, univ_mem_F1234⟩ : ↥F1234) := Subtype.ext hA
      rw [hAeq]
      change (treeGraph F1234).degree Uv = 3
      have h3 := three_le_degree_Uv
      have hle := degree_Uv_le_three
      omega
    · have hAeq : A = (⟨({2, 3} : Finset (Fin 4)), pair_mem_F1234⟩ : ↥F1234) :=
        Subtype.ext hA
      rw [hAeq]
      change (treeGraph F1234).degree Qv = 3
      have h3 := three_le_degree_Qv
      have hle := degree_Qv_le_three
      omega
  · exact absurd ⟨x, rfl⟩ hv

/-! ## 4. 距离：各边权 `1` 时的记账

树距离表：同标签 `0`；`0-1` 与 `2-3` 为 `2`；跨侧（`0/1` 对 `2/3`）为 `3`。 -/

/-- **各边权 `1` 时的距离记账工具**：`walkDist` 就是 walk 的边数。 -/
theorem walkDist_eq_edges_length {X : Type*} (T : Phylogram X)
    (h1 : ∀ e : Edge T.toCladogram, T.w e = 1) {u v : T.V} (p : T.graph.Walk u v) :
    T.walkDist p = (p.edges.length : ℝ) := by
  unfold Phylogram.walkDist
  have hmem : ∀ e ∈ p.edges, T.wExt e = 1 := by
    intro e he
    have hE : e ∈ T.graph.edgeSet := SimpleGraph.Walk.edges_subset_edgeSet p he
    rw [Phylogram.wExt, dite_eq_left hE]
    exact h1 ⟨e, hE⟩
  rw [List.map_congr_left hmem, List.map_const', List.sum_replicate]
  simp

theorem T1234_w_eq_one (e : Edge T1234.toCladogram) : T1234.w e = 1 := rfl

theorem dist_eq_edges_of_walk {a b : LaminarVertex F1234} (p : (treeGraph F1234).Walk a b)
    (hp : p.IsPath) : T1234.dist a b = (p.edges.length : ℝ) := by
  rw [Phylo.TreeDist.dist_eq_walkDist_of_isPath T1234 p hp,
    walkDist_eq_edges_length T1234 T1234_w_eq_one p]
  rfl

theorem dist_eq_two_of_walk {a b : LaminarVertex F1234} (p : (treeGraph F1234).Walk a b)
    (hp : p.IsPath) (hn : p.edges.length = 2) : T1234.dist a b = 2 := by
  rw [dist_eq_edges_of_walk p hp, hn]
  norm_num

theorem dist_eq_three_of_walk {a b : LaminarVertex F1234} (p : (treeGraph F1234).Walk a b)
    (hp : p.IsPath) (hn : p.edges.length = 3) : T1234.dist a b = 3 := by
  rw [dist_eq_edges_of_walk p hp, hn]
  norm_num

/-! ### `IsPath` 的两个组合子（`decide` 会被 `SimpleGraph.Walk` 的 `Decidable` 实例卡住，故手证） -/

theorem isPath_chain2 {u v w : LaminarVertex F1234} (h1 : (treeGraph F1234).Adj u v)
    (h2 : (treeGraph F1234).Adj v w) (huw : u ≠ w) :
    (SimpleGraph.Walk.cons h1 (SimpleGraph.Walk.cons h2 SimpleGraph.Walk.nil)).IsPath := by
  refine SimpleGraph.Walk.IsPath.cons ?_ ?_
  · refine SimpleGraph.Walk.IsPath.cons SimpleGraph.Walk.IsPath.nil ?_
    simpa [SimpleGraph.Walk.support_nil] using h2.ne
  · intro hmem
    rw [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil] at hmem
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    exact hmem.elim h1.ne huw

theorem isPath_chain3 {u v w z : LaminarVertex F1234} (h1 : (treeGraph F1234).Adj u v)
    (h2 : (treeGraph F1234).Adj v w) (h3 : (treeGraph F1234).Adj w z)
    (huw : u ≠ w) (huz : u ≠ z) (hvz : v ≠ z) :
    (SimpleGraph.Walk.cons h1 (SimpleGraph.Walk.cons h2
      (SimpleGraph.Walk.cons h3 SimpleGraph.Walk.nil))).IsPath := by
  refine SimpleGraph.Walk.IsPath.cons ?_ ?_
  · refine SimpleGraph.Walk.IsPath.cons ?_ ?_
    · refine SimpleGraph.Walk.IsPath.cons SimpleGraph.Walk.IsPath.nil ?_
      simpa [SimpleGraph.Walk.support_nil] using h3.ne
    · intro hmem
      rw [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil] at hmem
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
      exact hmem.elim h2.ne hvz
  · intro hmem
    rw [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_cons,
      SimpleGraph.Walk.support_nil] at hmem
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with h | h | h
    · exact h1.ne h
    · exact huw h
    · exact huz h

/-! ### 六个具体距离（其余由对称性给出） -/

theorem dist_zero_one : T1234.dist (T1234.leaf (0 : Fin 4)) (T1234.leaf (1 : Fin 4)) = 2 :=
  dist_eq_two_of_walk
    (SimpleGraph.Walk.cons adj_leaf0_Uv
      (SimpleGraph.Walk.cons adj_leaf1_Uv.symm SimpleGraph.Walk.nil))
    (isPath_chain2 adj_leaf0_Uv adj_leaf1_Uv.symm (by simp)) (by decide)

theorem dist_one_zero : T1234.dist (T1234.leaf (1 : Fin 4)) (T1234.leaf (0 : Fin 4)) = 2 := by
  rw [Phylo.TreeDist.dist_comm T1234]
  exact dist_zero_one

theorem dist_two_three : T1234.dist (T1234.leaf (2 : Fin 4)) (T1234.leaf (3 : Fin 4)) = 2 :=
  dist_eq_two_of_walk
    (SimpleGraph.Walk.cons adj_leaf2_Qv
      (SimpleGraph.Walk.cons adj_leaf3_Qv.symm SimpleGraph.Walk.nil))
    (isPath_chain2 adj_leaf2_Qv adj_leaf3_Qv.symm (by simp)) (by decide)

theorem dist_three_two : T1234.dist (T1234.leaf (3 : Fin 4)) (T1234.leaf (2 : Fin 4)) = 2 := by
  rw [Phylo.TreeDist.dist_comm T1234]
  exact dist_two_three

theorem dist_zero_two : T1234.dist (T1234.leaf (0 : Fin 4)) (T1234.leaf (2 : Fin 4)) = 3 :=
  dist_eq_three_of_walk
    (SimpleGraph.Walk.cons adj_leaf0_Uv
      (SimpleGraph.Walk.cons adj_Uv_Qv
        (SimpleGraph.Walk.cons adj_leaf2_Qv.symm SimpleGraph.Walk.nil)))
    (isPath_chain3 adj_leaf0_Uv adj_Uv_Qv adj_leaf2_Qv.symm (by simp) (by simp) (by simp))
    (by decide)

theorem dist_one_two : T1234.dist (T1234.leaf (1 : Fin 4)) (T1234.leaf (2 : Fin 4)) = 3 :=
  dist_eq_three_of_walk
    (SimpleGraph.Walk.cons adj_leaf1_Uv
      (SimpleGraph.Walk.cons adj_Uv_Qv
        (SimpleGraph.Walk.cons adj_leaf2_Qv.symm SimpleGraph.Walk.nil)))
    (isPath_chain3 adj_leaf1_Uv adj_Uv_Qv adj_leaf2_Qv.symm (by simp) (by simp) (by simp))
    (by decide)

theorem dist_zero_three : T1234.dist (T1234.leaf (0 : Fin 4)) (T1234.leaf (3 : Fin 4)) = 3 :=
  dist_eq_three_of_walk
    (SimpleGraph.Walk.cons adj_leaf0_Uv
      (SimpleGraph.Walk.cons adj_Uv_Qv
        (SimpleGraph.Walk.cons adj_leaf3_Qv.symm SimpleGraph.Walk.nil)))
    (isPath_chain3 adj_leaf0_Uv adj_Uv_Qv adj_leaf3_Qv.symm (by simp) (by simp) (by simp))
    (by decide)

theorem dist_one_three : T1234.dist (T1234.leaf (1 : Fin 4)) (T1234.leaf (3 : Fin 4)) = 3 :=
  dist_eq_three_of_walk
    (SimpleGraph.Walk.cons adj_leaf1_Uv
      (SimpleGraph.Walk.cons adj_Uv_Qv
        (SimpleGraph.Walk.cons adj_leaf3_Qv.symm SimpleGraph.Walk.nil)))
    (isPath_chain3 adj_leaf1_Uv adj_Uv_Qv adj_leaf3_Qv.symm (by simp) (by simp) (by simp))
    (by decide)

theorem dist_two_zero : T1234.dist (T1234.leaf (2 : Fin 4)) (T1234.leaf (0 : Fin 4)) = 3 := by
  rw [Phylo.TreeDist.dist_comm T1234]
  exact dist_zero_two

theorem dist_two_one : T1234.dist (T1234.leaf (2 : Fin 4)) (T1234.leaf (1 : Fin 4)) = 3 := by
  rw [Phylo.TreeDist.dist_comm T1234]
  exact dist_one_two

theorem dist_three_zero : T1234.dist (T1234.leaf (3 : Fin 4)) (T1234.leaf (0 : Fin 4)) = 3 := by
  rw [Phylo.TreeDist.dist_comm T1234]
  exact dist_zero_three

theorem dist_three_one : T1234.dist (T1234.leaf (3 : Fin 4)) (T1234.leaf (1 : Fin 4)) = 3 := by
  rw [Phylo.TreeDist.dist_comm T1234]
  exact dist_one_three

/-- ★★ **`T1234` 的树距离显式表**：同标签 `0`；`0-1`、`2-3` 为 `2`；跨侧为 `3`。 -/
theorem T1234_dist (x y : Fin 4) :
    T1234.dist (T1234.leaf x) (T1234.leaf y) =
      if x = y then 0 else if (x < 2) = (y < 2) then 2 else 3 := by
  fin_cases x <;> fin_cases y <;>
    simp [Phylogram.dist_self, dist_zero_one, dist_one_zero, dist_two_three, dist_three_two,
      dist_zero_two, dist_one_two, dist_zero_three, dist_one_three,
      dist_two_zero, dist_two_one, dist_three_zero, dist_three_one]

/-! ## 5. ★★★ 非空真证书：该树**真的**展示 quartet `01|23`

内部边 `Uv—Qv`（对应镶嵌族成员 `{2,3}`）把叶集分成 `{2,3}`（`Qv` 侧）与 `{0,1}`（`Uv` 侧）。
用 `Phylo.isSplitOf_splitOf` 得 `IsSplitOf (splitOf {2,3})`，再用
`Cladogram.displaysQuartet_of_clade` 得 `DisplaysQuartet 2 3 0 1`，最后用
`Cladogram.displaysQuartet_comm_cd` 交换两侧次序。 -/

theorem isSplitOf_pair_F1234 : T1234.toCladogram.IsSplitOf
    (splitOf ({2, 3} : Finset (Fin 4)) nonempty_pair_F1234
      (compl_nonempty_of_ne_univ pair_ne_univ_F1234)) :=
  isSplitOf_splitOf laminar_F1234 nonempty_F1234 univ_mem_F1234 card_mem_F1234 hroot_F1234
    pair_mem_F1234 pair_ne_univ_F1234

/-- ★★★ **非空真证书**：`T1234` 展示 quartet `01|23`（不是空真）。 -/
theorem T1234_displaysQuartet : T1234.toCladogram.DisplaysQuartet 0 1 2 3 := by
  have h : T1234.toCladogram.DisplaysQuartet 2 3 0 1 := by
    refine Cladogram.displaysQuartet_of_clade (T := T1234.toCladogram)
      (s := splitOf ({2, 3} : Finset (Fin 4)) nonempty_pair_F1234
        (compl_nonempty_of_ne_univ pair_ne_univ_F1234)) isSplitOf_pair_F1234 ?_ ?_ ?_ ?_
    · simp
    · simp
    · simp
    · simp
  exact (Cladogram.displaysQuartet_comm_cd T1234.toCladogram 2 3 0 1).mp h

/-! ## 6. ★★★ 非退化见证 `njstDataFin4` -/

/-- `T1234` 的树距离相异度。 -/
def T1234Dissim : Dissimilarity (Fin 4) where
  val x y := T1234.dist (T1234.leaf x) (T1234.leaf y)
  symm x y := Phylo.TreeDist.dist_comm T1234 (T1234.leaf x) (T1234.leaf y)
  diag x := Phylogram.dist_self T1234 (T1234.leaf x)

@[simp] theorem T1234Dissim_val (x y : Fin 4) :
    T1234Dissim.val x y = T1234.dist (T1234.leaf x) (T1234.leaf y) := rfl

/-- 树距离的**四点条件**（`Fin 4` 上全部 `4^4 = 256` 个情形的数字穷举）。 -/
theorem T1234Dissim_fourPoint : T1234Dissim.FourPoint := by
  intro i j k l
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp only [T1234Dissim_val, T1234_dist] <;> norm_num

/-- ★★★ **非退化见证**：`|X| = 4` 上 `NJstData` 的**可居留实例**，实现树是各边权 `1` 的 `12|34`。

与退化的 `njstDataFin2` 相比，这里 `hT_binary` 与 `hT_pos` 都**非空真**：
`T1234` 有 6 个顶点、两个内部顶点度恰为 `3`（`T1234_isBinary`），且每条边权为 `1`。 -/
abbrev njstDataFin4 : NJstData.{0, 0} (Fin 4) where
  δ := T1234Dissim
  δr := T1234Dissim
  w := fun _ => 1
  ustar := by
    intro x y _
    simp only [T1234Dissim_val]
    ring
  T := T1234
  hT_binary := T1234_isBinary
  hT_pos := by
    intro e
    rw [T1234_w_eq_one e]
    norm_num
  hT_dist := fun _ _ => rfl
  starFourPoint := T1234Dissim_fourPoint

end
