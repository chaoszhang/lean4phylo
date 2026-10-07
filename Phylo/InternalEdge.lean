/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.SideSubtree
import Phylo.Algorithm.Cherry

/-!
# `Phylo.InternalEdge` —— 内部边（非叶端点）一侧含 ≥ 2 叶（`SideSubtree` 阶段 2）

`Phylo/SideSubtree.lean` 已证「边的侧分量诱导一棵子树」（阶段 1）。本文件补上**阶段 2**：

> **`no_degree_two` 的树中，若边 `s(u,v)` 的端点 `u` 不是叶，则 `u` 一侧至少含 2 个叶。**

这是 HANDOVER §3 / §4 的 **T2** —— 「T1 第 1 步 / quartet → split 恢复 / KF 距离」三处的共同前置。

## 证明（握手引理 + 局部度数界）

设 `U := T.sideVertices s(u,v) u`（`T − e` 中含 `u` 的分量），`G' := T.graph.induce ↑U`。

1. **只有 `e` 跨越 `U`**（`SideSubtree.eq_edge_of_adj_of_mem_sideVertices_of_notMem`）；
2. 于是 `x ∈ U`、`x ≠ u` ⟹ `N_T(x) ⊆ U`，故 `deg_{G'}(x) = deg_T(x)`；
   * `x` 度 1 ⟹ `deg_{G'}(x) = 1`；* `x` 非叶 ⟹ `deg_{G'}(x) ≥ 3`（`no_degree_two` + 无孤立点）；
3. `N_T(u) ⊆ U ∪ {v}` 且 `v ∉ U`，故 `deg_{G'}(u) ≥ deg_T(u) − 1 ≥ 2`；
4. 在 `G'` 上用握手引理 `∑ deg = 2·#边`，按「度 1 / 非 `u` 非叶 / `u`」三段夹逼：
   `ℓ_U + 3(i_U − 1) + 2 ≤ 2(|U| − 1)`，代入 `|U| = ℓ_U + i_U` 得 **`ℓ_U ≥ i_U + 1 ≥ 2`**。

## 修正记录（2026-10-08）

`HANDOVER.md` §4 与 `SideSubtree.lean` 旧注释的骨架第 2 步写的是「`x ≠ u` ⟹ `N(x) ⊆ U`」。
**这是假命题**：取 `T` 为路径 `u—x—w`、`e = {x,w}`，则 `u, x ∈ U` 而 `w ∉ U`。
正确形式是 `N(x) ⊆ U ∪ {u}`（弱化版；`u` 单独处理）。由旧骨架另派生两条**等价的死路**：

* 「`e = s(x,w)` ⟹ 删边后 `x`、`w` 仍相邻」：`Sym2.eq_swap` 给出 `s(w,x) = s(x,w)`，
  与 `e = s(x,w)` 合起来**证明了** `s(w,x) = e`，故该命题为假；
* 「`u ∈ e`」：路径反例中 `u` 是 `e` 的邻居侧点，不在 `e` 里。

## 实现注记（性能）

`T.sideVertices e u` 是带 `classical` 的 `noncomputable def`，出现在 `T.graph.induce ↑(⋯)` 的
类型里时每次 `whnf` 都极贵。对策：计数引理 `two_le_card_degree_one_of_side` 对**不透明的
`U : Finset T.V`** 陈述，`sideVertices` 只在最后实例化一次。此外
`degree_induce_of_neighborSet_subset` / `map_neighborFinset_induce` 在本环境里会 `whnf`
超时或 `rw` 匹配失败（`Set.toFinset` 的 `Fintype` 实例不 defeq），改用自证的
`degree_induce_eq_card_inter`（`Finset.card_bij`，完全不碰 `Set.toFinset`）。
-/

open Phylo
open SimpleGraph

universe u v

namespace Cladogram

variable {X : Type u} [Fintype X] [DecidableEq X]

set_option linter.unusedSectionVars false

variable (T : Cladogram.{u, v} X)

/-! ## 辅助引理：`Sym2` 端点提取 -/

/-- **`Sym2` 端点提取**：`u ∈ e`、`e = s(x,w)`、`u ≠ x` ⟹ `u = w`。 -/
theorem eq_of_mem_of_eq_pair {e : Sym2 T.V} {u x w : T.V}
    (hu : u ∈ e) (he : s(x, w) = e) (hux : u ≠ x) : u = w := by
  rw [← he] at hu
  rcases Sym2.mem_iff.mp hu with h | h
  · exact absurd h hux
  · exact h

/-- 若 `e = s(x,w)`，则 `x ∈ e`。 -/
theorem mem_pair_left {e : Sym2 T.V} {x w : T.V} (he : s(x, w) = e) : x ∈ e :=
  he ▸ (Sym2.mem_iff.mpr (Or.inl rfl) : x ∈ s(x, w))

/-- 若 `e = s(x,w)`，则 `w ∈ e`。 -/
theorem mem_pair_right {e : Sym2 T.V} {x w : T.V} (he : s(x, w) = e) : w ∈ e :=
  he ▸ (Sym2.mem_iff.mpr (Or.inr rfl) : w ∈ s(x, w))

/-- 由 `s(x,w) = e = s(x,u)` 与 `u ≠ x` 得 `w = u`（走 `Sym2.eq_iff`，避开 `mem_iff` 的坑）。 -/
theorem eq_right_of_eq_pair {e : Sym2 T.V} {x w u : T.V}
    (he : s(x, w) = e) (hu : e = s(x, u)) (hux : u ≠ x) : w = u := by
  rcases Sym2.eq_iff.mp (he.trans hu) with ⟨-, h2⟩ | ⟨h1, -⟩
  · exact h2
  · exact absurd h1.symm hux

/-- 有边即有两个顶点（`|V| ≥ 2`）。 -/
theorem two_le_card_of_adj {u v : T.V} (huv : T.graph.Adj u v) : 2 ≤ Fintype.card T.V :=
  Fintype.one_lt_card_iff_nontrivial.mpr ⟨u, v, huv.ne⟩

/-! ## 诱导子图中一个顶点的度 -/

/-- ★ **诱导子图中 `x` 的度 = `#(N_T(x) ∩ U)`**。 -/
theorem degree_induce_eq_card_inter (U : Finset T.V) (x : T.V) (hx : x ∈ U) :
    (T.graph.induce (↑U : Set T.V)).degree ⟨x, hx⟩ =
      (T.graph.neighborFinset x ∩ U).card := by
  classical
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  refine Finset.card_bij (fun (y : ↥(↑U : Set T.V)) _ => (y : T.V)) ?_ ?_ ?_
  · intro a ha
    rw [SimpleGraph.mem_neighborFinset] at ha
    rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
    exact ⟨ha, a.2⟩
  · intro a₁ _ a₂ _ h
    exact Subtype.ext h
  · intro b hb
    rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset] at hb
    exact ⟨⟨b, hb.2⟩, by rw [SimpleGraph.mem_neighborFinset]; exact hb.1, rfl⟩

/-! ## 一般计数引理（`U` 不透明，避免 `sideVertices` 的 `whnf` 开销） -/

/-- ★★ **侧集合含 ≥ 2 个度为 1 的顶点**（一般形式）。

`U` 是被割边 `s(u,v)` 分出来的一侧（`hcross` 编码「只有 `e` 跨越 `U`」），
`hE` 编码 `#E(T[U]) + 1 = |U|`（`T[U]` 是树），`hnd` 说明 `u` 不是叶。 -/
theorem two_le_card_degree_one_of_side
    (U : Finset T.V) {u v : T.V}
    (hE : (T.graph.induce (↑U : Set T.V)).edgeFinset.card + 1 = U.card)
    (huv : T.graph.Adj u v) (hu : u ∈ U) (hv : v ∉ U)
    (hcross : ∀ x ∈ U, ∀ y, T.graph.Adj x y → y ∉ U → s(x, y) = s(u, v))
    (hnd : T.graph.degree u ≠ 1) :
    2 ≤ (U.filter (fun x => T.graph.degree x = 1)).card := by
  classical
  have hnl : ¬ T.IsLeaf u := fun h => hnd ((T.isLeaf_iff_degree_eq_one u).mp h)
  -- ### 1. 非 `u` 顶点的邻居全在 `U` 内
  have hnb : ∀ x ∈ U, x ≠ u → T.graph.neighborSet x ⊆ (↑U : Set T.V) := by
    intro x hx hxu y hy
    by_contra hyn
    have hpair : s(x, y) = s(u, v) := hcross x hx y hy hyn
    have hmem : x ∈ s(u, v) := hpair ▸ (Sym2.mem_iff.mpr (Or.inl rfl) : x ∈ s(x, y))
    rcases Sym2.mem_iff.mp hmem with h | h
    · exact hxu h
    · exact hv (h ▸ hx)
  -- ### 2. `x ≠ u` 时诱导子图的度 = `T` 中的度
  have hdeg : ∀ x (hx : x ∈ U), x ≠ u →
      (T.graph.induce (↑U : Set T.V)).degree ⟨x, hx⟩ = T.graph.degree x := by
    intro x hx hxu
    rw [T.degree_induce_eq_card_inter U x hx]
    have hsub : T.graph.neighborFinset x ⊆ U := fun y hy =>
      hnb x hx hxu ((SimpleGraph.mem_neighborFinset T.graph x y).mp hy)
    rw [Finset.inter_eq_left.mpr hsub, SimpleGraph.card_neighborFinset_eq_degree]
  -- ### 3. `u` 在诱导子图中的度 ≥ 2
  have hNsub : T.graph.neighborFinset u ⊆ insert v U := by
    intro y hy
    rw [SimpleGraph.mem_neighborFinset] at hy
    by_cases hyU : y ∈ U
    · exact Finset.mem_insert.mpr (Or.inr hyU)
    · have hpair : s(u, y) = s(u, v) := hcross u hu y hy hyU
      have hmem : y ∈ s(u, v) := hpair ▸ (Sym2.mem_iff.mpr (Or.inr rfl) : y ∈ s(u, y))
      rcases Sym2.mem_iff.mp hmem with h | h
      · exact absurd h hy.ne'
      · exact Finset.mem_insert.mpr (Or.inl h)
  have hdu : 2 ≤ (T.graph.induce (↑U : Set T.V)).degree ⟨u, hu⟩ := by
    rw [T.degree_induce_eq_card_inter U u hu]
    have hsp := Finset.card_inter_add_card_sdiff (T.graph.neighborFinset u) U
    have hle1 : (T.graph.neighborFinset u \ U).card ≤ 1 := by
      calc (T.graph.neighborFinset u \ U).card ≤ ({v} : Finset T.V).card :=
            Finset.card_le_card (fun y hy => by
              rw [Finset.mem_sdiff] at hy
              rcases Finset.mem_insert.mp (hNsub hy.1) with h | h
              · exact Finset.mem_singleton.mpr h
              · exact absurd h hy.2)
        _ = 1 := Finset.card_singleton v
    have h3 : 3 ≤ T.graph.degree u :=
      T.three_le_degree_of_not_isLeaf (T.two_le_card_of_adj huv) hnl
    have hdegc : T.graph.degree u = (T.graph.neighborFinset u).card :=
      (SimpleGraph.card_neighborFinset_eq_degree T.graph u).symm
    omega
  -- ### 4. 把 `∑ deg_{G'}` 按「度 1 / 度非 1」分块
  set Ls : Finset ↥(↑U : Set T.V) :=
    (Finset.univ : Finset ↥(↑U : Set T.V)).filter (fun x => T.graph.degree (x : T.V) = 1)
    with hLs
  set Is : Finset ↥(↑U : Set T.V) :=
    (Finset.univ : Finset ↥(↑U : Set T.V)).filter (fun x => ¬ T.graph.degree (x : T.V) = 1)
    with hIs
  have huIs : (⟨u, hu⟩ : ↥(↑U : Set T.V)) ∈ Is := by
    rw [hIs, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hnd⟩
  have hsum := SimpleGraph.sum_degrees_eq_twice_card_edges (T.graph.induce (↑U : Set T.V))
  have hsplit : (∑ x ∈ Ls, (T.graph.induce (↑U : Set T.V)).degree x)
      + (∑ x ∈ Is, (T.graph.induce (↑U : Set T.V)).degree x)
      = ∑ x : ↥(↑U : Set T.V), (T.graph.induce (↑U : Set T.V)).degree x := by
    rw [hLs, hIs, Finset.sum_filter_add_sum_filter_not]
  have hLsum : (∑ x ∈ Ls, (T.graph.induce (↑U : Set T.V)).degree x) = Ls.card := by
    have h : ∀ x ∈ Ls, (T.graph.induce (↑U : Set T.V)).degree x = 1 := by
      intro x hx
      rw [hLs, Finset.mem_filter] at hx
      have hxu : (x : T.V) ≠ u := fun h => hnd (h ▸ hx.2)
      rw [hdeg x x.2 hxu]
      exact hx.2
    rw [Finset.sum_congr rfl h]
    simp
  have hIsum : (T.graph.induce (↑U : Set T.V)).degree ⟨u, hu⟩
      + 3 * (Is.erase ⟨u, hu⟩).card
      ≤ ∑ x ∈ Is, (T.graph.induce (↑U : Set T.V)).degree x := by
    have h1 : 3 * (Is.erase ⟨u, hu⟩).card
        ≤ ∑ x ∈ Is.erase ⟨u, hu⟩, (T.graph.induce (↑U : Set T.V)).degree x := by
      rw [mul_comm]
      refine Finset.card_nsmul_le_sum _ _ 3 (fun x hx => ?_)
      rw [Finset.mem_erase, hIs, Finset.mem_filter] at hx
      have hxu : (x : T.V) ≠ u := fun h => hx.1 (Subtype.ext h)
      rw [hdeg x x.2 hxu]
      exact T.three_le_degree_of_not_isLeaf (T.two_le_card_of_adj huv)
        (fun h => hx.2.2 ((T.isLeaf_iff_degree_eq_one (x : T.V)).mp h))
    have h2 := Finset.sum_erase_add Is
      (fun x => (T.graph.induce (↑U : Set T.V)).degree x) huIs
    omega
  -- ### 5. 收尾：把子类型上的计数搬回 `U`
  have hcardLs : (U.filter (fun x => T.graph.degree x = 1)).card = Ls.card := by
    rw [hLs]
    refine (Finset.card_bij (fun (x : ↥(↑U : Set T.V)) _ => (x : T.V)) ?_ ?_ ?_).symm
    · intro a ha
      rw [Finset.mem_filter] at ha ⊢
      exact ⟨a.2, ha.2⟩
    · intro a₁ _ a₂ _ h
      exact Subtype.ext h
    · intro b hb
      rw [Finset.mem_filter] at hb
      exact ⟨⟨b, hb.1⟩,
        by rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, hb.2⟩, rfl⟩
  have hcardIs : (U.filter (fun x => ¬ T.graph.degree x = 1)).card = Is.card := by
    rw [hIs]
    refine (Finset.card_bij (fun (x : ↥(↑U : Set T.V)) _ => (x : T.V)) ?_ ?_ ?_).symm
    · intro a ha
      rw [Finset.mem_filter] at ha ⊢
      exact ⟨a.2, ha.2⟩
    · intro a₁ _ a₂ _ h
      exact Subtype.ext h
    · intro b hb
      rw [Finset.mem_filter] at hb
      exact ⟨⟨b, hb.1⟩,
        by rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, hb.2⟩, rfl⟩
  have hcardU :=
    Finset.card_filter_add_card_filter_not (s := U) (p := fun x => T.graph.degree x = 1)
  have hErase : Is.card = (Is.erase ⟨u, hu⟩).card + 1 :=
    (Finset.card_erase_add_one huIs).symm
  rw [hcardLs]
  omega

/-! ## 主定理 -/

/-- 边的另一端不在本侧。 -/
theorem notMem_sideVertices_of_adj {u v : T.V} (huv : T.graph.Adj u v) :
    v ∉ T.sideVertices s(u, v) u := by
  rw [mem_sideVertices]
  exact fun hr => T.not_reachable_deleteEdges_of_adj huv (reachable_comm.mpr hr)

/-- ★★ **边的侧集合（端点非叶）含 ≥ 2 个叶**（HANDOVER T2）。

`T.sideLeaves s(u,v) u` 是「删去边 `s(u,v)` 后与 `u` 同侧的叶标签集」。
取对侧端点 `u` 是内部顶点（`degree u ≠ 1`，由 `no_degree_two` 等价于 `¬ IsLeaf u`）即可。 -/
theorem two_le_card_sideLeaves {u v : T.V} (huv : T.graph.Adj u v)
    (hnd : T.graph.degree u ≠ 1) :
    2 ≤ (T.sideLeaves s(u, v) u).card := by
  classical
  set U := T.sideVertices s(u, v) u with hU
  have hu : u ∈ U := T.self_mem_sideVertices _ _
  have hv : v ∉ U := T.notMem_sideVertices_of_adj huv
  have hE' : (T.graph.induce (↑(T.sideVertices s(u, v) u) : Set T.V)).edgeFinset.card + 1
      = (T.sideVertices s(u, v) u).card := by
    rw [T.card_edgeFinset_induce_sideVertices, ← Set.toFinset_card]
    congr 1
    ext x
    simp
  have hE : (T.graph.induce (↑U : Set T.V)).edgeFinset.card + 1 = U.card := hE'
  have hcross : ∀ x ∈ U, ∀ y, T.graph.Adj x y → y ∉ U → s(x, y) = s(u, v) :=
    fun x hx y hy hyU => T.eq_edge_of_adj_of_mem_sideVertices_of_notMem hy hx hyU
  have hmain := T.two_le_card_degree_one_of_side U hE huv hu hv hcross hnd
  have hf : U.filter (fun x => T.graph.degree x = 1) = U.filter T.IsLeaf := by
    refine Finset.filter_congr ?_
    intro x _
    exact (T.isLeaf_iff_degree_eq_one x).symm
  rw [hf] at hmain
  have hleaves : T.sideLeaves s(u, v) u
      = Finset.univ.filter (fun x : X => T.leaf x ∈ U) := by
    ext x
    rw [T.mem_sideLeaves]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (mem_sideVertices (e := s(u, v)) (u := u) (w := T.leaf x)).symm
  have hbij : (Finset.univ.filter (fun x : X => T.leaf x ∈ U)).card
      = (U.filter T.IsLeaf).card := by
    refine Finset.card_bij (fun (x : X) _ => T.leaf x) ?_ ?_ ?_
    · intro a ha
      rw [Finset.mem_filter] at ha ⊢
      exact ⟨ha.2, ⟨a, rfl⟩⟩
    · intro a₁ _ a₂ _ h
      exact T.leaf.injective h
    · intro b hb
      rw [Finset.mem_filter] at hb
      obtain ⟨a, ha⟩ := hb.2
      refine ⟨a, ?_, ha⟩
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, ha ▸ hb.1⟩
  rw [hleaves, hbij]
  exact hmain

/-- ★★ **内部边两侧各含 ≥ 2 叶**（HANDOVER T2 的完整形式）。

两端都非叶（`degree ≠ 1`，`no_degree_two` 下等价于「是内部顶点」）的边，其删边后的
两个叶集都至少含 2 个叶 —— 这正是「边 ↔ split」不产生退化 split 的保证。 -/
theorem two_le_card_sideLeaves_both {u v : T.V} (huv : T.graph.Adj u v)
    (hu : T.graph.degree u ≠ 1) (hv : T.graph.degree v ≠ 1) :
    2 ≤ (T.sideLeaves s(u, v) u).card ∧ 2 ≤ (T.sideLeaves s(u, v) v).card := by
  refine ⟨T.two_le_card_sideLeaves huv hu, ?_⟩
  rw [Sym2.eq_swap]
  exact T.two_le_card_sideLeaves huv.symm hv

end Cladogram
