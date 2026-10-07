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

end Cladogram

namespace Split

/-- 由「真子集」构造 split：`A | Aᶜ`（要求 `A` 与 `Aᶜ` 都非空）。

用 `Fin.cases`（而非 `if i = 0`）实现，使 `parts 0` / `parts 1` 都是 **`rfl`**。 -/
noncomputable def ofCompl {α : Type*} [Fintype α] [DecidableEq α] (A : Finset α)
    (hA : A.Nonempty) (hAc : Aᶜ.Nonempty) : Split α where
  parts := Fin.cases A fun _ : Fin 1 => Aᶜ
  pairwise_disjoint := by
    intro i j hij
    rw [Finset.disjoint_left]
    intro x hx hy
    by_cases hi : i = 0
    · subst hi
      by_cases hj : j = 0
      · subst hj
        exact absurd rfl hij
      · have hj1 : j = 1 := by fin_cases j <;> simp_all
        subst hj1
        exact (Finset.mem_compl.mp hy) hx
    · have hi1 : i = 1 := by fin_cases i <;> simp_all
      subst hi1
      by_cases hj : j = 0
      · subst hj
        exact (Finset.mem_compl.mp hx) hy
      · have hj1 : j = 1 := by fin_cases j <;> simp_all
        subst hj1
        exact absurd rfl hij
  union_eq_univ := by
    ext x
    refine ⟨fun _ => Finset.mem_univ _, fun _ => ?_⟩
    rw [Finset.mem_biUnion]
    by_cases h : x ∈ A
    · exact ⟨0, Finset.mem_univ _, h⟩
    · exact ⟨1, Finset.mem_univ _, Finset.mem_compl.mpr h⟩
  nonempty := by
    intro i
    by_cases hi : i = 0
    · subst hi; exact hA
    · have hi1 : i = 1 := by fin_cases i <;> simp_all
      subst hi1; exact hAc

/-- `ofCompl` 的 `sideA` 就是 `A`（定义相等）。 -/
@[simp] theorem ofCompl_sideA {α : Type*} [Fintype α] [DecidableEq α] (A : Finset α)
    (hA : A.Nonempty) (hAc : Aᶜ.Nonempty) : (ofCompl A hA hAc).sideA = A := rfl

/-- `ofCompl` 的 `sideB` 就是 `Aᶜ`（定义相等）。 -/
@[simp] theorem ofCompl_sideB {α : Type*} [Fintype α] [DecidableEq α] (A : Finset α)
    (hA : A.Nonempty) (hAc : Aᶜ.Nonempty) : (ofCompl A hA hAc).sideB = Aᶜ := rfl

/-! ### `Compatible` 在 `swap` 下的行为（T0.1 第 3 步「计数路线」的管道）

「把 `s` 与 `s.swap` 加进相容族」这一步需要这几条：`Compatible` 对两侧的 `swap`
都不变，且 `Compatible s s.swap` 恒成立（因为 `s.sideA ∩ s.swap.sideA = ∅`）。 -/

/-- `s` 与自己的 `swap` **相容**（`s.sideA ∩ s.swap.sideA = s.sideA ∩ s.sideB = ∅`）。

⚠️ 注意 `¬ Compatible s s`（同一侧自己与自己不交是假的）—— 故「两两相容」在
集合语境下要按「互异元素」表述。 -/
theorem compatible_swap_self {α : Type*} [Fintype α] [DecidableEq α] (s : Split α) :
    Compatible s s.swap :=
  Or.inl (by rw [swap_sideA]; exact s.disjoint_sides)

/-- `Compatible` 对**右侧**的 `swap` 不变（四个选言支只是被置换）。 -/
theorem compatible_swap_right {α : Type*} [Fintype α] [DecidableEq α] {s t : Split α} :
    Compatible s t.swap ↔ Compatible s t := by
  simp only [Compatible, swap_sideA, swap_sideB]
  tauto

/-- `Compatible` 对**左侧**的 `swap` 不变。 -/
theorem compatible_swap_left {α : Type*} [Fintype α] [DecidableEq α] {s t : Split α} :
    Compatible s.swap t ↔ Compatible s t :=
  (compatible_comm s.swap t).trans ((compatible_swap_right (s := t) (t := s)).trans
    (compatible_comm t s))

end Split

namespace Cladogram

set_option linter.unusedSectionVars false

variable {X : Type u} [Fintype X] [DecidableEq X]
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

/-! ## T0.1 第 2 步：非退化边被 quartet 见证

`QuartetDecidesTree`（HANDOVER T0.1，`Phylo/Stat/QuartetDecides.lean`）的证明路线第 2 步是
「每条内部边 `e` 的叶侧 `A|B` 由 quartet 见证」。这就是下面两条定理 ——
它们是 **T2 的直接下游**，也是「由 `Q(T) = Q(T')` 恢复 `Σ(T) = Σ(T')`」的起点。 -/

/-- `splitOfEdge` 的 `sideA`（定义相等）。 -/
@[simp] theorem splitOfEdge_sideA (e : Sym2 T.V) (u : T.V)
    (hA : (T.sideLeaves e u).Nonempty) (hB : (Finset.univ \ T.sideLeaves e u).Nonempty) :
    (T.splitOfEdge e u hA hB).sideA = T.sideLeaves e u := rfl

/-- `splitOfEdge` 的 `sideB`（定义相等）。 -/
@[simp] theorem splitOfEdge_sideB (e : Sym2 T.V) (u : T.V)
    (hA : (T.sideLeaves e u).Nonempty) (hB : (Finset.univ \ T.sideLeaves e u).Nonempty) :
    (T.splitOfEdge e u hA hB).sideB = Finset.univ \ T.sideLeaves e u := by
  show (if (1 : Fin 2) = 0 then T.sideLeaves e u else Finset.univ \ T.sideLeaves e u)
    = Finset.univ \ T.sideLeaves e u
  split_ifs with h
  · exact absurd h (by decide)
  · rfl

/-- ★★ **侧集合非退化 ⟹ 被 quartet 见证**。

边 `s(a,b)` 的 `u` 侧与对侧各含 ≥ 2 个叶时，可取互异的 `x, y`（在 `u` 侧）与 `z, w`（在对侧）
使 `T` 展示 quartet `xy|zw`；而且见证它的 split 就是这条边给出的 `splitOfEdge`。 -/
theorem exists_displaysQuartet_of_sideLeaves {a b : T.V} (hab : T.graph.Adj a b) (u : T.V)
    (hA : 2 ≤ (T.sideLeaves s(a, b) u).card)
    (hB : 2 ≤ (Finset.univ \ T.sideLeaves s(a, b) u).card) :
    ∃ x y z w : X, x ≠ y ∧ z ≠ w ∧
      ({x, y} : Finset X) ⊆ T.sideLeaves s(a, b) u ∧
      ({z, w} : Finset X) ⊆ Finset.univ \ T.sideLeaves s(a, b) u ∧
      T.DisplaysQuartet x y z w := by
  classical
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp hA
  obtain ⟨z, hz, w, hw, hzw⟩ := Finset.one_lt_card.mp hB
  have hsubA : ({x, y} : Finset X) ⊆ T.sideLeaves s(a, b) u := fun t ht => by
    rw [Finset.mem_insert, Finset.mem_singleton] at ht
    exact ht.elim (fun h => h ▸ hx) (fun h => h ▸ hy)
  have hsubB : ({z, w} : Finset X) ⊆ Finset.univ \ T.sideLeaves s(a, b) u := fun t ht => by
    rw [Finset.mem_insert, Finset.mem_singleton] at ht
    exact ht.elim (fun h => h ▸ hz) (fun h => h ▸ hw)
  refine ⟨x, y, z, w, hxy, hzw, hsubA, hsubB, ?_⟩
  exact ⟨T.splitOfEdge s(a, b) u ⟨x, hx⟩ ⟨z, hz⟩, ⟨a, b, hab, u, rfl⟩, hsubA, hsubB⟩

/-- ★★ **内部边被 quartet 见证**（**T2 的直接推论**，HANDOVER T0.1 第 2 步）。

两端都非叶的边 `s(a,b)`，存在 4 个互异的叶 `x,y,z,w` 使 `T` 展示 quartet `xy|zw`。 -/
theorem exists_displaysQuartet_of_internalEdge {a b : T.V} (hab : T.graph.Adj a b)
    (hda : T.graph.degree a ≠ 1) (hdb : T.graph.degree b ≠ 1) :
    ∃ x y z w : X, x ≠ y ∧ z ≠ w ∧ T.DisplaysQuartet x y z w := by
  have hb : 2 ≤ (T.sideLeaves s(a, b) b).card := by
    rw [Sym2.eq_swap]
    exact T.two_le_card_sideLeaves hab.symm hdb
  have hcompl : Finset.univ \ T.sideLeaves s(a, b) a = T.sideLeaves s(a, b) b := by
    rw [← Finset.compl_eq_univ_sdiff, ← T.sideLeaves_compl_adj hab]
  obtain ⟨x, y, z, w, hxy, hzw, _, _, hdisp⟩ :=
    T.exists_displaysQuartet_of_sideLeaves hab a (T.two_le_card_sideLeaves hab hda)
      (by rw [hcompl]; exact hb)
  exact ⟨x, y, z, w, hxy, hzw, hdisp⟩

/-! ## T0.1 第 3 步（`Q(T) = Q(T') ⟹ Σ(T) = Σ(T')`）的可证部分

**容易方向（本文件已证）**：`A` 是 `T` 的某条边的一侧 ⟹ 对任意 `a,b ∈ A`、`c,d ∉ A`
皆有 `ab|cd ∈ Q(T)`（见 `displaysQuartet_of_clade`）。

**归约（本文件已证）**：两棵树的 **quartet 系统相同**（`SameQuartetSystem`，用
`DisplaysQuartet` 层表述）⟹ `Σ(T) ∪ Σ(T')` **两两相容**（`compatible_of_sameQuartetSystem`）。
证明只用到 `Split.exists_four_of_incompatible` 与 **`Phylo/Quartet.lean`** 里的
★★ `Cladogram.not_displaysQuartet_swap`
（「一棵树不能在同一个 4-元集上同时展示 `ab|cd` 与 `ac|bd`」）。

⚠️ **`QuartetDecidesTree` 的现有陈述是假的**，见 `Phylo/Stat/QuartetDecides.lean` 的
修正记录与 `HANDOVER.md` §4 T0.1：`DisplaysSplitOn` 允许 **1|3** split 被"展示"，
于是两棵不同的 binary 树可以用同一个常量 `q` 满足全部假设。 -/

/-- ★★ **clade 的必要条件**（T0.1 第 3 步的容易方向）。

若 `A` 恰是树 `T` 某条边的一侧（即 `A = s.sideA`，`s ∈ Σ(T)`），则对任意
`a,b ∈ A` 与 `c,d ∉ A`，`T` 都展示 quartet `ab|cd` —— 而且见证 split 就是 `s` 本身。 -/
theorem displaysQuartet_of_clade {s : Split X} (hs : T.IsSplitOf s)
    {a b c d : X} (ha : a ∈ s.sideA) (hb : b ∈ s.sideA)
    (hc : c ∉ s.sideA) (hd : d ∉ s.sideA) :
    T.DisplaysQuartet a b c d :=
  ⟨s, hs,
    fun x hx => by
      rw [Finset.mem_insert, Finset.mem_singleton] at hx
      exact hx.elim (fun h => h ▸ ha) (fun h => h ▸ hb),
    fun x hx => by
      rw [Finset.mem_insert, Finset.mem_singleton] at hx
      exact hx.elim (fun h => h ▸ Split.mem_sideB_of_not_mem_sideA s hc)
        (fun h => h ▸ Split.mem_sideB_of_not_mem_sideA s hd)⟩

/-- **「两棵树有相同的 quartet 系统」的 `DisplaysQuartet` 层表述**（4 点互异）。

⚠️ 这是**正确的**表述：`Phylo.Stat.QuartetDecides` 里的 `q, q'`（`QuartetChoice`）
版本**不够强**（它允许 1|3 split 被"展示"），见该文件的修正记录。 -/
def SameQuartetSystem (T T' : Cladogram X) : Prop :=
  ∀ a b c d : X, ({a, b, c, d} : Finset X).card = 4 →
    (T.DisplaysQuartet a b c d ↔ T'.DisplaysQuartet a b c d)

/-- ★★ **同一 quartet 系统 ⟹ 两棵树的 split 系统两两相容**（T0.1 第 3 步的归约）。

**这是 `Q(T) = Q(T') ⟹ Σ(T) = Σ(T')` 的关键一步**：一旦两两相容，剩下的就是
「binary 树的 `Σ` 是**极大**相容族」（⟹ `Σ(T') ⊆ Σ(T)`，反之亦然）。

证明：若 `s ∈ Σ(T)`、`t ∈ Σ(T')` 不相容，则 `Split.exists_four_of_incompatible`
给出互异的 `a,b,c,d` 使 `{a,b} ⊆ s.sideA`、`{c,d} ⊆ s.sideB`、
`{a,c} ⊆ t.sideA`、`{b,d} ⊆ t.sideB`；于是 `T` 展示 `ab|cd`，由同一 quartet 系统
`T'` 也展示 `ab|cd`，而 `t` 又让 `T'` 展示 `ac|bd` —— 与 ★★ `not_displaysQuartet_swap`
矛盾。 -/
theorem compatible_of_sameQuartetSystem {T T' : Cladogram X}
    (h : SameQuartetSystem T T') {s t : Split X}
    (hs : T.IsSplitOf s) (ht : T'.IsSplitOf t) : Split.Compatible s t := by
  by_contra hinc
  obtain ⟨a, b, c, d, hab, hcd, hac, hbd, hcard⟩ :=
    Split.exists_four_of_incompatible (s := s) (t := t) hinc
  exact T'.not_displaysQuartet_swap
    ((h a b c d hcard).mp ⟨s, hs, hab, hcd⟩) ⟨t, ht, hac, hbd⟩

/-! ## T0.1 第 3 步（正题）：**clade 刻画**

> `A ⊆ X` 是 `T` 的 **clade**（= 某条边的一侧）**⟺** `A` 满足 **clan 条件**
> （`A` 内任意两点与 `A` 外任意两点构成的 quartet 都被 `T` 展示）。

本文件证出：

* ★★ `isClan_of_isClade` —— 容易方向；
* ★★ `compatible_of_isClan` —— **clan 条件 ⟹ `A|Aᶜ` 与 `T` 的每个 split 相容**（关键一步）；
* ★★ `isClade_iff_isClan` —— **模 `SplitsMaximal T` 的完整刻画**（两个方向都证完）。

⬜ **剩余的唯一输入**：`SplitsMaximal T`（「与全部 split 相容 ⟹ 自身是 split」），
在 `T.IsBinary` 时成立 —— 见下方 `BinarySplitsMaximal` 的 docstring（含证明思路）。 -/

/-- **clan 条件**：`A` 内任意两点与 `A` 外任意两点构成的 quartet 都被 `T` 展示。 -/
def IsClan (A : Finset X) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∉ A, ∀ d ∉ A, T.DisplaysQuartet a b c d

/-- **clade**：`A` 恰是 `T` 某条边的某一侧。 -/
def IsClade (A : Finset X) : Prop :=
  ∃ s : Split X, T.IsSplitOf s ∧ s.sideA = A

/-- ★★ **clade ⟹ clan**（容易方向；本质是 `displaysQuartet_of_clade`）。 -/
theorem isClan_of_isClade {A : Finset X} (h : T.IsClade A) : T.IsClan A := by
  obtain ⟨s, hs, rfl⟩ := h
  exact fun a ha b hb c hc d hd => T.displaysQuartet_of_clade hs ha hb hc hd

/-- ★★ **任意两个 clan 集必相容**（T0.1 第 3 步的文献路线第一步）。

**出处**：Bandelt & Dress 1986, **Prop 2(b) 的证明**（`references/md/BandeltDress1986_ReconstructingShapeOfTree.md`
**706–708 行**），原文：

> *"any two clusters `Y`, `Y'` with respect to `∥` are compatible since `A ∈ Y ∩ Y'`,
> `B ∈ Y ∩ Ȳ'`, `C ∈ Ȳ ∩ Y'`, `D ∈ Ȳ ∩ Ȳ'` would imply `AB∥CD` as well as `AC∥BD`,
> **contradicting antisymmetry**."*

搬到本题：若四个交都非空，取 `A,B,C,D` 分别落在 `Y∩Z`、`Y∩Zᶜ`、`Yᶜ∩Z`、`Yᶜ∩Zᶜ`；
由 `Y` 是 clan 得 `T` 展示 `AB|CD`，由 `Z` 是 clan 得 `T` 展示 `AC|BD`
—— 与**反对称性**（★★ `Cladogram.not_displaysQuartet_swap`）矛盾。
故四个交至少一个为空，这正是 `SidesCompatible` 的四个选言支。 -/
theorem sidesCompatible_of_isClan {Y Z : Finset X} (hY : T.IsClan Y) (hZ : T.IsClan Z) :
    SidesCompatible Y Z := by
  by_contra h
  rw [SidesCompatible, not_or, not_or, not_or] at h
  obtain ⟨hYZ, hZY, hdisj, huniv⟩ := h
  have key : ∀ (A B C D : X), A ∈ Y → B ∈ Y → C ∉ Y → D ∉ Y →
      A ∈ Z → C ∈ Z → B ∉ Z → D ∉ Z → False :=
    fun A B C D hAY hBY hCY hDY hAZ hCZ hBZ hDZ =>
      T.not_displaysQuartet_swap (hY A hAY B hBY C hCY D hDY)
        (hZ A hAZ C hCZ B hBZ D hDZ)
  have hB : ∃ B, B ∈ Y ∧ B ∉ Z := by
    by_contra hcon
    exact hYZ fun x hx => by by_contra hxz; exact hcon ⟨x, hx, hxz⟩
  obtain ⟨B, hBY, hBZ⟩ := hB
  have hC : ∃ C, C ∈ Z ∧ C ∉ Y := by
    by_contra hcon
    exact hZY fun x hx => by by_contra hxy; exact hcon ⟨x, hx, hxy⟩
  obtain ⟨C, hCZ, hCY⟩ := hC
  have hA : ∃ A, A ∈ Y ∧ A ∈ Z := by
    by_contra hcon
    exact hdisj (Finset.disjoint_left.mpr fun x hx hy => hcon ⟨x, hx, hy⟩)
  obtain ⟨A, hAY, hAZ⟩ := hA
  have hD : ∃ D, D ∉ Y ∪ Z := by
    by_contra hcon
    refine huniv (Finset.eq_univ_iff_forall.mpr fun x => ?_)
    by_contra hx
    exact hcon ⟨x, hx⟩
  obtain ⟨D, hD⟩ := hD
  rw [Finset.mem_union, not_or] at hD
  exact key A B C D hAY hBY hCY hD.1 hAZ hCZ hBZ hD.2

/-- **quartet 的两对可互换**：`ab|cd` ⟺ `cd|ab`（Bandelt–Dress 的**对称性**）。

注意见证 split 要**换向**：`ab|cd` 的见证 `s` 换成 `s.swap` 才把 `{c,d}` 放到 `sideA`。 -/
theorem displaysQuartet_comm {a b c d : X} :
    T.DisplaysQuartet a b c d ↔ T.DisplaysQuartet c d a b :=
  ⟨fun ⟨s, hs, hab, hcd⟩ =>
      ⟨s.swap, T.isSplitOf_swap hs, by rwa [Split.swap_sideA], by rwa [Split.swap_sideB]⟩,
   fun ⟨s, hs, hcd, hab⟩ =>
      ⟨s.swap, T.isSplitOf_swap hs, by rwa [Split.swap_sideA], by rwa [Split.swap_sideB]⟩⟩

/-- ★★ **clan 系统对补闭合**：`A` 是 clan ⟹ `Aᶜ` 也是 clan。

**出处**：Bandelt & Dress 1986, Prop 2(b) 的证明（`references/md/BandeltDress1986_ReconstructingShapeOfTree.md`
**704–705 行**）：*"Trivially, for any such cluster `Y` the complement `Ȳ` is also a cluster."*

证明即 `ab|cd ⟺ cd|ab`（上一条 `displaysQuartet_comm`）。 -/
theorem isClan_compl {A : Finset X} (h : T.IsClan A) : T.IsClan (Aᶜ) := by
  intro a ha b hb c hc d hd
  have hcA : c ∈ A := by simpa using hc
  have hdA : d ∈ A := by simpa using hd
  have haA : a ∉ A := by simpa using ha
  have hbA : b ∉ A := by simpa using hb
  exact T.displaysQuartet_comm.mpr (h c hcA d hdA a haA b hbA)

/-- ★★ **clan ⟹ `A|Aᶜ` 与 `T` 的每个 split 相容**（T0.1 第 3 步的关键一步）。

若 `sA := A|Aᶜ` 与某个 `t ∈ Σ(T)` 不相容，`Split.exists_four_of_incompatible` 给出
`a,b ∈ A` 与 `c,d ∉ A` 使 `{a,c} ⊆ t.sideA`、`{b,d} ⊆ t.sideB`，于是
`T` 既展示 `ab|cd`（clan 条件）又展示 `ac|bd`（由 `t`）—— 与
★★ `Cladogram.not_displaysQuartet_swap` 矛盾。 -/
theorem compatible_of_isClan {A : Finset X} (hA : A.Nonempty) (hAc : (Aᶜ).Nonempty)
    (h : T.IsClan A) {t : Split X} (ht : T.IsSplitOf t) :
    Split.Compatible (Split.ofCompl A hA hAc) t := by
  by_contra hinc
  obtain ⟨a, b, c, d, hab, hcd, hac, hbd, _⟩ :=
    Split.exists_four_of_incompatible (s := Split.ofCompl A hA hAc) (t := t) hinc
  have ha : a ∈ A := hab (by simp)
  have hb : b ∈ A := hab (by simp)
  have hc : c ∉ A := fun hc => (Finset.mem_compl.mp (hcd (by simp))) hc
  have hd : d ∉ A := fun hd => (Finset.mem_compl.mp (hcd (by simp))) hd
  exact T.not_displaysQuartet_swap (h a ha b hb c hc d hd) ⟨t, ht, hac, hbd⟩

/-- **split 系统极大**：与 `T` 的**每个** split 都相容的 split，本身就是 `T` 的 split。 -/
def SplitsMaximal : Prop :=
  ∀ s : Split X, (∀ t : Split X, T.IsSplitOf t → Split.Compatible s t) → T.IsSplitOf s

/-- ★★ **clade 刻画**（**模 `SplitsMaximal T`**，两个方向都已证）。

⚠️ `SplitsMaximal T` 本身在 `T.IsBinary` 时成立，但**尚未形式化** ——
见 `BinarySplitsMaximal`。本定理把它隔离成**唯一**的输入。 -/
theorem isClade_iff_isClan (hmax : T.SplitsMaximal) {A : Finset X}
    (hA : A.Nonempty) (hAc : (Aᶜ).Nonempty) :
    T.IsClade A ↔ T.IsClan A := by
  refine ⟨T.isClan_of_isClade, fun h => ?_⟩
  exact ⟨Split.ofCompl A hA hAc, hmax _ (fun t ht => T.compatible_of_isClan hA hAc h ht),
    Split.ofCompl_sideA A hA hAc⟩

end Cladogram

/-- ⬜ **binary 树的 split 系统极大**（**尚未形式化** —— 目标 T0.1 第 3 步的唯一剩余输入）。

**陈述**：`T.IsBinary` ⟹ `T.SplitsMaximal`（即：与 `T` 的每个 split 都相容的 split，
本身就是 `T` 的 split）。

**为什么不是开放问题**：这是「binary 树的 split 系统是极大相容族」的标准事实
（Semple & Steel §3.8 / Buneman；也等价于「binary 树由 `Σ(T)` 唯一决定」）。

**证明思路（已勘定，记此省下轮时间）**：设 `s = A|Aᶜ`（`|A|, |Aᶜ| ≥ 2`；单点情形由
`Cladogram.exists_isSplitOf_singleton` 直接给出）与所有 split 相容，取 `a₀ ∈ A`、`b₀ ∈ Aᶜ`，令

`𝓤 := {T.sideLeaves e u | e 是 `T` 的边, `T.leaf a₀ ∈ ·`, `b₀ ∉ ·`}`
（= 路径 `a₀ → b₀` 上各边的 `a₀` 侧；偏离路径的边两侧同含 `a₀, b₀`，故被排除）。

1. **`𝓤` 嵌套**：`Σ(T)` 两两相容（`pairwiseCompatible`）。两条都「分开 `a₀` 与 `b₀`」的
   相容 split，其 `a₀` 侧之交非空、补侧之交也非空，故四分之一的选言支里只剩两个
   ⟹ 一侧包含另一侧。**不需要路径结构。**
2. **每个 `U ∈ 𝓤` 满足 `A ⊆ U` 或 `U ⊆ A`**：相容性给四个选言支；`a₀ ∈ A ∩ U` 排除
   `A ⊆ Uᶜ`，`b₀ ∈ Aᶜ \ U` 排除 `Aᶜ ⊆ U`（即 `U ⊆ A` 的补）。
3. `{a₀} ∈ 𝓤`（`⊆ A`）与 `X \ {b₀} ∈ 𝓤`（`⊇ A`），故 `𝓤` 中既有含于 `A` 的也有含 `A` 的。
4. 取 `U_* := ` 含于 `A` 的**最大**者、`U* := ` 包含 `A` 的**最小**者（嵌套 ⟹ 良定义）。
   若 `U_* ⊊ U*`，则二者在链中**相邻**，且 `U* \ U_*` 恰是链上「两条相邻边之间那个顶点
   `v`」处分出的叶集。此时 `A` 在 `U* \ U_*` 上取到**真子集**（既非空、又非全部），
   于是 `v` 的**第三条边**（binary ⟹ 除两条路径边外恰有一条）对应的 split 把 `A` 与 `Aᶜ`
   都劈开 ⟹ 与 `s` 不相容 —— 矛盾。
   （退化情形：若 `v` 的第三条边通向**单叶**，则 `U* \ U_*` 是单点，`A` 只能是 `U_*` 或 `U*`，
   与「真子集」矛盾，故此时必有 `U_* = U* = A` ✓。）

⚠️ **技术障碍**：第 4 步需要「`𝓤` 是沿路径的边侧」这一结构（相邻差 = 某顶点的分支叶集），
即需要 `Walk` 上的边编号 —— 这是本轮未做的部分。

---

**路线 B（计数 / 镶嵌族）的完整方案（2026-10-08 第 4 轮推演，**优先试这条**）**

设 `ρ ∈ X`，对每条 split 取**不含 `ρ` 的那一侧**，得 `F := {t.away ρ : t ∈ Σ}`。
由 `laminar_of_sidesCompatible_of_notMem`（`Phylo/Split.lean`，**已在库里**）
知 `F` 是镶嵌族（两两嵌套或相离）。要点：

1. `t ↦ t.away ρ` 至多 2 对 1 ⟹ `|Σ| ≤ 2·|F|`。
2. `F` 含全部单点 `{x} (x ≠ ρ)`（来自平凡 split）。
3. **镶嵌族基数上界（本方案的核心，需新证）**：
   * **(基本)** 镶嵌族 `G` 满足 `Y ∈ G` ⟹ `|G| ≤ 2|Y| - 1`；
   * **(精细)** 镶嵌族 `G` 满足 `Y ∈ G` 且 `∃ y ∈ Y, {y} ∉ G` ⟹ `|G| ≤ 2|Y| - 2`。
   两者可**互归纳**证明（对 `|Y|` 做强归纳）：设 `A₁…A_k` 为 `Y` 的极大真成员
   （两两不交），`G = {Y} ∪ ⋃_i G_i`（`G_i = {A ∈ G : A ⊆ Aᵢ}`，含 `Aᵢ`），
   则 `|G| ≤ 1 + Σ_i (2|Aᵢ| - 1) = 1 + 2Σ|Aᵢ| - k`。记 `m := |Y| - Σ|Aᵢ| ≥ 0`：
   * 基本版：`k = 0` ⟹ `|G| = 1`；`k = 1` ⟹ `A₁ ⊊ Y` 故 `≤ 2|A₁| ≤ 2|Y|-2`；
     `k ≥ 2` ⟹ `1 + 2|Y| - k ≤ 2|Y| - 1` ✓。
   * 精细版：对被 `{y}` 「缺失」的那个 `y` —— 若 `y ∈ Aᵢ` 则该 `i` 用精细版；
     否则 `m ≥ 1`。逐情算得 `2m + k + |J| ≥ 3`（`J` = 用精细版的下标集），
     其中 `m = 0` 时必有 `k ≥ 2`（因 `Aᵢ` 都是**真**成员），故成立 ✓。
4. 于是 `|Σ| ≤ 2|F| ≤ 2(2|X| - 2) = 4|X| - 6`。
5. 而 `T` binary 时 `|Σ(T)| = 2·#E(T) = 2(2|X| - 3) = 4|X| - 6`
   （`Phylo/Algorithm/BinaryCount.lean` 的 `IsBinary.card_edgeFinset`，**已在库**；
   再用 `T.leafFinset.card = Fintype.card X`）。
6. 若 `s ∉ Σ(T)` 且与全部相容，则 `Σ(T) ∪ {s, s.swap}` 两两相容（用
   `Split.compatible_swap_self` / `compatible_swap_left/right`，**本文件已加**）
   且大小 `4|X| - 4 > 4|X| - 6` —— **矛盾** ✓

⇒ 第 3 步（镶嵌族基数上界，两条互归纳）是**唯一**的新工程量。 -/
def BinarySplitsMaximal (X : Type u) [Fintype X] [DecidableEq X] : Prop :=
  ∀ T : Cladogram.{u, v} X, T.IsBinary → T.SplitsMaximal

/-- ★★ **binary 树的 clade 刻画**（模 `BinarySplitsMaximal`；目标 T0.1 第 3 步的最终形式）。

⚠️ `BinarySplitsMaximal` 本身尚未形式化（见其 docstring）；本定理把 T0.1 第 3 步的
**其余部分全部证完**，只剩这一个输入。 -/
theorem Cladogram.isClade_iff_isClan_of_binary {X : Type u} [Fintype X] [DecidableEq X]
    (hb : BinarySplitsMaximal.{u, v} X) {T : Cladogram.{u, v} X} (hT : T.IsBinary)
    {A : Finset X} (hA : A.Nonempty) (hAc : (Aᶜ).Nonempty) :
    T.IsClade A ↔ T.IsClan A :=
  T.isClade_iff_isClan (hb T hT) hA hAc
