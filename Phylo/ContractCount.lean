/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.PhylogramContract

/-!
# `Phylo.ContractCount` —— 零权边计数 `|零权边| = |V| − |零距离类|`

**目标**（W2b 专项）：

```lean
theorem card_zeroEdges_eq_card_sub_card_classes {X : Type*} [Fintype X] [DecidableEq X]
    (T : Phylogram X) :
    (T.graph.edgeFinset.filter (fun e => T.wExt e = 0)).card
      = Fintype.card T.V - Fintype.card (Q T)
```

**含义**：零权边（= 类内边）总数 = 顶点数 − 零距离类数。
等价说法：**每个零距离类诱导的子图是一棵树**，类内边数 = 类大小 − 1，再对类求和。

**路线**（全部器械来自 `Phylo.PhylogramContract` + Mathlib）：

1. `support_subset_class_of_walk_zero`：一条**全零权** walk 的支撑集不离开其起点所在的零距离类
   （逐步用 `dist_eq_zero_iff_wExt_eq_zero_of_adj` + `mk_eq_iff`）；
2. `preconnected_induce_class`：由 `exists_zeroWalk_of_dist_eq_zero` 得到全零权 walk，
   用 `SimpleGraph.Walk.induce` 提升到 `T.graph.induce ↑C`；
3. `isTree_induce_class`：连通（上一步）+ 无环（`IsAcyclic.induce`）⟹ `IsTree`；
4. `classEdgeFinset`（两端都在 `C` 里的全局边）与诱导子图的边集同基数 ——
   Mathlib 的 `SimpleGraph.card_filter_edgeFinset_toFinset_subset`（探针实测：**存在**，
   故无需自造 `Sym2` 双射）；
5. 逐类 `|类内边| = |C| − 1`（`IsTree.card_edgeFinset`）；
6. 零权边集 = 各类内边集的**不交并**（`Finset.card_biUnion`），
   顶点数 = 各类大小之和（`Finset.card_biUnion`），`omega` 收口。

⚠️ 本文件不含任何占位证明或新公理，且**不修改任何既有文件**。
-/

noncomputable section

open Finset
open Classical
open SimpleGraph

attribute [local instance] Classical.propDecidable

universe u v

namespace Phylo

namespace Contract

set_option linter.unusedSectionVars false

variable {X : Type u} (T : Phylogram.{u, v} X)

/-! ## 1. 全零权 walk 不离开零距离类 -/

/-- ★★ **全零权 walk 的支撑集落在起点所在的零距离类里**。

逐步论证：cons 步的中间顶点 `y` 满足 `wExt ⟦x,y⟧ = 0`，
故 `dist x y = 0`（`dist_eq_zero_iff_wExt_eq_zero_of_adj`），
故 `mk x = mk y`，而 `mk x = C`（`x` 在 `C` 里）。 -/
theorem support_subset_class_of_walk_zero {C : Q T} :
    ∀ {a b : T.V} (p : T.graph.Walk a b), a ∈ (C : Finset T.V) →
      (∀ e ∈ p.edges, T.wExt e = 0) → ∀ x ∈ p.support, x ∈ (C : Finset T.V) := by
  intro a b p
  induction p with
  | nil =>
    intro ha _ x hx
    rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at hx
    rwa [hx]
  | cons hadj q ih =>
    intro ha hp x hx
    rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact ha
    · have hstep : ∀ {x y : T.V}, T.graph.Adj x y → T.wExt s(x, y) = 0 →
          x ∈ (C : Finset T.V) → y ∈ (C : Finset T.V) := by
        intro x y hxy hw hx
        have h1 : T.dist x y = 0 := (dist_eq_zero_iff_wExt_eq_zero_of_adj T hxy).mpr hw
        rw [mem_iff_mk_eq] at hx ⊢
        exact ((mk_eq_iff T).mpr h1).symm.trans hx
      refine ih (hstep hadj ?_ ha) ?_ x hx
      · exact hp _ (by rw [SimpleGraph.Walk.edges_cons]; exact List.mem_cons_self ..)
      · intro e he
        exact hp e (by rw [SimpleGraph.Walk.edges_cons]; exact List.mem_cons_of_mem _ he)

/-! ## 2. 零距离类诱导的子图连通 -/

/-- ★★ **零距离类诱导的子图连通**。

`a b ∈ C` ⟹ `dist a.1 b.1 = 0`（`dist_eq_zero_of_mem_same`）
⟹ 全零权 walk ⟹ 由 §1 提升为诱导子图中的 walk。 -/
theorem preconnected_induce_class (C : Q T) :
    (T.graph.induce (↑(C : Finset T.V) : Set T.V)).Preconnected := by
  intro a b
  obtain ⟨p, hp⟩ := exists_zeroWalk_of_dist_eq_zero T (dist_eq_zero_of_mem_same T a.2 b.2)
  refine ⟨(p.induce (↑(C : Finset T.V))
    (support_subset_class_of_walk_zero T p a.2 hp)).copy (Subtype.ext rfl) (Subtype.ext rfl)⟩

/-- ★★ **零距离类诱导的子图是一棵树**（连通 + 无环）。 -/
theorem isTree_induce_class (C : Q T) :
    (T.graph.induce (↑(C : Finset T.V) : Set T.V)).IsTree := by
  refine SimpleGraph.IsTree.mk
    (SimpleGraph.Connected.mk (preconnected_induce_class T C) (nonempty := ?_))
    (T.isTree.isAcyclic.induce _)
  obtain ⟨u, hu⟩ := C.2
  exact ⟨⟨u, by rw [← hu]; exact self_mem_zeroClass T u⟩⟩

/-! ## 3. 类内边集与诱导子图的边集 -/

/-- **零距离类 `C` 内部的边**：`T.graph` 的两端都落在 `C` 里的边。

（用 `Sym2.toFinset ⊆ C` 表述「两端都在 `C` 里」。） -/
abbrev classEdgeFinset (C : Q T) : Finset (Sym2 T.V) :=
  T.graph.edgeFinset.filter (fun e => e.toFinset ⊆ (C : Finset T.V))

/-- ★★ **零距离类内部边数 = 类大小 − 1**（诱导子图是树 ⟹ `#边 + 1 = #顶点`）。 -/
theorem card_classEdgeFinset (C : Q T) :
    (classEdgeFinset T C).card
      = Fintype.card ↥(↑(C : Finset T.V) : Set T.V) - 1 := by
  have h1 : (classEdgeFinset T C).card
      = (T.graph.induce (↑(C : Finset T.V) : Set T.V)).edgeFinset.card :=
    SimpleGraph.card_filter_edgeFinset_toFinset_subset (G := T.graph) (C : Finset T.V)
  have h2 := (isTree_induce_class T C).card_edgeFinset
  omega

/-- 零距离类非空（作为子类型）。 -/
theorem card_class_pos (C : Q T) :
    1 ≤ Fintype.card ↥(↑(C : Finset T.V) : Set T.V) := by
  obtain ⟨u, hu⟩ := C.2
  refine Fintype.card_pos_iff.mpr ⟨⟨u, ?_⟩⟩
  exact Finset.mem_coe.mpr (by rw [← hu]; exact self_mem_zeroClass T u)

/-! ## 4. 零权边集 = 各类内边集的不交并 -/

/-- ★★ **零权边 ⟺ 两端同属一个零距离类**（全局边集上）。

正向：`wExt ⟦u,v⟧ = 0` ⟹ `dist u v = 0` ⟹ `mk u = mk v` ⟹ 两端都在类 `mk u` 里。
反向：两端都在 `C` 里 ⟹ `dist u v = 0` ⟹ `wExt ⟦u,v⟧ = 0`。 -/
theorem biUnion_classEdgeFinset_eq_zero :
    (Finset.univ : Finset (Q T)).biUnion (classEdgeFinset T)
      = T.graph.edgeFinset.filter (fun e => T.wExt e = 0) := by
  classical
  ext e
  rw [Finset.mem_biUnion, Finset.mem_filter]
  constructor
  · rintro ⟨C, -, hsub⟩
    obtain ⟨he, hsub'⟩ := Finset.mem_filter.mp hsub
    refine ⟨he, ?_⟩
    revert he hsub'
    refine Sym2.ind ?_ e
    intro u v he hsub'
    have huv : T.graph.Adj u v :=
      (SimpleGraph.mem_edgeSet T.graph).mp (SimpleGraph.mem_edgeFinset.mp he)
    have hu : u ∈ (C : Finset T.V) := hsub' (by simp [Sym2.toFinset_mk_eq])
    have hv : v ∈ (C : Finset T.V) := hsub' (by simp [Sym2.toFinset_mk_eq])
    exact (dist_eq_zero_iff_wExt_eq_zero_of_adj T huv).mp (dist_eq_zero_of_mem_same T hu hv)
  · rintro ⟨he, hw⟩
    revert he hw
    refine Sym2.ind ?_ e
    intro u v he hw
    have huv : T.graph.Adj u v :=
      (SimpleGraph.mem_edgeSet T.graph).mp (SimpleGraph.mem_edgeFinset.mp he)
    have hd : T.dist u v = 0 := (dist_eq_zero_iff_wExt_eq_zero_of_adj T huv).mpr hw
    refine ⟨mk T u, Finset.mem_univ _, Finset.mem_filter.mpr ⟨he, ?_⟩⟩
    intro x hx
    rw [Sym2.toFinset_mk_eq, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with hx | hx
    · rw [hx, mk_coe, mem_zeroClass]
      exact T.dist_self u
    · rw [hx, mk_coe, mem_zeroClass]
      exact hd

/-- ★★ **不同零距离类的类内边集不交**。 -/
theorem pairwiseDisjoint_classEdgeFinset :
    Set.PairwiseDisjoint ((Finset.univ : Finset (Q T)) : Set (Q T)) (classEdgeFinset T) := by
  intro C _ D _ hCD
  refine Finset.disjoint_left.mpr ?_
  intro e heC heD
  have hC := Finset.mem_filter.mp heC
  have hD := Finset.mem_filter.mp heD
  revert hC hD
  refine Sym2.ind ?_ e
  intro u v hC hD
  have huC : u ∈ (C : Finset T.V) := hC.2 (by simp [Sym2.toFinset_mk_eq])
  have huD : u ∈ (D : Finset T.V) := hD.2 (by simp [Sym2.toFinset_mk_eq])
  exact hCD (((mem_iff_mk_eq T).mp huC).symm.trans ((mem_iff_mk_eq T).mp huD))

/-! ## 5. 顶点数 = 各类大小之和 -/

/-- **`Fintype.card ↥(↑s : Set T.V) = s.card`**（Finset 的子类型基数）。 -/
theorem card_coe_finset (s : Finset T.V) :
    Fintype.card ↥(↑s : Set T.V) = s.card :=
  Fintype.card_coe s

/-- ★★ **顶点数 = 各类大小之和**（零距离类给出 `T.V` 的一个划分）。 -/
theorem card_V_eq_sum_classes :
    Fintype.card T.V = ∑ C : Q T, Fintype.card ↥(↑(C : Finset T.V) : Set T.V) := by
  classical
  have hunion : (Finset.univ : Finset T.V)
      = (Finset.univ : Finset (Q T)).biUnion (fun C => (C : Finset T.V)) := by
    ext v
    rw [Finset.mem_biUnion]
    exact ⟨fun _ => ⟨mk T v, Finset.mem_univ _, self_mem_zeroClass T v⟩,
      fun _ => Finset.mem_univ v⟩
  have hdisj : Set.PairwiseDisjoint ((Finset.univ : Finset (Q T)) : Set (Q T))
      (fun C : Q T => (C : Finset T.V)) := by
    intro C _ D _ hCD
    refine Finset.disjoint_left.mpr ?_
    intro v hvC hvD
    exact hCD (((mem_iff_mk_eq T).mp hvC).symm.trans ((mem_iff_mk_eq T).mp hvD))
  have hcard := Finset.card_biUnion hdisj
  calc Fintype.card T.V
      = (Finset.univ : Finset T.V).card := Finset.card_univ.symm
    _ = ((Finset.univ : Finset (Q T)).biUnion (fun C => (C : Finset T.V))).card := by
          rw [hunion]
    _ = ∑ C : Q T, (C : Finset T.V).card := hcard
    _ = ∑ C : Q T, Fintype.card ↥(↑(C : Finset T.V) : Set T.V) :=
          Finset.sum_congr rfl fun C _ => (card_coe_finset T (C : Finset T.V)).symm

/-- ★★ **逐类求和**：`∑ (|C| − 1) = |V| − |Q|`。 -/
theorem sum_classCards_sub_one :
    (∑ C : Q T, (Fintype.card ↥(↑(C : Finset T.V) : Set T.V) - 1))
      = Fintype.card T.V - Fintype.card (Q T) := by
  classical
  have hmain : (∑ C : Q T, (Fintype.card ↥(↑(C : Finset T.V) : Set T.V) - 1))
      + Fintype.card (Q T) = Fintype.card T.V := by
    calc (∑ C : Q T, (Fintype.card ↥(↑(C : Finset T.V) : Set T.V) - 1))
          + Fintype.card (Q T)
        = (∑ C : Q T, (Fintype.card ↥(↑(C : Finset T.V) : Set T.V) - 1))
          + ∑ _C : Q T, (1 : ℕ) := by simp
      _ = ∑ C : Q T, ((Fintype.card ↥(↑(C : Finset T.V) : Set T.V) - 1) + 1) :=
            (Finset.sum_add_distrib).symm
      _ = ∑ C : Q T, Fintype.card ↥(↑(C : Finset T.V) : Set T.V) :=
            Finset.sum_congr rfl fun C _ => Nat.sub_add_cancel (card_class_pos T C)
      _ = Fintype.card T.V := (card_V_eq_sum_classes T).symm
  omega

/-! ## 6. 主定理 -/

/-- ★★★ **零权边总数 = 顶点数 − 零距离类数**。

（`Q T = Set.range (zeroClass T)` 是零距离类之集；`T.wExt e = 0` 即 `e` 是零权边。） -/
theorem card_zeroEdges_eq_card_sub_card_classes {X : Type*} [Fintype X] [DecidableEq X]
    (T : Phylogram X) :
    (T.graph.edgeFinset.filter (fun e => T.wExt e = 0)).card
      = Fintype.card T.V - Fintype.card (Q T) := by
  classical
  rw [← biUnion_classEdgeFinset_eq_zero T,
    Finset.card_biUnion (pairwiseDisjoint_classEdgeFinset T)]
  have hsum : (∑ C : Q T, (classEdgeFinset T C).card)
      = ∑ C : Q T, (Fintype.card ↥(↑(C : Finset T.V) : Set T.V) - 1) :=
    Finset.sum_congr rfl fun C _ => card_classEdgeFinset T C
  rw [hsum]
  exact sum_classCards_sub_one T

end Contract

end Phylo
