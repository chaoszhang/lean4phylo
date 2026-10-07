/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.PositiveRealization
import Phylo.CherryQuartet
import Phylo.Split
-- ⚠️ §7 的 (A1) 需要「删边后每一侧都含叶」（★★ `Cladogram.sideLeaves_nonempty_of_adj`，
-- `Phylo/InternalEdge.lean:393`）与「跨侧 walk 必过该边端点」（★★ `mem_pair_of_mem_sideVertices`，
-- `Phylo/SplitsMaximal.lean:256`）——`Phylo.Split` 里有 `sideLeaves` 本身，但**没有**这两条。
import Phylo.InternalEdge
import Phylo.SplitsMaximal

/-!
# `Phylo.PhylogramContract` —— 收缩零权边（T0.3 收口的 (A2) 器械）

**目标**（`Phylo/PositiveRealization.lean:20-25` 的原文）：

```lean
theorem exists_realizingPhylogram_pos_of_addConst {X : Type u} [Fintype X] [DecidableEq X]
    (δ : Dissimilarity X) (hfp : δ.FourPoint) (hcard : 4 ≤ Fintype.card X)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ T : Phylogram X, (∀ e : Edge T.toCladogram, 0 < T.w e) ∧
      ∀ x y : X, T.dist (T.leaf x) (T.leaf y) = (δ.addConst ε).val x y
```

本文件铺设 (A2)「收缩零权边」所需的**器械层**：

1. **距离演算**（§1）：任意 walk 的加权长度 ≥ `dist`（★ `dist_le_walkDist`）、
   `walkDist = 0` ⟺ 每条边权为 0、同零距离类的顶点距离不变、
   「边表不过某条边的 walk ⟹ 删边后仍可达」（★ `reachable_deleteEdges_of_edges_notMem`，
   比库内 `reachable_deleteEdges_of_support_notMem` 假设更弱）；
2. **零距离类**（§2）：`zeroClass T u := {v | T.dist u v = 0}`、商顶点类型
   `Q T := Set.range (zeroClass T)`、商映射 `mk T`、以及 `mk T u = mk T v ↔ T.dist u v = 0`；
3. **商图**（§3）：`QG T := SimpleGraph.map (mk T) T.graph`。
   ⚠️ Mathlib 的 `SimpleGraph.map` 收的是**普通函数**（不是嵌入）：
   `#print` 给出 `Adj := Ne ⊓ Relation.Map G.Adj f f`，`loopless` 由 `Ne` 自动保证。
   含邻接刻画 ★★ `QG_adj_iff`、正权边上的同态性 ★★ `QG_adj_of_adj_of_dist_ne_zero`、
   ★★ `edge_eq_of_sameClass`（**树中同一对零距离类之间至多一条边**），
   以及 ★★ `QG_reachable` / `QG_preconnected` / `QG_connected`（连通性，沿 walk 归纳提升）。
   ⚠️ `SimpleGraph.Connected.map` **不可用**：它要全定义的图同态，而 0 权边处 `mk T u = mk T v`、
   `QG` 邻接的 `Ne` 项为假，构不出同态 —— 故连通性必须自己映射 walk（类内 0 权边那一步「停住」即可）。
4. **里程碑 B 的第一批零件**（§4）：度 2 顶点的邻居对（★ `exists_neighbor_pair_of_degree_two`）
   与「两个邻居不相邻」（★ `not_adj_of_adj_adj_of_degree_two`，树无三角形）；
5. **抑制的图手术定义层**（§5）：`walk_deleteEdges_of_edges_notMem`（Walk 版删边提升）、
   `suppressSet` / `SuppV` / `suppressGraph` / `SuppG`、★★ `SuppG_adj_iff`
   （化简成「旧 `T`-邻接 ∨ 新边 `a—b`」）、★ `leaf_ne_of_degree_two`、★★ `suppressLeaf`。

## ⚠️ 一条影响计划的观察（§6 记录）

**抑制步对目标定理可能根本不必要**：若「**没有 0 权边触到标签**」（= `PositiveRealization.lean`
§四的 (A1) 前提），则商图 `QG T` **没有任何度 2 顶点**：
* 单点类 `{u}`：`u` 是标签 ⟹ 其唯一邻边必正（否则 `v ∈ zeroClass u = {u}`）⟹ 度 = 1；
  `u` 是内部点 ⟹ `deg_T u ≥ 3`，且两个邻居若同类会被 ★★ `edge_eq_of_sameClass` 逼成同一条边
  ⟹ 度 = `deg_T u ≥ 3`；
* 多点类 `C`：`|C| ≥ 2` ⟹ `C` 中无标签（标签在 `C` 里就有一条 0 权边触到它）⟹ 每个 `u ∈ C` 都是
  内部点、`deg_T u ≥ 3`；又 `C` 诱导的子图是树（连通：零权路径；无圈：`IsAcyclic.anti`），
  `|C|` 个顶点 ⟹ 至多 `|C| − 1` 条类内边 ⟹ 出边数 `≥ 3|C| − 2(|C|−1) = |C| + 2 ≥ 4`；
  再由 `edge_eq_of_sameClass`，不同出边去往不同类 ⟹ 度 ≥ 4。
⇒ 若先做 (A1)，**里程碑 B 可以整个跳过**（不必造「允许度 2 顶点」的松弛结构，
也不必做「同时抑制所有极大度 2 链」的重构）。

## ✅ 第二批（W2b 续做）已交付的部分

* **§6 里程碑 A 余下之一：`QG` 的树性** —— 走**桥判据**（不依赖 `Phylo/ContractCount.lean` 的计数引理，
  因为本文件不能 `import` 它：`ContractCount` 反过来 `import` 本文件，成环 ✗）：
  ★★ `QG_deleteEdges_reachable_lift`（`QG − e` 的 walk 提升到 `T − e'`）⟹ ★★ `QG_isBridge_of_adj`
  ⟹ ★★ `QG_isAcyclic` ⟹ ★★★ `QG_isTree`（配 ★★ `QG_connected`）。
* **§7 (A1)：零权边不触叶** —— ★★★ `noZeroAtLeaf_of_realizes_addConst`：若 `T` 是某个「四点条件 `δ` 的
  `δ.addConst ε`」的实现树，则每条触到标签的边权严格为正。
  ⚠️ 这里 `hfp` 是**必需**前提：「标签两两距离全正」**不**蕴含 (A1)（反例见 §7 文件头）。
* **§8 (A2) 归约：商 cladogram / 商 phylogram** —— `repr`/`qdist`/`qgWeight`（边权良定义由 ★★ `qdist_eq`）、
  ★★★ `isTree_induce_zeroClass`、★★★ `three_le_card_neighborFinset_of_not_label`（非标签类度 ≥ 3）、
  ★★★ `leaf_iff_degree_one_QG`、★★★ `no_degree_two_QG`、★★★ `quotCladogram`、★★★ `quotPhylogram`
  （边权**严格为正**：★★★ `quotPhylogram_w_pos`），以及 ★★★ **`dist` 记账**
  （★★ `quotPhylogram_walk_lift` + ★★ `quotPhylogram_walk_project` ⟹ ★★★ `quotPhylogram_dist` /
  ★★★ `quotPhylogram_dist_leaf`）。
* **§9 里程碑 C：目标定理** —— ★★★ `exists_pos_realization_of_addConst`（归约）与
  ★★★ `exists_realizingPhylogram_pos_of_addConst`（`PositiveRealization.lean:20-25` 的原文）。

## 诚实边界（**仍未完成 / 与原计划的偏离**）

* **里程碑 B（一次抑制所有极大度 2 链）未做** —— **按 §6 的观察刻意跳过**：既然 §7 的 (A1) 已证，
  §8 的 `no_degree_two_QG` 就直接给出「`QG` 无度 2 顶点」，**抑制器械对目标定理不需要**。
  §4/§5 已交付的度 2 零件（`exists_neighbor_pair_of_degree_two`、`suppressGraph`、`SuppG_adj_iff`、
  `suppressLeaf` 等）仍保留、可编译，但**没有**把它们组装成「一步抑制」的新图。
  若将来需要（例如 (A1) 前提不成立的情形），器械层从这里继续即可。
* 目标定理的 `Phylogram` **顶点宇宙固定为 `.{u, u}`**（与 `Dissimilarity.ExistsRealizingPhylogram`
  的定义一致：`Buneman.lean:563` 用的是 `Phylogram.{u, u} X`），故陈述写作 `∃ T : Phylogram.{u,u} X`。
* `QG` 树性走的是**桥判据**而非计数路线：与 `Phylo/ContractCount.lean:104` 的 `isTree_induce_class`
  同名件已改名（本文件内为 `isTree_induce_zeroClass`），避免 `environment already contains`。
-/

noncomputable section

open Finset
open Classical
open SimpleGraph
open List

attribute [local instance] Classical.propDecidable

universe u v

namespace Phylo

namespace Contract

/-! ## 1. 距离演算 -/

section DistLemmas

variable (T : Phylogram.{u, v} X)

/-- ★ **任意 walk 的加权长度 ≥ 树距离**。

（把 walk 归约成简单路径 `p.toPath`：其边表是 `p` 边表的 sublist，
配边权非负即得。这是 `Phylogram.dist_triangle` 证明里的那一步的**抽出**。） -/
theorem dist_le_walkDist {a b : T.V} (p : T.graph.Walk a b) :
    T.dist a b ≤ T.walkDist p := by
  rw [Phylo.TreeDist.dist_eq_walkDist_of_isPath T _ p.toPath.isPath]
  show ((p.toPath : T.graph.Walk a b).edges.map T.wExt).sum ≤ (p.edges.map T.wExt).sum
  refine List.Sublist.sum_le_sum ?_ ?_
  · have h1 : p.bypass.edges <+ p.edges := by
      rw [SimpleGraph.Walk.edges_eq_map_darts, SimpleGraph.Walk.edges_eq_map_darts]
      exact (SimpleGraph.Walk.darts_bypass_sublist_darts p).map SimpleGraph.Dart.edge
    exact h1.map T.wExt
  · intro x hx
    obtain ⟨e, -, rfl⟩ := List.mem_map.mp hx
    exact Phylo.TreeDist.wExt_nonneg T e

/-- ★★ **`cons` 的 `walkDist` 展开**（本文件自用版；与 `Phylogram.walkDist_cons` 同内容）。 -/
theorem walkDist_cons {a b c : T.V} (h : T.graph.Adj a b) (p : T.graph.Walk b c) :
    T.walkDist (SimpleGraph.Walk.cons h p) = T.wExt s(a, b) + T.walkDist p := by
  simp only [Phylogram.walkDist, SimpleGraph.Walk.edges_cons, List.map_cons, List.sum_cons]

/-- 通用的「非负列表和为 0 ⟺ 每项为 0」。 -/
theorem list_sum_eq_zero_iff_of_nonneg {l : List ℝ} :
    (∀ x ∈ l, 0 ≤ x) → (l.sum = 0 ↔ ∀ x ∈ l, x = 0) := by
  induction l with
  | nil => intro _; simp
  | cons y t ih =>
    intro h
    have hy : 0 ≤ y := h y (List.mem_cons_self ..)
    have ht : ∀ z ∈ t, 0 ≤ z := fun z hz => h z (List.mem_cons_of_mem _ hz)
    rw [List.sum_cons]
    constructor
    · intro h0 x hx
      have ht0 : t.sum = 0 := by
        have hpos : 0 ≤ t.sum := List.sum_nonneg ht
        linarith
      have hy0 : y = 0 := by linarith
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact hy0
      · exact (ih ht).mp ht0 x hx'
    · intro h0
      rw [h0 y (List.mem_cons_self ..),
        (ih ht).mpr (fun z hz => h0 z (List.mem_cons_of_mem _ hz))]
      ring

/-- ★★ **`walkDist = 0` ⟺ 该 walk 的每条边权为 0**。 -/
theorem walkDist_eq_zero_iff {a b : T.V} (p : T.graph.Walk a b) :
    T.walkDist p = 0 ↔ ∀ e ∈ p.edges, T.wExt e = 0 := by
  rw [Phylogram.walkDist]
  constructor
  · intro h0 e he
    refine (list_sum_eq_zero_iff_of_nonneg ?_).mp h0 (T.wExt e) (List.mem_map.mpr ⟨e, he, rfl⟩)
    intro x hx
    obtain ⟨e', -, rfl⟩ := List.mem_map.mp hx
    exact Phylo.TreeDist.wExt_nonneg T e'
  · intro h0
    refine (list_sum_eq_zero_iff_of_nonneg ?_).mpr ?_
    · intro x hx
      obtain ⟨e', -, rfl⟩ := List.mem_map.mp hx
      exact Phylo.TreeDist.wExt_nonneg T e'
    · intro x hx
      obtain ⟨e', he', rfl⟩ := List.mem_map.mp hx
      exact h0 e' he'

/-- ★★ **同零距离类的顶点之间有一条「全零权」walk**。 -/
theorem exists_zeroWalk_of_dist_eq_zero {a b : T.V} (h : T.dist a b = 0) :
    ∃ p : T.graph.Walk a b, ∀ e ∈ p.edges, T.wExt e = 0 :=
  ⟨(T.existsUnique_path a b).choose,
    (walkDist_eq_zero_iff T _).mp
      ((Phylo.TreeDist.dist_eq_walkDist_of_isPath T _ (T.existsUnique_path a b).choose_spec.1).symm.trans h)⟩

/-- ★ **相邻顶点的距离为 0 ⟺ 该边权为 0**。 -/
theorem dist_eq_zero_iff_wExt_eq_zero_of_adj {a b : T.V} (h : T.graph.Adj a b) :
    T.dist a b = 0 ↔ T.wExt s(a, b) = 0 := by
  rw [Phylo.TreeDist.dist_eq_wExt_of_adj T h]

/-- ★★ **`dist` 只依赖零距离类**：`dist u u' = 0`、`dist v v' = 0` ⟹ `dist u v = dist u' v'`。

（三角不等式双向夹逼；`dist_nonneg` 不必要。） -/
theorem dist_eq_of_dist_eq_zero {u u' v v' : T.V} (hu : T.dist u u' = 0)
    (hv : T.dist v v' = 0) : T.dist u v = T.dist u' v' := by
  have h3 : T.dist v' v = 0 := by rw [Phylo.TreeDist.dist_comm T v' v]; exact hv
  have h4 : T.dist u' u = 0 := by rw [Phylo.TreeDist.dist_comm T u' u]; exact hu
  refine le_antisymm ?_ ?_
  · have h1 : T.dist u v ≤ T.dist u u' + T.dist u' v := Phylogram.dist_triangle T u u' v
    have h2 : T.dist u' v ≤ T.dist u' v' + T.dist v' v := Phylogram.dist_triangle T u' v' v
    linarith
  · have h1 : T.dist u' v' ≤ T.dist u' u + T.dist u v' := Phylogram.dist_triangle T u' u v'
    have h2 : T.dist u v' ≤ T.dist u v + T.dist v v' := Phylogram.dist_triangle T u v v'
    linarith

/-- ★ **不走过边 `e` 的 walk ⟹ 删去 `e` 后仍可达**。 -/
theorem reachable_deleteEdges_of_edges_notMem {e : Sym2 T.V} {a b : T.V}
    (p : T.graph.Walk a b) (h : ∀ f ∈ p.edges, f ≠ e) :
    (T.graph.deleteEdges {e}).Reachable a b := by
  induction p with
  | nil => exact Reachable.refl _
  | cons hadj q ih =>
    refine Reachable.trans ?_ (ih ?_)
    · refine (SimpleGraph.deleteEdges_adj.mpr ⟨hadj, ?_⟩).reachable
      rw [Set.mem_singleton_iff]
      intro hmem
      exact h _ (by rw [SimpleGraph.Walk.edges_cons]; exact List.mem_cons_self ..) hmem
    · intro f hf
      exact h f (by rw [SimpleGraph.Walk.edges_cons]; exact List.mem_cons_of_mem _ hf)

end DistLemmas

/-! ## 2. 零距离类与商顶点 -/

section ZeroClass

variable (T : Phylogram.{u, v} X)

/-- **`u` 的零距离类**：与 `u` 距离为 `0` 的全部顶点。 -/
def zeroClass (u : T.V) : Finset T.V :=
  (Finset.univ : Finset T.V).filter (fun w => T.dist u w = 0)

/-- `zeroClass` 的成员判定。 -/
theorem mem_zeroClass {u w : T.V} : w ∈ zeroClass T u ↔ T.dist u w = 0 := by
  simp [zeroClass]

/-- `u` 属于它自己的零距离类。 -/
theorem self_mem_zeroClass (u : T.V) : u ∈ zeroClass T u :=
  (mem_zeroClass T).mpr (T.dist_self u)

/-- 零距离类非空。 -/
theorem zeroClass_nonempty (u : T.V) : (zeroClass T u).Nonempty :=
  ⟨u, self_mem_zeroClass T u⟩

/-- ★★ **零距离类相等 ⟺ 两点距离为 0**。 -/
theorem zeroClass_eq_iff {u w : T.V} : zeroClass T u = zeroClass T w ↔ T.dist u w = 0 := by
  constructor
  · intro h
    have : u ∈ zeroClass T w := h ▸ self_mem_zeroClass T u
    rw [mem_zeroClass] at this
    rwa [Phylo.TreeDist.dist_comm T w u] at this
  · intro h
    ext z
    rw [mem_zeroClass, mem_zeroClass]
    constructor
    · intro hz
      rw [dist_eq_of_dist_eq_zero T (by rw [Phylo.TreeDist.dist_comm T w u]; exact h) (T.dist_self z)]
      exact hz
    · intro hz
      rw [dist_eq_of_dist_eq_zero T h (T.dist_self z)]
      exact hz

/-- **商顶点类型**：零距离类的集合。 -/
abbrev Q : Type _ := Set.range (zeroClass T)

instance : Fintype (Q T) := Set.fintypeRange (zeroClass T)

instance : DecidableEq (Q T) := inferInstance

/-- **商映射**：`u ↦` 它的零距离类。 -/
def mk (u : T.V) : Q T := ⟨zeroClass T u, u, rfl⟩

@[simp] theorem mk_coe (u : T.V) : (mk T u : Finset T.V) = zeroClass T u := rfl

/-- ★★ **`mk` 的核恰是零距离关系**。 -/
theorem mk_eq_iff {u w : T.V} : mk T u = mk T w ↔ T.dist u w = 0 := by
  constructor
  · intro h
    exact (zeroClass_eq_iff T).mp (Subtype.ext_iff.mp h)
  · intro h
    exact Subtype.ext ((zeroClass_eq_iff T).mpr h)

/-- `mk` 相等的判定（`Subtype` 版）。 -/
theorem mk_eq_iff' {u w : T.V} : mk T u = mk T w ↔ (mk T u : Finset T.V) = (mk T w : Finset T.V) :=
  Subtype.ext_iff

/-- ★ **`mk` 满射**。 -/
theorem mk_surjective : Function.Surjective (mk T) := by
  rintro ⟨C, u, rfl⟩
  exact ⟨u, rfl⟩

/-- `mk` 只依赖零距离类。 -/
theorem mk_eq_mk_of_dist_eq_zero {u w : T.V} (h : T.dist u w = 0) : mk T u = mk T w :=
  (mk_eq_iff T).mpr h

/-- ★★ **零距离类就是 `mk` 的纤维**：`u ∈ C ↔ mk T u = C`。 -/
theorem mem_iff_mk_eq {u : T.V} {C : Q T} : u ∈ (C : Finset T.V) ↔ mk T u = C := by
  obtain ⟨w, hw⟩ := C.2
  have h1 : u ∈ (C : Finset T.V) ↔ T.dist w u = 0 := by
    rw [show (C : Finset T.V) = zeroClass T w from hw.symm]
    exact mem_zeroClass T
  have h2 : mk T u = C ↔ T.dist u w = 0 := by
    rw [show C = mk T w from Subtype.ext hw.symm]
    exact mk_eq_iff T
  rw [h1, h2, Phylo.TreeDist.dist_comm T w u]

/-- ★ **同一类的两点距离为 0**。 -/
theorem dist_eq_zero_of_mem_same {u w : T.V} {C : Q T} (hu : u ∈ (C : Finset T.V))
    (hw : w ∈ (C : Finset T.V)) : T.dist u w = 0 := by
  rw [mem_iff_mk_eq] at hu hw
  exact (mk_eq_iff T).mp (hu.trans hw.symm)

/-- 不同类的两点距离**非零**。 -/
theorem dist_ne_zero_of_mk_ne {u w : T.V} (h : mk T u ≠ mk T w) : T.dist u w ≠ 0 :=
  fun hz => h ((mk_eq_iff T).mpr hz)

end ZeroClass

/-! ## 3. 商图 -/

section QuotGraph

variable (T : Phylogram.{u, v} X)

/-- **商图**：`SimpleGraph.map (mk T) T.graph`。

  ⚠️ Mathlib 的 `SimpleGraph.map` 收的是**普通函数**（探针实测：`(V → W) → SimpleGraph V → SimpleGraph W`，
  定义 `Adj := Ne ⊓ Relation.Map G.Adj f f`）——`Quotient.mk` 这类非单射映射可以直接用；
  `loopless` 由 `Ne` 那一项自动保证（「类内 0 权边」不会变成自环）。 -/
abbrev QG : SimpleGraph (Q T) := SimpleGraph.map (mk T) T.graph

/-- ★★ **商图的邻接刻画**。 -/
theorem QG_adj_iff {C D : Q T} :
    (QG T).Adj C D ↔
      C ≠ D ∧ ∃ u v : T.V, T.graph.Adj u v ∧ mk T u = C ∧ mk T v = D := by
  constructor
  · intro h
    obtain ⟨u, v, huv, hu, hv⟩ := h.2
    exact ⟨h.1, u, v, huv, hu, hv⟩
  · rintro ⟨hne, u, v, huv, hu, hv⟩
    exact ⟨hne, u, v, huv, hu, hv⟩

/-- ★★ **正权边的像是商图的边**（`mk` 在「非零距离边」上的同态性）。 -/
theorem QG_adj_of_adj_of_dist_ne_zero {u v : T.V} (h : T.graph.Adj u v)
    (hne : T.dist u v ≠ 0) : (QG T).Adj (mk T u) (mk T v) :=
  ⟨fun hz => hne ((mk_eq_iff T).mp hz), u, v, h, rfl, rfl⟩

/-- ★★ **树中同一对零距离类之间至多一条边**。

（证明走 `inSide`（`Phylo/Split.lean`）：「全零权 walk」永远绕开正权边，
故 `u'` 在 `u` 侧、`v'` 不在 `u` 侧，而 `v'—u'` 是跨割的边 ⟹ 它必须就是 `⟦u,v⟧`。） -/
theorem edge_eq_of_sameClass [Fintype X] [DecidableEq X] {u v u' v' : T.V}
    (hu : T.dist u u' = 0) (hv : T.dist v v' = 0)
    (huv : T.graph.Adj u v) (hu'v' : T.graph.Adj u' v') (hne : T.dist u v ≠ 0) :
    s(u, v) = s(u', v') := by
  have hw : T.wExt s(u, v) ≠ 0 := by
    rw [← Phylo.TreeDist.dist_eq_wExt_of_adj T huv]
    exact hne
  -- 「全零权 walk 绕开正权边 `⟦u,v⟧`」
  have key : ∀ {a b : T.V} (p : T.graph.Walk a b), (∀ e ∈ p.edges, T.wExt e = 0) →
      (T.graph.deleteEdges {s(u, v)}).Reachable a b := by
    intro a b p hp
    refine reachable_deleteEdges_of_edges_notMem T p ?_
    intro f hf hfe
    exact hw (hfe ▸ hp f hf)
  have h1 : T.inSide s(u, v) u u' := by
    obtain ⟨p, hp⟩ := exists_zeroWalk_of_dist_eq_zero T hu
    exact key p hp
  have h2 : ¬ T.inSide s(u, v) u v' := by
    intro hside
    obtain ⟨q, hq⟩ := exists_zeroWalk_of_dist_eq_zero T hv
    exact T.not_reachable_deleteEdges_of_adj huv (hside.trans (key q hq).symm)
  exact (T.eq_of_adj_of_not_inSide (e₁ := s(u, v)) (u₁ := u) hu'v' h1 h2).symm

/-! ### 3.1 `QG` 的连通性

  ⚠️ **不能**用 `SimpleGraph.Connected.map`：它要求一个**全定义**的图同态 `T.graph →g QG T`，
  而在「类内 0 权边」上 `mk T u = mk T v`，`QG` 的邻接含 `Ne` 项、根本造不出邻接。
  改为**沿 walk 归纳**造 `Reachable`：遇到类内 0 权边那一步把 walk **停住**（用可达性的自反/传递）。 -/

/-- ★★ **walk 的商提升（可达性版）**。 -/
theorem QG_reachable {a b : T.V} (p : T.graph.Walk a b) :
    (QG T).Reachable (mk T a) (mk T b) := by
  refine SimpleGraph.Walk.recOn (motive := fun a b _ => (QG T).Reachable (mk T a) (mk T b)) p ?_ ?_
  · exact Reachable.refl _
  · intro u v w h q ih
    by_cases hz : mk T u = mk T v
    · rw [hz]
      exact ih
    · exact (QG_adj_of_adj_of_dist_ne_zero T h (dist_ne_zero_of_mk_ne T hz)).reachable.trans ih

/-- ★★ **`QG` 预连通**。 -/
theorem QG_preconnected : (QG T).Preconnected := by
  intro C D
  obtain ⟨u, rfl⟩ := mk_surjective T C
  obtain ⟨v, rfl⟩ := mk_surjective T D
  obtain ⟨p⟩ := T.isTree.connected.preconnected u v
  exact QG_reachable T p

/-- `Q T` 非空（`T.graph` 是树 ⟹ `T.V` 非空）。 -/
instance : Nonempty (Q T) :=
  T.isTree.connected.nonempty.elim fun v => ⟨mk T v⟩

/-- ★★ **`QG` 连通**。 -/
theorem QG_connected : (QG T).Connected :=
  SimpleGraph.Connected.mk (QG_preconnected T)

end QuotGraph

/-! ## 4. 里程碑 B 的地基：度 2 顶点的两个邻居

  抑制 `v`（`degree v = 2`，邻居 `a, b`）的图手术：删 `v`、把 `v—a`、`v—b` 换成权为
  `w(va) + w(vb)` 的新边 `a—b`。**关键观察**：`a`、`b` 的度不变（各丢一条、各得一条）
  ⇒ 抑制**不会**产生新的度 1／度 2 顶点 ⇒ `leaf_iff_degree_one` 自动保持、迭代必终止。
  下面两条是这块手术的第一批零件。 -/

section DegreeTwo

variable (T : Phylogram.{u, v} X)

/-- ★★ **度 2 顶点的邻居恰有两个**：`a ≠ b`、`a`、`b` 都与 `v` 相邻、且没有别的邻居。 -/
theorem exists_neighbor_pair_of_degree_two {v : T.V} (hv : T.graph.degree v = 2) :
    ∃ a b : T.V, a ≠ b ∧ T.graph.Adj v a ∧ T.graph.Adj v b ∧
      ∀ w : T.V, T.graph.Adj v w → w = a ∨ w = b := by
  have hcard : (T.graph.neighborFinset v).card = 2 := by
    rw [SimpleGraph.card_neighborFinset_eq_degree T.graph v]
    exact hv
  obtain ⟨a, b, hab, hpair⟩ := Finset.card_eq_two.mp hcard
  have ha_mem : a ∈ T.graph.neighborFinset v := by rw [hpair]; simp
  have hb_mem : b ∈ T.graph.neighborFinset v := by rw [hpair]; simp
  refine ⟨a, b, hab, (SimpleGraph.mem_neighborFinset T.graph v a).mp ha_mem,
    (SimpleGraph.mem_neighborFinset T.graph v b).mp hb_mem, ?_⟩
  · intro w hw
    have hmem : w ∈ T.graph.neighborFinset v :=
      (SimpleGraph.mem_neighborFinset T.graph v w).mpr hw
    rw [hpair] at hmem
    simpa using hmem

/-- ★★ **度 2 顶点的两个邻居不相邻**（树无三角形）。

（否则 `a—v—b—a` 是回路；等价地，删去边 `a—b` 后 `a` 仍经 `v` 可达 `b`，
与「树中每条边都是桥」矛盾 —— 白蹭库内 ★★ `Cladogram.not_reachable_deleteEdges_of_adj`。） -/
theorem not_adj_of_adj_adj_of_degree_two [Fintype X] [DecidableEq X] {v a b : T.V}
    (hva : T.graph.Adj v a) (hvb : T.graph.Adj v b) (hab : a ≠ b) : ¬ T.graph.Adj a b := by
  intro hab_adj
  refine T.not_reachable_deleteEdges_of_adj hab_adj ?_
  have hav : T.graph.Adj a v := hva.symm
  refine (SimpleGraph.deleteEdges_adj.mpr ⟨hav, ?_⟩).reachable.trans
    (SimpleGraph.deleteEdges_adj.mpr ⟨hvb, ?_⟩).reachable
  · rw [Set.mem_singleton_iff, Sym2.eq_iff]
    rintro (⟨-, hvab⟩ | ⟨hab', -⟩)
    · exact hvb.ne hvab
    · exact hab hab'
  · rw [Set.mem_singleton_iff, Sym2.eq_iff]
    rintro (⟨hva', -⟩ | ⟨-, hvb'⟩)
    · exact hva.ne hva'
    · exact hab hvb'.symm

end DegreeTwo

/-! ## 5. 抑制度 2 顶点：图手术的定义层

  `suppressGraph T v a b` = 删 `v—a`、`v—b`、加 `a—b`（顶点集仍为 `T.V`，`v` 成为孤立点）；
  `SuppG T v a b` = 它在保留顶点集 `{w | w ≠ v}` 上的**诱导子图**。
  ★★ `SuppG_adj_iff` 把邻接化简成「旧的 `T`-邻接，或新的 `a—b` 边」——
  两个「删掉的边」条件被 `x.1 ≠ v`、`y.1 ≠ v` 自动排除。 -/

section Suppress

variable (T : Phylogram.{u, v} X)

/-- ★ **删边 walk 提升**：边表不过 `s` 的 walk 落在 `G.deleteEdges s` 里（Walk 版，
比 `reachable_deleteEdges_of_edges_notMem` 强：给出 walk 本身）。 -/
def walk_deleteEdges_of_edges_notMem {s : Set (Sym2 T.V)} {a b : T.V} (p : T.graph.Walk a b)
    (h : ∀ f ∈ p.edges, f ∉ s) : (T.graph.deleteEdges s).Walk a b := by
  induction p with
  | nil => exact SimpleGraph.Walk.nil
  | cons hadj q ih =>
    refine SimpleGraph.Walk.cons (SimpleGraph.deleteEdges_adj.mpr ⟨hadj, ?_⟩) (ih ?_)
    · intro hmem
      exact h _ (by rw [SimpleGraph.Walk.edges_cons]; exact List.mem_cons_self ..) hmem
    · intro f hf
      exact h f (by rw [SimpleGraph.Walk.edges_cons]; exact List.mem_cons_of_mem _ hf)

/-- 抑制度 2 顶点 `v` 时的**保留顶点集** `{w | w ≠ v}`。 -/
def suppressSet (v : T.V) : Set T.V := {w | w ≠ v}

/-- 保留顶点类型。 -/
abbrev SuppV (v : T.V) : Type _ := ↥(suppressSet T v)

/-- 删 `v—a`、`v—b`、加 `a—b` 后的中间图（顶点集仍为 `T.V`；`v` 成为孤立点）。 -/
def suppressGraph (v a b : T.V) : SimpleGraph T.V :=
  (T.graph.deleteEdges {s(v, a), s(v, b)}) ⊔ SimpleGraph.fromEdgeSet {s(a, b)}

/-- **抑制后的图**：`suppressGraph` 在 `{w | w ≠ v}` 上的诱导子图。 -/
abbrev SuppG (v a b : T.V) : SimpleGraph (SuppV T v) :=
  (suppressGraph T v a b).induce (suppressSet T v)

/-- `suppressGraph` 的邻接展开（顶点集 `T.V` 上）。 -/
theorem suppressGraph_adj {v a b : T.V} {u w : T.V} :
    (suppressGraph T v a b).Adj u w ↔
      (T.graph.Adj u w ∧ s(u, w) ≠ s(v, a) ∧ s(u, w) ≠ s(v, b)) ∨
        (s(u, w) = s(a, b) ∧ u ≠ w) := by
  rw [suppressGraph, SimpleGraph.sup_adj, SimpleGraph.deleteEdges_adj,
    SimpleGraph.fromEdgeSet_adj]
  constructor
  · rintro (⟨hadj, hmem⟩ | ⟨heq, hne⟩)
    · refine Or.inl ⟨hadj, ?_, ?_⟩ <;>
        · intro h
          exact hmem (by rw [h]; simp)
    · exact Or.inr ⟨heq, hne⟩
  · rintro (⟨hadj, h1, h2⟩ | ⟨heq, hne⟩)
    · refine Or.inl ⟨hadj, ?_⟩
      rw [Set.mem_insert_iff, Set.mem_singleton_iff]
      exact fun h => h.elim h1 h2
    · exact Or.inr ⟨heq, hne⟩

/-- ★★ **抑制后的邻接刻画**（化简版：两个删边条件被 `≠ v` 自动排除）。 -/
theorem SuppG_adj_iff {v a b : T.V} (hab : a ≠ b) {x y : SuppV T v} :
    (SuppG T v a b).Adj x y ↔ T.graph.Adj x.1 y.1 ∨ s(x.1, y.1) = s(a, b) := by
  rw [SuppG, SimpleGraph.induce_adj, suppressGraph_adj]
  have hx : x.1 ≠ v := x.2
  have hy : y.1 ≠ v := y.2
  constructor
  · rintro (⟨h, -, -⟩ | ⟨h, -⟩)
    · exact Or.inl h
    · exact Or.inr h
  · rintro (h | h)
    · refine Or.inl ⟨h, ?_, ?_⟩ <;>
        · intro heq
          rw [Sym2.eq_iff] at heq
          rcases heq with ⟨h1, -⟩ | ⟨-, h2⟩
          · exact hx h1
          · exact hy h2
    · refine Or.inr ⟨h, ?_⟩
      intro hxy
      rw [hxy] at h
      rw [Sym2.eq_iff] at h
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact hab (h1.symm.trans h2)
      · exact hab (h2.symm.trans h1)

/-- 度 2 顶点**不是**标签的像（标签的度是 1）。 -/
theorem leaf_ne_of_degree_two {v : T.V} (hv : T.graph.degree v = 2) (x : X) :
    T.leaf x ≠ v := by
  intro h
  have h1 : T.graph.degree (T.leaf x) = 1 :=
    (T.isLeaf_iff_degree_eq_one (T.leaf x)).mp ⟨x, rfl⟩
  rw [h] at h1
  omega

/-- ★★ **标签嵌入**：标签绝不被抑制（度 1 ≠ 度 2）。 -/
def suppressLeaf (v : T.V) (hv : T.graph.degree v = 2) : X ↪ SuppV T v where
  toFun x := ⟨T.leaf x, leaf_ne_of_degree_two T hv x⟩
  inj' := by
    intro x y h
    exact T.leaf.injective (Subtype.ext_iff.mp h)

@[simp] theorem suppressLeaf_apply (v : T.V) (hv : T.graph.degree v = 2) (x : X) :
    ((suppressLeaf T v hv x : SuppV T v) : T.V) = T.leaf x := rfl

end Suppress

/-! ## 6. `QG` 的树性（里程碑 A 余下：**桥判据路线**）

  ⚠️ 与 `Phylo/ContractCount.lean` 的关系：那份文件 `import Phylo.PhylogramContract`，
  **本文件不能反向 `import` 它**（成环）。故这里**不用**计数引理
  `card_zeroEdges_eq_card_sub_card_classes`，改走**桥判据**：

  * `SimpleGraph.isAcyclic_iff_forall_adj_isBridge`：只需证 `QG` 的每条边都是桥；
  * `SimpleGraph.isBridge_iff`：`IsBridge e ↔ ¬(QG - e).Reachable u v`；
  * 把 `QG - e` 的 walk **提升**到 `T - e'`（`e'` 是对应的正权 `T`-边）——边对应的唯一性由
    ★★ `edge_eq_of_sameClass` 保证，于是与「`T` 的每条边都是桥」矛盾。

  配 ★★ `QG_connected` 即得 ★★ `QG_isTree`（比计数路线少一条引理，且无循环依赖）。 -/

section QuotTree

variable [Fintype X] [DecidableEq X]

variable (T : Phylogram.{u, v} X)

omit [Fintype X] [DecidableEq X] in
/-- ★★ **`QG - e` 的 walk 提升到 `T - e'`**（`e = s(mk u, mk v)`，`e' = s(u,v)` 是 `T` 的**正权**边）。

  沿 walk 归纳：每一步在 `QG` 里走 `C' → C''`，取实现它的 `T`-边 `u'—v'`；
  类内的零权 walk 负责把「当前点」搬到 `u'`，且零权 walk 必不过正权边 `e'`；
  而 `s(u',v') ≠ s(u,v)` 由「`QG - e` 里没有 `e`」这一项 + ★★ `edge_eq_of_sameClass` 得出。 -/
theorem QG_deleteEdges_reachable_lift {u v : T.V} (huv : T.graph.Adj u v)
    (huvne : T.dist u v ≠ 0) :
    ∀ {C' D' : Q T} (_q : ((QG T).deleteEdges {s(mk T u, mk T v)}).Walk C' D') {a b : T.V},
      mk T a = C' → mk T b = D' → (T.graph.deleteEdges {s(u, v)}).Reachable a b := by
  intro C' D' q
  induction q with
  | nil =>
    intro a b ha hb
    have hd : T.dist a b = 0 := (mk_eq_iff T).mp (ha.trans hb.symm)
    obtain ⟨p, hp⟩ := exists_zeroWalk_of_dist_eq_zero T hd
    refine reachable_deleteEdges_of_edges_notMem T p ?_
    intro f hf hfe
    have h0 : T.wExt s(u, v) = 0 := hfe ▸ hp f hf
    rw [← Phylo.TreeDist.dist_eq_wExt_of_adj T huv] at h0
    exact huvne h0
  | cons hadj q' ih =>
    intro a b ha hb
    obtain ⟨hadjQG, hnotmem⟩ := SimpleGraph.deleteEdges_adj.mp hadj
    obtain ⟨-, u', v', hu'v', hmu', hmv'⟩ := (QG_adj_iff T).mp hadjQG
    have hreach1 : (T.graph.deleteEdges {s(u, v)}).Reachable a u' := by
      have hd : T.dist a u' = 0 := (mk_eq_iff T).mp (ha.trans hmu'.symm)
      obtain ⟨p, hp⟩ := exists_zeroWalk_of_dist_eq_zero T hd
      refine reachable_deleteEdges_of_edges_notMem T p ?_
      intro f hf hfe
      have h0 : T.wExt s(u, v) = 0 := hfe ▸ hp f hf
      rw [← Phylo.TreeDist.dist_eq_wExt_of_adj T huv] at h0
      exact huvne h0
    have hne' : s(u', v') ≠ s(u, v) := by
      rw [← hmu', ← hmv'] at hnotmem
      intro heq
      have hmkeq : s(mk T u', mk T v') = s(mk T u, mk T v) := by
        rcases Sym2.eq_iff.mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · rfl
        · exact Sym2.eq_swap
      exact hnotmem (Set.mem_singleton_iff.mpr hmkeq)
    have hadj' : (T.graph.deleteEdges {s(u, v)}).Adj u' v' :=
      SimpleGraph.deleteEdges_adj.mpr ⟨hu'v', by rw [Set.mem_singleton_iff]; exact hne'⟩
    exact hreach1.trans (hadj'.reachable.trans (ih hmv' hb))

/-- ★★ **`QG` 的每条边都是桥**。

  （反证：`QG - e` 里 `C` 到 `D` 可达 ⟹ 提升到 `T - e'` 得 `u` 到 `v` 可达，与
  ★ `Cladogram.not_reachable_deleteEdges_of_adj`（树中每条边都是桥）矛盾。） -/
theorem QG_isBridge_of_adj {C D : Q T} (h : (QG T).Adj C D) : (QG T).IsBridge s(C, D) := by
  rw [SimpleGraph.isBridge_iff]
  intro hreach
  obtain ⟨hCD, u, v, huv, huC, hvD⟩ := (QG_adj_iff T).mp h
  have huvne : T.dist u v ≠ 0 := dist_ne_zero_of_mk_ne T (by rw [huC, hvD]; exact hCD)
  rw [← huC, ← hvD] at hreach
  exact T.not_reachable_deleteEdges_of_adj huv
    (QG_deleteEdges_reachable_lift T huv huvne hreach.some rfl rfl)

/-- ★★ **`QG` 无圈**（每条边都是桥）。 -/
theorem QG_isAcyclic : (QG T).IsAcyclic := by
  rw [SimpleGraph.isAcyclic_iff_forall_adj_isBridge]
  intro C D h
  exact QG_isBridge_of_adj T h

/-- ★★★ **`QG` 是一棵树**（连通 ★★ `QG_connected` + 无圈 ★★ `QG_isAcyclic`）。

  **里程碑 A 余下第一块**（不算计数、无循环依赖）。 -/
theorem QG_isTree : (QG T).IsTree :=
  SimpleGraph.IsTree.mk (QG_connected T) (QG_isAcyclic T)

end QuotTree

/-! ## 7. (A1)：**零权边不触叶**（在「`T` 是 `δ.addConst ε` 的实现树」前提下）

  ⚠️ 关键区分（本项目已 4 次因「自创引理没造反例」白干，这里先造了反例）：
  「标签两两距离全正」（`hpos`）**不**蕴含 (A1)。反例（4 叶 `x,y,z,t`）：
  `x—u(0)`、`y—u(1)`、`u—v(1)`、`v—z(1)`、`v—t(1)`——所有叶间距离为正，
  但零权边 `x—u` 触到标签 `x`。
  该树**不是**任何「四点条件 `δ` 的 `δ_ε`」的实现树：若 `T` 实现 `δ_ε = δ + ε`，则由
  `δ_ε(y,z) = d(y,z) = d(y,x) + d(x,z)`（`d(x,u)=0` 使 `x` 与 `u` 度量同点）得
  `δ(y,z) = δ(y,x) + δ(x,z) + ε > δ(y,x) + δ(x,z)`，与 `δ` 的三角不等式矛盾。

  下面把这条矛盾**形式化**：所需器械全部现成 ——
  ★★ `Cladogram.sideLeaves_nonempty_of_adj_both`（删边后**两侧都含叶**，
  正是「每个分支含一片标签」）、★★ `Cladogram.mem_pair_of_mem_sideVertices`（跨侧 walk 必过该边端点）、
  ★★ `TreeDist.dist_eq_add_of_mem_support`（路径上取点距离可加）、
  ★★ `Phylogram.eq_add_dist_of_ne_of_unique_adj`（叶的唯一邻居给出分解）、
  ★★ `Dissimilarity.triangle`（四点条件 ⟹ 三角不等式）。 -/

section A1

variable {X : Type u} [Fintype X] [DecidableEq X]

/-- **(A1) 的谓词**：每条**触到标签**的边权都严格为正。 -/
def NoZeroAtLeaf (T : Phylogram.{u, v} X) : Prop :=
  ∀ (x : X) {v : T.V}, T.graph.Adj (T.leaf x) v → 0 < T.wExt s(T.leaf x, v)

/-- ★★★ **(A1)：`T` 是某个「四点条件 `δ` 的 `δ.addConst ε`」的实现树 ⟹ 零权边不触叶**。

  （见本节文件头的反例说明：这里 `hfp` 是**必需**前提，不能去掉。） -/
theorem noZeroAtLeaf_of_realizes_addConst (T : Phylogram.{u, v} X) (δ : NJ.Dissimilarity X)
    (hfp : δ.FourPoint) {ε : ℝ} (hε : 0 < ε)
    (hreal : ∀ x y : X, T.dist (T.leaf x) (T.leaf y) = (δ.addConst ε).val x y) :
    NoZeroAtLeaf T := by
  intro x v hxv
  by_cases hv : T.IsLeaf v
  · -- `v` 是叶：此时 `dist (leaf x) v` 由 `addConst_val_pos` 直接为正
    obtain ⟨y, rfl⟩ := hv
    by_cases hyx : y = x
    · subst hyx
      exact absurd hxv (fun h => h.ne rfl)
    · have h1 : T.dist (T.leaf x) (T.leaf y) = T.wExt s(T.leaf x, T.leaf y) :=
        Phylo.TreeDist.dist_eq_wExt_of_adj T hxv
      rw [← h1, hreal x y]
      exact NJ.Dissimilarity.addConst_val_pos δ hfp hε (Ne.symm hyx)
  · -- `v` 是非叶 ⟹ 度 ≥ 3 ⟹ 取两个不同于 `leaf x` 的邻居，两个分支各取一叶 ⟹ 矛盾
    have hdeg1 : T.graph.degree v ≠ 1 := fun h => hv ((T.isLeaf_iff_degree_eq_one v).mpr h)
    have hdeg2 : T.graph.degree v ≠ 2 := T.no_degree_two v
    have hmem : T.leaf x ∈ T.graph.neighborFinset v :=
      (SimpleGraph.mem_neighborFinset T.graph v _).mpr hxv.symm
    have hcard1 : (T.graph.neighborFinset v).card ≠ 1 := by
      intro h
      refine hdeg1 ?_
      rw [← SimpleGraph.card_neighborFinset_eq_degree]
      rw [h]
    have hcard2 : (T.graph.neighborFinset v).card ≠ 2 := by
      intro h
      refine hdeg2 ?_
      rw [← SimpleGraph.card_neighborFinset_eq_degree]
      rw [h]
    have herase : 1 < ((T.graph.neighborFinset v).erase (T.leaf x)).card := by
      rw [Finset.card_erase_of_mem hmem]
      have h0 : 0 < (T.graph.neighborFinset v).card := Finset.card_pos.mpr ⟨_, hmem⟩
      omega
    obtain ⟨w₁, hw₁mem, w₂, hw₂mem, hw₁₂⟩ := Finset.one_lt_card.mp herase
    have hvw₁ : T.graph.Adj v w₁ :=
      (SimpleGraph.mem_neighborFinset T.graph v w₁).mp (Finset.mem_of_mem_erase hw₁mem)
    have hvw₂ : T.graph.Adj v w₂ :=
      (SimpleGraph.mem_neighborFinset T.graph v w₂).mp (Finset.mem_of_mem_erase hw₂mem)
    have hw₁ne : w₁ ≠ T.leaf x := Finset.ne_of_mem_erase hw₁mem
    have hw₂ne : w₂ ≠ T.leaf x := Finset.ne_of_mem_erase hw₂mem
    -- 两个分支各取一片叶（`sideLeaves e u` 收的是「从 `u` 出发在 `T - e` 中可达」的叶）
    obtain ⟨i, hi⟩ := (_root_.Cladogram.sideLeaves_nonempty_of_adj_both T.toCladogram hvw₁).2
    obtain ⟨j, hj⟩ := (_root_.Cladogram.sideLeaves_nonempty_of_adj_both T.toCladogram hvw₂).2
    have hi' : T.inSide s(v, w₁) w₁ (T.leaf i) := (T.mem_sideLeaves_iff_inSide).mp hi
    have hj' : T.inSide s(v, w₂) w₂ (T.leaf j) := (T.mem_sideLeaves_iff_inSide).mp hj
    -- `T.leaf x` 在 `v` 侧
    have hne₁ : s(v, T.leaf x) ≠ s(v, w₁) := by
      intro h
      have hmem' : w₁ ∈ s(v, T.leaf x) := by rw [h]; exact Sym2.mem_iff.mpr (Or.inr rfl)
      rcases Sym2.mem_iff.mp hmem' with h1 | h1
      · exact hvw₁.ne h1.symm
      · exact hw₁ne h1
    have hx₁ : T.inSide s(v, w₁) v (T.leaf x) :=
      (SimpleGraph.deleteEdges_adj.mpr ⟨hxv.symm, by rw [Set.mem_singleton_iff]; exact hne₁⟩).reachable
    have hne₂ : s(v, T.leaf x) ≠ s(v, w₂) := by
      intro h
      have hmem' : w₂ ∈ s(v, T.leaf x) := by rw [h]; exact Sym2.mem_iff.mpr (Or.inr rfl)
      rcases Sym2.mem_iff.mp hmem' with h1 | h1
      · exact hvw₂.ne h1.symm
      · exact hw₂ne h1
    have hx₂ : T.inSide s(v, w₂) v (T.leaf x) :=
      (SimpleGraph.deleteEdges_adj.mpr ⟨hxv.symm, by rw [Set.mem_singleton_iff]; exact hne₂⟩).reachable
    have hw₁₂ne : s(w₂, v) ≠ s(v, w₁) := by
      intro h
      rw [Sym2.eq_swap] at h
      rcases Sym2.eq_iff.mp h with ⟨-, h2⟩ | ⟨h1, h2⟩
      · exact hw₁₂ h2.symm
      · exact hw₁₂ (h1.symm.trans h2.symm)
    -- `w₂` 落在 `s(v,w₁)` 的 `v` 侧
    have hw₂V : w₂ ∈ T.sideVertices s(v, w₁) v := by
      rw [T.mem_sideVertices]
      exact (SimpleGraph.deleteEdges_adj.mpr
        ⟨hvw₂.symm, by rw [Set.mem_singleton_iff]; exact hw₁₂ne⟩).reachable
    -- 三片叶两两不同
    have hix : i ≠ x := fun h => T.not_inSide_both hvw₁ ⟨hx₁, h ▸ hi'⟩
    have hjx : j ≠ x := fun h => T.not_inSide_both hvw₂ ⟨hx₂, h ▸ hj'⟩
    have hjV : T.inSide s(v, w₁) v (T.leaf j) := by
      have h1 : T.leaf j ∈ T.sideVertices s(v, w₁) v :=
        T.sideVertices_adj_subset hvw₁ hvw₂ hw₂V
          ((T.mem_sideVertices (e := s(v, w₂)) (u := w₂) (w := T.leaf j)).mpr
            ((T.inSide_comm _ _ _).mpr hj'))
      exact (T.inSide_comm _ _ _).mp
        ((T.mem_sideVertices (e := s(v, w₁)) (u := v) (w := T.leaf j)).mp h1)
    have hij : i ≠ j := fun h => T.not_inSide_both hvw₁ ⟨hjV, h ▸ hi'⟩
    -- `v` 在 `leaf j → leaf i` 的唯一路径上
    have hp : ((T.existsUnique_path (T.leaf j) (T.leaf i)).choose).IsPath :=
      (T.existsUnique_path (T.leaf j) (T.leaf i)).choose_spec.1
    have hiV : T.leaf i ∈ T.sideVertices s(v, w₁) w₁ :=
      (T.mem_sideVertices (e := s(v, w₁)) (u := w₁) (w := T.leaf i)).mpr
        ((T.inSide_comm _ _ _).mpr hi')
    have hjV' : T.leaf j ∉ T.sideVertices s(v, w₁) w₁ := by
      intro hmem
      refine T.not_inSide_both hvw₁ ⟨hjV, ?_⟩
      exact (T.inSide_comm _ _ _).mp
        ((T.mem_sideVertices (e := s(v, w₁)) (u := w₁) (w := T.leaf j)).mp hmem)
    have hv_path : v ∈ ((T.existsUnique_path (T.leaf j) (T.leaf i)).choose).support :=
      T.mem_pair_of_mem_sideVertices (e := s(v, w₁)) (u := w₁) hiV hjV'
        (T.existsUnique_path (T.leaf j) (T.leaf i)).choose (v := v)
        (Sym2.mem_iff.mpr (Or.inl rfl))
    have hsplit : T.dist (T.leaf j) (T.leaf i) = T.dist (T.leaf j) v + T.dist v (T.leaf i) :=
      Phylo.TreeDist.dist_eq_add_of_mem_support T _ hp hv_path
    -- 反证：左边权为 0
    by_contra hcon
    have hw0 : T.wExt s(T.leaf x, v) = 0 :=
      le_antisymm (not_lt.mp hcon) (Phylo.TreeDist.wExt_nonneg T _)
    -- `x` 与 `v` 度量上同点（`dist (leaf x) v = wExt s(leaf x, v) = 0`），
    -- 于是 `dist (leaf i) (leaf x) = dist v (leaf i)`（两条三角不等式夹逼）
    have hxv0 : T.dist (T.leaf x) v = 0 := by
      rw [Phylo.TreeDist.dist_eq_wExt_of_adj T hxv, hw0]
    have hxi : T.dist (T.leaf i) (T.leaf x) = T.dist v (T.leaf i) := by
      refine le_antisymm ?_ ?_
      · have h := Phylogram.dist_triangle T (T.leaf i) v (T.leaf x)
        rw [Phylo.TreeDist.dist_comm T v (T.leaf x), hxv0, add_zero,
          Phylo.TreeDist.dist_comm T (T.leaf i) v] at h
        exact h
      · have h := Phylogram.dist_triangle T v (T.leaf x) (T.leaf i)
        rw [Phylo.TreeDist.dist_comm T v (T.leaf x), hxv0, zero_add] at h
        rwa [Phylo.TreeDist.dist_comm T (T.leaf x) (T.leaf i)] at h
    have hxj : T.dist (T.leaf x) (T.leaf j) = T.dist v (T.leaf j) := by
      refine le_antisymm ?_ ?_
      · have h := Phylogram.dist_triangle T (T.leaf x) v (T.leaf j)
        rw [hxv0, zero_add] at h
        exact h
      · have h := Phylogram.dist_triangle T v (T.leaf x) (T.leaf j)
        rw [Phylo.TreeDist.dist_comm T v (T.leaf x), hxv0, zero_add] at h
        exact h
    have hijD : T.dist (T.leaf i) (T.leaf j) = T.dist v (T.leaf i) + T.dist v (T.leaf j) := by
      rw [Phylo.TreeDist.dist_comm T (T.leaf i) (T.leaf j), hsplit,
        Phylo.TreeDist.dist_comm T (T.leaf j) v]
      exact add_comm _ _
    -- 度量恒等式 ⟹ 与三角不等式矛盾
    have hmain : T.dist (T.leaf i) (T.leaf j)
        = T.dist (T.leaf i) (T.leaf x) + T.dist (T.leaf x) (T.leaf j) := by
      rw [hijD, hxi, hxj]
    have hδ : (δ.addConst ε).val i j = (δ.addConst ε).val i x + (δ.addConst ε).val x j := by
      rw [← hreal i j, ← hreal i x, ← hreal x j]
      exact hmain
    have htri : δ.val i j ≤ δ.val i x + δ.val x j := by
      have h := NJ.Dissimilarity.triangle δ hfp x i j
      rwa [δ.symm x i] at h
    have hexp : δ.val i j + ε = (δ.val i x + ε) + (δ.val x j + ε) := by
      rw [← NJ.Dissimilarity.addConst_val_ne δ ε hij,
        ← NJ.Dissimilarity.addConst_val_ne δ ε hix,
        ← NJ.Dissimilarity.addConst_val_ne δ ε hjx.symm]
      exact hδ
    linarith

end A1

/-! ## 8. 商 cladogram / phylogram（里程碑 C 的组装件）

  前提两条：
  * ★★ `NoZeroAtLeaf T`（§7，由 `hfp` + `hreal` 给出）：**零权边不触叶**；
  * `hpos : ∀ x ≠ y, 0 < T.dist (leaf x) (leaf y)`（由 ★★ `addConst_val_pos` 给出）：标签两两距离为正。

  有了这两条，**`QG` 直接就是合法的 `Cladogram`**（§6 的 `QG_isTree` + 下面的度分析）：
  * 标签类 `mk (leaf x)` 是**单点类** `{leaf x}`，(A1) 使它的度恰为 `1`；
  * 非标签类的度 **≥ 3**（单点内部点：`deg_T ≥ 3` 且邻居两两不同类；
    `|C| ≥ 2`：`C` 诱导子图是树，取它**两片叶** `a ≠ b`，每个在 `C` 外各有 ≥ 2 个邻居，
    于是边界边 ≥ 4 ⇒ 由 ★★ `edge_eq_of_sameClass` 度 ≥ 4）。
  ⇒ **`QG` 没有度 2 顶点**，于是 §5 的「抑制度 2 顶点」器械对目标定理**不需要**
  （这正是文件头 §6 的观察，现在由 ★★★ `noZeroAtLeaf_of_realizes_addConst` 兑现）。 -/

section QuotCladogram

-- 本段大量使用「无实例参数」的小引理与 `Nontrivial`（`Prop` 类）实例，按 `Phylo/ContractCount.lean:54`
-- 的先例关掉这两条 linter，保证**零 warning**。
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

variable {X : Type u} [Fintype X] [DecidableEq X]

variable (T : Phylogram.{u, v} X)

/-- ★★ **(A1) 的推论：标签所在的零距离类是单点**。

  证明：若 `dist (leaf x) u = 0` 且 `u ≠ leaf x`，则唯一路径非空，其**首边**（触到 `leaf x`）
  的权为 `0`（全零权 walk 的每条边权为 0，★ `walkDist_eq_zero_iff`），与 (A1) 矛盾。 -/
theorem zeroClass_leaf_eq_singleton (hA1 : NoZeroAtLeaf T) (x : X) :
    zeroClass T (T.leaf x) = {T.leaf x} := by
  refine Finset.eq_singleton_iff_unique_mem.mpr ⟨self_mem_zeroClass T _, ?_⟩
  intro u hu
  rw [mem_zeroClass] at hu
  by_contra hne
  obtain ⟨p, hp⟩ := exists_zeroWalk_of_dist_eq_zero T hu
  obtain ⟨v, hxv, p', heq⟩ :=
    SimpleGraph.Walk.exists_eq_cons_of_ne (Ne.symm hne) p
  rw [heq] at hp
  exact absurd (hp _ (by rw [SimpleGraph.Walk.edges_cons]; exact List.mem_cons_self ..))
    (ne_of_gt (hA1 x hxv))

/-- ★★ **标签类的度恰为 1**（唯一邻居是 `leaf x` 的唯一邻居）。 -/
theorem degree_mk_leaf (hA1 : NoZeroAtLeaf T) (x : X) :
    (QG T).degree (mk T (T.leaf x)) = 1 := by
  obtain ⟨v, hxv, huniq⟩ : ∃ v : T.V, T.graph.Adj (T.leaf x) v ∧
      ∀ w : T.V, T.graph.Adj (T.leaf x) w → w = v := by
    obtain ⟨v, hv, huniq⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp
      ((T.isLeaf_iff_degree_eq_one (T.leaf x)).mp ⟨x, rfl⟩)
    exact ⟨v, hv, fun w hw => huniq w hw⟩
  have hC : (mk T (T.leaf x) : Finset T.V) = {T.leaf x} := by
    rw [mk_coe]; exact zeroClass_leaf_eq_singleton T hA1 x
  have hne : T.dist v (T.leaf x) ≠ 0 := by
    rw [Phylo.TreeDist.dist_eq_wExt_of_adj T hxv.symm, Sym2.eq_swap]
    exact ne_of_gt (hA1 x hxv)
  have hsing : (QG T).neighborFinset (mk T (T.leaf x)) = {mk T v} := by
    refine Finset.eq_singleton_iff_unique_mem.mpr ⟨?_, ?_⟩
    · rw [SimpleGraph.mem_neighborFinset]
      exact (QG_adj_of_adj_of_dist_ne_zero T hxv.symm hne).symm
    · intro D hD
      rw [SimpleGraph.mem_neighborFinset] at hD
      obtain ⟨-, u, w, huw, hu, hw⟩ := (QG_adj_iff T).mp hD
      have hu' : u = T.leaf x := by
        have : u ∈ ({T.leaf x} : Finset T.V) := by
          rw [← hC]; exact (mem_iff_mk_eq T).mpr hu
        simpa using this
      have huw' : T.graph.Adj (T.leaf x) w := hu' ▸ huw
      rw [huniq w huw'] at hw
      exact hw.symm
  rw [← SimpleGraph.card_neighborFinset_eq_degree, hsing]
  simp

omit [Fintype X] in
/-- ★★ **叶嵌入单射**（`hpos`：标签两两距离为正）。 -/
theorem mk_leaf_injective (hpos : ∀ x y : X, x ≠ y → 0 < T.dist (T.leaf x) (T.leaf y)) :
    Function.Injective (fun x : X => mk T (T.leaf x)) := by
  intro x y h
  by_contra hxy
  exact absurd ((mk_eq_iff T).mp h) (ne_of_gt (hpos x y hxy))

/-! ### 8.1 非标签类的度 ≥ 3 -/

/-- 从 `C` 出发的一条边给出 `QG` 的一个邻居。 -/
theorem QG_adj_mk_of_adj_notMem {C : Q T} {u w : T.V} (hu : u ∈ (C : Finset T.V))
    (huw : T.graph.Adj u w) (hw : w ∉ (C : Finset T.V)) : (QG T).Adj C (mk T w) := by
  refine (QG_adj_iff T).mpr ⟨?_, u, w, huw, (mem_iff_mk_eq T).mp hu, rfl⟩
  intro h
  exact hw ((mem_iff_mk_eq T).mpr h.symm)

/-- 两条「从 `C` 出发」的边终点同类 ⟹ 两条边相同（★★ `edge_eq_of_sameClass` 的直接推论）。

  这是**度分析的全部依据**：不同边界边给出不同的商邻居。 -/
theorem eq_edge_of_class_eq {C : Q T} {u u' w w' : T.V}
    (hu : u ∈ (C : Finset T.V)) (hu' : u' ∈ (C : Finset T.V))
    (huw : T.graph.Adj u w) (hu'w' : T.graph.Adj u' w')
    (hw : w ∉ (C : Finset T.V)) (_hw' : w' ∉ (C : Finset T.V))
    (h : mk T w = mk T w') : s(u, w) = s(u', w') := by
  have h1 : T.dist u u' = 0 := dist_eq_zero_of_mem_same T hu hu'
  have h2 : T.dist w w' = 0 := (mk_eq_iff T).mp h
  have hne : T.dist u w ≠ 0 := fun hz =>
    hw ((mem_iff_mk_eq T).mpr (((mk_eq_iff T).mpr hz).symm.trans ((mem_iff_mk_eq T).mp hu)))
  exact edge_eq_of_sameClass T h1 h2 huw hu'w' hne

/-- `deg_T v ≠ 1`、`deg_T v ≠ 2`、且 `v` 有邻居 ⟹ 邻居数 ≥ 3。 -/
theorem three_le_card_neighborFinset_of {v : T.V} (h1 : T.graph.degree v ≠ 1)
    (h2 : T.graph.degree v ≠ 2) (hne : (T.graph.neighborFinset v).Nonempty) :
    3 ≤ (T.graph.neighborFinset v).card := by
  have hc1 : (T.graph.neighborFinset v).card ≠ 1 := by
    intro h
    refine h1 ?_
    rw [← SimpleGraph.card_neighborFinset_eq_degree, h]
  have hc2 : (T.graph.neighborFinset v).card ≠ 2 := by
    intro h
    refine h2 ?_
    rw [← SimpleGraph.card_neighborFinset_eq_degree, h]
  have hc0 : 0 < (T.graph.neighborFinset v).card := Finset.card_pos.mpr hne
  omega

/-- 零距离类的一个代表元。 -/
noncomputable def repr (C : Q T) : T.V := C.2.choose

theorem mk_repr (C : Q T) : mk T (repr T C) = C := Subtype.ext C.2.choose_spec

theorem mem_repr (C : Q T) : repr T C ∈ (C : Finset T.V) := (mem_iff_mk_eq T).mpr (mk_repr T C)

/-- ★★ **每个顶点都有邻居**（`X` 非空：`leaf x₀` 度为 1；其余顶点由连通性走一步得到）。 -/
theorem neighborFinset_nonempty [Nonempty X] (v : T.V) :
    (T.graph.neighborFinset v).Nonempty := by
  let x₀ : X := Classical.arbitrary X
  by_cases h : v = T.leaf x₀
  · subst h
    obtain ⟨w, hw, -⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp
      ((T.isLeaf_iff_degree_eq_one (T.leaf x₀)).mp ⟨x₀, rfl⟩)
    exact ⟨w, (SimpleGraph.mem_neighborFinset T.graph _ w).mpr hw⟩
  · obtain ⟨p⟩ := T.isTree.connected v (T.leaf x₀)
    obtain ⟨w, hw, -⟩ := SimpleGraph.Walk.exists_eq_cons_of_ne h p
    exact ⟨w, (SimpleGraph.mem_neighborFinset T.graph v w).mpr hw⟩

/-- ★★ **零距离类诱导的子图是一棵树**（连通：类内两点间唯一路径全程零权 ⟹ 不离开类；
  无圈：子图）。 -/
theorem isTree_induce_zeroClass (C : Q T) :
    (T.graph.induce (↑(C : Finset T.V) : Set T.V)).IsTree := by
  refine SimpleGraph.IsTree.mk
    (SimpleGraph.Connected.mk ?_
      (nonempty := ⟨⟨repr T C, Finset.mem_coe.mpr (mem_repr T C)⟩⟩))
    (T.isTree.isAcyclic.induce _)
  intro a b
  have hd : T.dist a.1 b.1 = 0 := dist_eq_zero_of_mem_same T a.2 b.2
  have hp : ((T.existsUnique_path a.1 b.1).choose).IsPath :=
    (T.existsUnique_path a.1 b.1).choose_spec.1
  have hsub : ∀ u ∈ ((T.existsUnique_path a.1 b.1).choose).support,
      u ∈ (↑(C : Finset T.V) : Set T.V) := by
    intro u hu
    have hsplit := Phylo.TreeDist.dist_eq_add_of_mem_support T _ hp hu
    have h1 : T.dist a.1 u = 0 := by
      linarith [hd, hsplit, Phylo.TreeDist.dist_nonneg T u b.1,
        Phylo.TreeDist.dist_nonneg T a.1 u]
    rw [Finset.mem_coe]
    exact (mem_iff_mk_eq T).mpr
      (((mk_eq_iff T).mpr h1).symm.trans ((mem_iff_mk_eq T).mp a.2))
  exact ⟨(((T.existsUnique_path a.1 b.1).choose).induce (↑(C : Finset T.V)) hsub).copy
    (Subtype.ext rfl) (Subtype.ext rfl)⟩

/-- 非单点类 ⟹ `|C| ≥ 2`。 -/
theorem two_le_card_of_not_singleton {C : Q T}
    (h : ¬ ∃ u : T.V, (C : Finset T.V) = {u}) : 2 ≤ (C : Finset T.V).card := by
  have hpos : 0 < (C : Finset T.V).card := Finset.card_pos.mpr ⟨repr T C, mem_repr T C⟩
  have hne1 : (C : Finset T.V).card ≠ 1 := fun h1 => h ⟨_, (Finset.card_eq_one.mp h1).choose_spec⟩
  omega

/-- 诱导子图上的邻居数 = `T` 中落在 `C` 里的邻居数。 -/
theorem card_neighborFinset_induce (s : Set T.V) (a : ↥s) :
    ((T.graph.induce s).neighborFinset a).card
      = ((T.graph.neighborFinset a.1).filter (fun w => w ∈ s)).card := by
  refine Finset.card_bij (fun (w : ↥s) (_ : w ∈ (T.graph.induce s).neighborFinset a) => (w : T.V))
    ?_ ?_ ?_
  · intro w hw
    rw [Finset.mem_filter]
    exact ⟨(SimpleGraph.mem_neighborFinset T.graph a.1 w).mpr
      ((SimpleGraph.induce_adj).mp ((SimpleGraph.mem_neighborFinset _ a w).mp hw)), w.2⟩
  · intro w₁ _ w₂ _ h
    exact Subtype.ext h
  · intro w hw
    rw [Finset.mem_filter, SimpleGraph.mem_neighborFinset] at hw
    exact ⟨⟨w, hw.2⟩, by
      rw [SimpleGraph.mem_neighborFinset, SimpleGraph.induce_adj]; exact hw.1, rfl⟩

/-- ★★★ **非标签类的度 ≥ 3**（单点情形用「邻居两两不同类」；多点情形用类诱导子树的**两片叶**）。

  ⚠️ 不需要 (A1)：`hC` 已排除「类里有标签」（类里有叶 `u` ⟹ `mk (leaf x) = mk u = C`）。 -/
theorem three_le_card_neighborFinset_of_not_label [Nonempty X] {C : Q T}
    (hC : ∀ x : X, mk T (T.leaf x) ≠ C) :
    3 ≤ ((QG T).neighborFinset C).card := by
  obtain ⟨u, hu⟩ : ∃ u : T.V, u ∈ (C : Finset T.V) := ⟨repr T C, mem_repr T C⟩
  by_cases hsingle : ∃ u : T.V, (C : Finset T.V) = {u}
  · -- 单点类：`C = {u}`，`u` 是内部点，其邻居两两不同类
    obtain ⟨u, hu⟩ := hsingle
    have humem : u ∈ (C : Finset T.V) := by rw [hu]; exact Finset.mem_singleton_self u
    have hnotleaf : ¬ T.IsLeaf u := by
      rintro ⟨y, hy⟩
      exact hC y (by rw [hy]; exact (mem_iff_mk_eq T).mp humem)
    have hdeg : 3 ≤ (T.graph.neighborFinset u).card :=
      three_le_card_neighborFinset_of T (fun h => hnotleaf ((T.isLeaf_iff_degree_eq_one u).mpr h))
        (T.no_degree_two u) (neighborFinset_nonempty T u)
    have hinj : Set.InjOn (fun w : T.V => mk T w) ↑(T.graph.neighborFinset u) := by
      intro w hw w' hw' hmk
      have hwu : T.graph.Adj u w := (SimpleGraph.mem_neighborFinset T.graph u w).mp hw
      have hw'u : T.graph.Adj u w' := (SimpleGraph.mem_neighborFinset T.graph u w').mp hw'
      have hwC : w ∉ (C : Finset T.V) := by
        rw [hu]
        simp only [Finset.mem_singleton]
        exact Ne.symm hwu.ne
      have hw'C : w' ∉ (C : Finset T.V) := by
        rw [hu]
        simp only [Finset.mem_singleton]
        exact Ne.symm hw'u.ne
      have hedge := eq_edge_of_class_eq T humem humem hwu hw'u hwC hw'C hmk
      rcases Sym2.eq_iff.mp hedge with ⟨-, h2⟩ | ⟨h1, -⟩
      · exact h2
      · exact absurd (h1 ▸ humem) hw'C
    have hsub : (T.graph.neighborFinset u).image (fun w => mk T w) ⊆ (QG T).neighborFinset C := by
      intro D hD
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hD
      exact (SimpleGraph.mem_neighborFinset (QG T) C _).mpr
        (QG_adj_mk_of_adj_notMem T humem ((SimpleGraph.mem_neighborFinset T.graph u w).mp hw)
          (by rw [hu]; simp only [Finset.mem_singleton]
              exact Ne.symm ((SimpleGraph.mem_neighborFinset T.graph u w).mp hw).ne))
    calc 3 ≤ (T.graph.neighborFinset u).card := hdeg
      _ = ((T.graph.neighborFinset u).image (fun w => mk T w)).card :=
            (Finset.card_image_of_injOn hinj).symm
      _ ≤ ((QG T).neighborFinset C).card := Finset.card_le_card hsub
  · -- `|C| ≥ 2`：取类诱导子树的两片叶 `a, b`，共得 ≥ 4 条边界边
    have hcard2 : 2 ≤ (C : Finset T.V).card := two_le_card_of_not_singleton T hsingle
    haveI : Nontrivial ↥(↑(C : Finset T.V) : Set T.V) := by
      obtain ⟨u, hu, u', hu', hne⟩ := Finset.one_lt_card.mp (by omega : 1 < (C : Finset T.V).card)
      exact ⟨⟨u, Finset.mem_coe.mpr hu⟩, ⟨u', Finset.mem_coe.mpr hu'⟩,
        fun h => hne (Subtype.ext_iff.mp h)⟩
    obtain ⟨a, b, hab, ha1, hb1⟩ := (isTree_induce_zeroClass T C).exists_ne_and_degree_eq_one
    have hfilter1 : ∀ {d : ↥(↑(C : Finset T.V) : Set T.V)},
        ((T.graph.induce (↑(C : Finset T.V) : Set T.V)).degree d = 1) →
        ((T.graph.neighborFinset d.1).filter
          (fun w => w ∈ (↑(C : Finset T.V) : Set T.V))).card = 1 := by
      intro d hd
      obtain ⟨c, hc, hcuniq⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hd
      refine Finset.card_eq_one.mpr ⟨c.1, ?_⟩
      ext w
      rw [Finset.mem_filter, Finset.mem_singleton, SimpleGraph.mem_neighborFinset]
      constructor
      · rintro ⟨haw, hwC⟩
        have hadj : (T.graph.induce (↑(C : Finset T.V) : Set T.V)).Adj d ⟨w, hwC⟩ :=
          (SimpleGraph.induce_adj).mpr haw
        exact congrArg Subtype.val (hcuniq ⟨w, hwC⟩ hadj)
      · rintro rfl
        exact ⟨(SimpleGraph.induce_adj).mp hc, c.2⟩
    have hdeg3 : ∀ {d : ↥(↑(C : Finset T.V) : Set T.V)},
        ((T.graph.induce (↑(C : Finset T.V) : Set T.V)).degree d = 1) →
        3 ≤ (T.graph.neighborFinset d.1).card := by
      intro d hd
      have hdnotleaf : ¬ T.IsLeaf d.1 := by
        rintro ⟨y, hy⟩
        exact hC y (by rw [hy]; exact (mem_iff_mk_eq T).mp d.2)
      obtain ⟨c, hc, -⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hd
      refine three_le_card_neighborFinset_of T
        (fun h => hdnotleaf ((T.isLeaf_iff_degree_eq_one d.1).mpr h))
        (T.no_degree_two d.1) ⟨c.1, (SimpleGraph.mem_neighborFinset T.graph d.1 c.1).mpr
          ((SimpleGraph.induce_adj).mp hc)⟩
    have hout2 : ∀ {d : ↥(↑(C : Finset T.V) : Set T.V)},
        ((T.graph.induce (↑(C : Finset T.V) : Set T.V)).degree d = 1) →
        2 ≤ ((T.graph.neighborFinset d.1).filter
          (fun w => w ∉ (↑(C : Finset T.V) : Set T.V))).card := by
      intro d hd
      have hsum := Finset.card_filter_add_card_filter_not
        (s := T.graph.neighborFinset d.1) (p := fun w => w ∈ (↑(C : Finset T.V) : Set T.V))
      rw [hfilter1 hd] at hsum
      have := hdeg3 hd
      omega
    -- 两个外侧邻居 + 一个（另一片叶的）外侧邻居
    obtain ⟨w₁, hw₁, w₂, hw₂, hw₁₂⟩ := Finset.one_lt_card.mp
      (show 1 < ((T.graph.neighborFinset a.1).filter
        (fun w => w ∉ (↑(C : Finset T.V) : Set T.V))).card from by
        have := hout2 ha1
        omega)
    have hw₃ex : ((T.graph.neighborFinset b.1).filter
        (fun w => w ∉ (↑(C : Finset T.V) : Set T.V))).Nonempty :=
      Finset.card_pos.mp (by have := hout2 hb1; omega)
    obtain ⟨w₃, hw₃⟩ := hw₃ex
    have haC : a.1 ∈ (C : Finset T.V) := a.2
    have hbC : b.1 ∈ (C : Finset T.V) := b.2
    have haw₁ : T.graph.Adj a.1 w₁ :=
      (SimpleGraph.mem_neighborFinset T.graph a.1 w₁).mp (Finset.mem_filter.mp hw₁).1
    have haw₂ : T.graph.Adj a.1 w₂ :=
      (SimpleGraph.mem_neighborFinset T.graph a.1 w₂).mp (Finset.mem_filter.mp hw₂).1
    have hbw₃ : T.graph.Adj b.1 w₃ :=
      (SimpleGraph.mem_neighborFinset T.graph b.1 w₃).mp (Finset.mem_filter.mp hw₃).1
    have hw₁C : w₁ ∉ (C : Finset T.V) := (Finset.mem_filter.mp hw₁).2
    have hw₂C : w₂ ∉ (C : Finset T.V) := (Finset.mem_filter.mp hw₂).2
    have hw₃C : w₃ ∉ (C : Finset T.V) := (Finset.mem_filter.mp hw₃).2
    have hab' : a.1 ≠ b.1 := fun h => hab (Subtype.ext h)
    have h12 : mk T w₁ ≠ mk T w₂ := by
      intro hmk
      have hedge := eq_edge_of_class_eq T haC haC haw₁ haw₂ hw₁C hw₂C hmk
      rcases Sym2.eq_iff.mp hedge with ⟨-, h2⟩ | ⟨h1, -⟩
      · exact hw₁₂ h2
      · exact absurd (h1 ▸ haC) hw₂C
    have h13 : mk T w₁ ≠ mk T w₃ := by
      intro hmk
      have hedge := eq_edge_of_class_eq T haC hbC haw₁ hbw₃ hw₁C hw₃C hmk
      rcases Sym2.eq_iff.mp hedge with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact hab' h1
      · exact absurd (h1 ▸ haC) hw₃C
    have h23 : mk T w₂ ≠ mk T w₃ := by
      intro hmk
      have hedge := eq_edge_of_class_eq T haC hbC haw₂ hbw₃ hw₂C hw₃C hmk
      rcases Sym2.eq_iff.mp hedge with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact hab' h1
      · exact absurd (h1 ▸ haC) hw₃C
    have hsub : ({mk T w₁, mk T w₂, mk T w₃} : Finset (Q T)) ⊆ (QG T).neighborFinset C := by
      intro D hD
      simp only [Finset.mem_insert, Finset.mem_singleton] at hD
      rcases hD with rfl | rfl | rfl
      · exact (SimpleGraph.mem_neighborFinset (QG T) C _).mpr
          (QG_adj_mk_of_adj_notMem T haC haw₁ hw₁C)
      · exact (SimpleGraph.mem_neighborFinset (QG T) C _).mpr
          (QG_adj_mk_of_adj_notMem T haC haw₂ hw₂C)
      · exact (SimpleGraph.mem_neighborFinset (QG T) C _).mpr
          (QG_adj_mk_of_adj_notMem T hbC hbw₃ hw₃C)
    have hcard3 : ({mk T w₁, mk T w₂, mk T w₃} : Finset (Q T)).card = 3 := by
      simp [h12, h13, h23]
    calc 3 = ({mk T w₁, mk T w₂, mk T w₃} : Finset (Q T)).card := hcard3.symm
      _ ≤ ((QG T).neighborFinset C).card := Finset.card_le_card hsub

/-! ### 8.2 叶 ⟺ 度 1、无度 2 -/

/-- ★★★ **`QG` 上：`C` 是标签类 ⟺ `deg C = 1`**（`Cladogram` 的 `leaf_iff_degree_one` 字段）。 -/
theorem leaf_iff_degree_one_QG [Nonempty X] (hA1 : NoZeroAtLeaf T) (C : Q T) :
    (∃ x : X, mk T (T.leaf x) = C) ↔ (QG T).degree C = 1 := by
  constructor
  · rintro ⟨x, rfl⟩
    exact degree_mk_leaf T hA1 x
  · intro h
    by_contra hcon
    have hcon' : ∀ x : X, mk T (T.leaf x) ≠ C := fun x hx => hcon ⟨x, hx⟩
    have h3 : (3 : ℕ∞) ≤ (QG T).degree C := by
      rw [← SimpleGraph.card_neighborFinset_eq_degree]
      exact_mod_cast three_le_card_neighborFinset_of_not_label T hcon'
    rw [h] at h3
    exact absurd h3 (by norm_num)

/-- ★★★ **`QG` 无度 2 顶点**（`Cladogram` 的 `no_degree_two` 字段）。 -/
theorem no_degree_two_QG [Nonempty X] (hA1 : NoZeroAtLeaf T) (C : Q T) :
    (QG T).degree C ≠ 2 := by
  by_cases hx : ∃ x : X, mk T (T.leaf x) = C
  · rw [(leaf_iff_degree_one_QG T hA1 C).mp hx]
    norm_num
  · have hcon' : ∀ x : X, mk T (T.leaf x) ≠ C := fun x h => hx ⟨x, h⟩
    have h3 : (3 : ℕ∞) ≤ (QG T).degree C := by
      rw [← SimpleGraph.card_neighborFinset_eq_degree]
      exact_mod_cast three_le_card_neighborFinset_of_not_label T hcon'
    intro h2
    rw [h2] at h3
    exact absurd h3 (by norm_num)

/-! ### 8.3 边权：`qdist`（类间距离）与 `qgWeight`（`QG` 的边权） -/

/-- **类间距离**（取两个类的代表元）。 -/
noncomputable def qdist (C D : Q T) : ℝ := T.dist (repr T C) (repr T D)

/-- ★★ **`qdist` 与代表元无关**（★ `dist_eq_of_dist_eq_zero`）。 -/
theorem qdist_eq {u v : T.V} {C D : Q T} (hu : u ∈ (C : Finset T.V))
    (hv : v ∈ (D : Finset T.V)) : qdist T C D = T.dist u v :=
  dist_eq_of_dist_eq_zero T (dist_eq_zero_of_mem_same T (mem_repr T C) hu)
    (dist_eq_zero_of_mem_same T (mem_repr T D) hv)

theorem qdist_comm (C D : Q T) : qdist T C D = qdist T D C := by
  rw [qdist, qdist, Phylo.TreeDist.dist_comm]

theorem qdist_nonneg (C D : Q T) : 0 ≤ qdist T C D := Phylo.TreeDist.dist_nonneg T _ _

/-- **`QG` 的边权**：`Sym2.lift` 把无序对 `s(C,D)` 映到 `qdist C D`（良定义由 ★★ `qdist_eq`）。 -/
noncomputable def qgWeight (e : Sym2 (Q T)) : ℝ :=
  Sym2.lift ⟨fun C D => qdist T C D, fun C D => qdist_comm T C D⟩ e

@[simp] theorem qgWeight_mk (C D : Q T) : qgWeight T s(C, D) = qdist T C D :=
  Sym2.lift_mk _ C D

theorem qgWeight_nonneg (e : Sym2 (Q T)) : 0 ≤ qgWeight T e :=
  Sym2.ind (fun C D => by rw [qgWeight_mk]; exact qdist_nonneg T C D) e

/-- ★★ **`QG` 的每条边权严格为正**（边两端必属不同的零距离类）。 -/
theorem qgWeight_pos {C D : Q T} (h : (QG T).Adj C D) : 0 < qgWeight T s(C, D) := by
  rw [qgWeight_mk]
  obtain ⟨hCD, u, v, huv, huC, hvD⟩ := (QG_adj_iff T).mp h
  rw [qdist_eq T ((mem_iff_mk_eq T).mpr huC) ((mem_iff_mk_eq T).mpr hvD)]
  have hne : T.dist u v ≠ 0 := dist_ne_zero_of_mk_ne T (by rw [huC, hvD]; exact hCD)
  rw [Phylo.TreeDist.dist_eq_wExt_of_adj T huv] at hne ⊢
  exact lt_of_le_of_ne (Phylo.TreeDist.wExt_nonneg T _) (Ne.symm hne)

/-- `qdist` 在 `mk` 下就是 `T.dist`。 -/
theorem qdist_mk (u v : T.V) : qdist T (mk T u) (mk T v) = T.dist u v :=
  qdist_eq T (self_mem_zeroClass T u) (self_mem_zeroClass T v)

/-! ### 8.4 商 cladogram / 商 phylogram -/

/-- ★★★ **商 cladogram**（顶点 = 零距离类，叶 = 标签类，边 = 正权边的像）。

  四个结构字段分别由 §6/§8.2 提供：`QG_isTree`（树性）、`mk_leaf_injective`（叶嵌入）、
  `leaf_iff_degree_one_QG`、`no_degree_two_QG`。 -/
noncomputable def quotCladogram [Nonempty X] (hA1 : NoZeroAtLeaf T)
    (hpos : ∀ x y : X, x ≠ y → 0 < T.dist (T.leaf x) (T.leaf y)) : Cladogram X where
  V := Q T
  fintypeV := inferInstance
  decEqV := inferInstance
  graph := QG T
  decAdj := inferInstance
  isTree := QG_isTree T
  leaf := ⟨fun x => mk T (T.leaf x), mk_leaf_injective T hpos⟩
  leaf_iff_degree_one := leaf_iff_degree_one_QG T hA1
  no_degree_two := no_degree_two_QG T hA1

-- ⚠️ `def` 默认不可归约，实例搜索/`rw` 看不到结构字段（库内先例 `Phylo/InductiveAssembly.lean:217-220`）。
attribute [reducible] quotCladogram

@[simp] theorem quotCladogram_leaf [Nonempty X] (hA1 : NoZeroAtLeaf T)
    (hpos : ∀ x y : X, x ≠ y → 0 < T.dist (T.leaf x) (T.leaf y)) (x : X) :
    (quotCladogram T hA1 hpos).leaf x = mk T (T.leaf x) := rfl

/-- ★★★ **商 phylogram**：边权 = 两个零距离类之间的距离（★★ `qgWeight_pos`：**严格为正**）。 -/
noncomputable def quotPhylogram [Nonempty X] (hA1 : NoZeroAtLeaf T)
    (hpos : ∀ x y : X, x ≠ y → 0 < T.dist (T.leaf x) (T.leaf y)) : Phylogram X where
  toCladogram := quotCladogram T hA1 hpos
  w := fun e => qgWeight T e.1
  w_nonneg := fun e => qgWeight_nonneg T e.1

attribute [reducible] quotPhylogram

/-- ★★ **`quotPhylogram` 的边权严格为正**（目标定理的正性来源）。 -/
theorem quotPhylogram_w_pos [Nonempty X] (hA1 : NoZeroAtLeaf T)
    (hpos : ∀ x y : X, x ≠ y → 0 < T.dist (T.leaf x) (T.leaf y))
    (e : Edge (quotCladogram T hA1 hpos)) : 0 < (quotPhylogram T hA1 hpos).w e := by
  show 0 < qgWeight T e.1
  exact Sym2.ind (fun C D hmem =>
    qgWeight_pos T ((SimpleGraph.mem_edgeSet (QG T)).mp hmem)) e.1 e.2

/-- `quotPhylogram` 在 `QG` 的边上取 `wExt` 就是 `qdist`。 -/
theorem quotPhylogram_wExt [Nonempty X] (hA1 : NoZeroAtLeaf T)
    (hpos : ∀ x y : X, x ≠ y → 0 < T.dist (T.leaf x) (T.leaf y)) {C D : Q T}
    (h : (QG T).Adj C D) : (quotPhylogram T hA1 hpos).wExt s(C, D) = qdist T C D := by
  rw [Phylo.TreeDist.wExt_eq_w _ ((SimpleGraph.mem_edgeSet (QG T)).mpr h)]
  show qgWeight T s(C, D) = qdist T C D
  exact qgWeight_mk T C D

/-! ### 8.5 距离记账（`dist` 沿 `mk` 不变）

  两条走法互逆的引理：
  * `quotPhylogram_walk_lift`：`QG` 的 walk 提升回 `T`（类内零权 walk 补上，权和不变）；
  * `quotPhylogram_walk_project`：`T` 的 walk 投到 `QG`（同类的步**跳过**，权和不变）。
  两者夹逼即得 ★★★ `quotPhylogram_dist`：`dist` 在 `mk` 下不变 —— 目标定理的「叶间距离不变」。 -/

/-- ★★ **`quotPhylogram` 的一条边的 `wExt` 就是对应 `T` 边的 `wExt`**（对类名做改写用的工具）。 -/
theorem quotPhylogram_wExt_eq [Nonempty X] (hA1 : NoZeroAtLeaf T)
    (hpos : ∀ x y : X, x ≠ y → 0 < T.dist (T.leaf x) (T.leaf y)) {Ca Cb : Q T}
    (hadj : (QG T).Adj Ca Cb) {u v : T.V} (huv : T.graph.Adj u v)
    (huC : mk T u = Ca) (hvC : mk T v = Cb) :
    (quotPhylogram T hA1 hpos).wExt s(Ca, Cb) = T.wExt s(u, v) := by
  rw [quotPhylogram_wExt T hA1 hpos hadj, ← huC, ← hvC, qdist_mk,
    Phylo.TreeDist.dist_eq_wExt_of_adj T huv]

/-- ★★ **`QG` 的 walk 提升回 `T`**（权和不变）。 -/
theorem quotPhylogram_walk_lift [Nonempty X] (hA1 : NoZeroAtLeaf T)
    (hpos : ∀ x y : X, x ≠ y → 0 < T.dist (T.leaf x) (T.leaf y)) :
    ∀ {C D : Q T} (q : (QG T).Walk C D) {a b : T.V}, mk T a = C → mk T b = D →
      ∃ p : T.graph.Walk a b, T.walkDist p = (quotPhylogram T hA1 hpos).walkDist q := by
  intro C D q
  induction q with
  | nil =>
    intro a b ha hb
    refine ⟨(T.existsUnique_path a b).choose, ?_⟩
    have h0 : T.walkDist (T.existsUnique_path a b).choose = 0 := by
      rw [← Phylo.TreeDist.dist_eq_walkDist_of_isPath T _ (T.existsUnique_path a b).choose_spec.1]
      exact (mk_eq_iff T).mp (ha.trans hb.symm)
    rw [h0]
    simp [Phylogram.walkDist, SimpleGraph.Walk.edges]
  | cons hadj q' ih =>
    rename_i Ca Cb Cc
    intro a b ha hb
    obtain ⟨-, u, v, huv, huC, hvC'⟩ := (QG_adj_iff T).mp hadj
    obtain ⟨p₁, hp₁⟩ := exists_zeroWalk_of_dist_eq_zero T ((mk_eq_iff T).mp (ha.trans huC.symm))
    have hw₁ : T.walkDist p₁ = 0 := (walkDist_eq_zero_iff T p₁).mpr hp₁
    obtain ⟨p₂, hp₂⟩ := ih hvC' hb
    refine ⟨p₁.append (SimpleGraph.Walk.cons huv p₂), ?_⟩
    have hL : T.walkDist (p₁.append (SimpleGraph.Walk.cons huv p₂))
        = T.wExt s(u, v) + T.walkDist p₂ := by
      rw [Phylo.TreeDist.walkDist_append, walkDist_cons T huv p₂, hw₁, zero_add]
    have hR : (quotPhylogram T hA1 hpos).walkDist (SimpleGraph.Walk.cons hadj q')
        = T.wExt s(u, v) + (quotPhylogram T hA1 hpos).walkDist q' := by
      rw [walkDist_cons (quotPhylogram T hA1 hpos) hadj q',
        quotPhylogram_wExt_eq T hA1 hpos hadj huv huC hvC']
    rw [hL, hR, hp₂]

/-- ★★ **`T` 的 walk 投到 `QG`**（同类的步跳过；权和不变）。 -/
theorem quotPhylogram_walk_project [Nonempty X] (hA1 : NoZeroAtLeaf T)
    (hpos : ∀ x y : X, x ≠ y → 0 < T.dist (T.leaf x) (T.leaf y)) :
    ∀ {a b : T.V} (p : T.graph.Walk a b), ∃ q : (QG T).Walk (mk T a) (mk T b),
      (quotPhylogram T hA1 hpos).walkDist q = T.walkDist p := by
  intro a b p
  refine SimpleGraph.Walk.recOn (motive := fun a b p => ∃ q : (QG T).Walk (mk T a) (mk T b),
    (quotPhylogram T hA1 hpos).walkDist q = T.walkDist p) p ?_ ?_
  · exact ⟨SimpleGraph.Walk.nil, by
      simp [Phylogram.walkDist, SimpleGraph.Walk.edges]⟩
  · intro u v w huv p' ih
    obtain ⟨q', hq'⟩ := ih
    by_cases hz : mk T u = mk T v
    · refine ⟨q'.copy hz.symm rfl, ?_⟩
      have hw : (quotPhylogram T hA1 hpos).walkDist (q'.copy hz.symm rfl)
          = (quotPhylogram T hA1 hpos).walkDist q' := by
        rw [Phylogram.walkDist, Phylogram.walkDist, SimpleGraph.Walk.edges_copy]
      have h0 : T.wExt s(u, v) = 0 := by
        rw [← Phylo.TreeDist.dist_eq_wExt_of_adj T huv]
        exact (mk_eq_iff T).mp hz
      rw [hw, hq', walkDist_cons T huv p', h0, zero_add]
    · have hadj := QG_adj_of_adj_of_dist_ne_zero T huv (dist_ne_zero_of_mk_ne T hz)
      refine ⟨SimpleGraph.Walk.cons hadj q', ?_⟩
      rw [walkDist_cons (quotPhylogram T hA1 hpos) hadj q',
        quotPhylogram_wExt T hA1 hpos hadj, qdist_mk,
        Phylo.TreeDist.dist_eq_wExt_of_adj T huv, walkDist_cons T huv p', hq']

/-- ★★★ **`dist` 沿 `mk` 不变**（里程碑 A 余下第二块：`dist` 记账）。 -/
theorem quotPhylogram_dist [Nonempty X] (hA1 : NoZeroAtLeaf T)
    (hpos : ∀ x y : X, x ≠ y → 0 < T.dist (T.leaf x) (T.leaf y)) (u v : T.V) :
    (quotPhylogram T hA1 hpos).dist (mk T u) (mk T v) = T.dist u v := by
  refine le_antisymm ?_ ?_
  · have hp : (T.existsUnique_path u v).choose.IsPath := (T.existsUnique_path u v).choose_spec.1
    have hd : T.dist u v = T.walkDist (T.existsUnique_path u v).choose :=
      Phylo.TreeDist.dist_eq_walkDist_of_isPath T _ hp
    obtain ⟨q, hq⟩ := quotPhylogram_walk_project T hA1 hpos (T.existsUnique_path u v).choose
    have h1 := dist_le_walkDist (quotPhylogram T hA1 hpos) q
    rw [hq, ← hd] at h1
    exact h1
  · have hq_path : ((quotPhylogram T hA1 hpos).existsUnique_path (mk T u) (mk T v)).choose.IsPath :=
      ((quotPhylogram T hA1 hpos).existsUnique_path (mk T u) (mk T v)).choose_spec.1
    have hd : (quotPhylogram T hA1 hpos).dist (mk T u) (mk T v)
        = (quotPhylogram T hA1 hpos).walkDist
          (((quotPhylogram T hA1 hpos).existsUnique_path (mk T u) (mk T v)).choose) :=
      Phylo.TreeDist.dist_eq_walkDist_of_isPath (quotPhylogram T hA1 hpos) _ hq_path
    obtain ⟨p, hp⟩ := quotPhylogram_walk_lift T hA1 hpos
      ((quotPhylogram T hA1 hpos).existsUnique_path (mk T u) (mk T v)).choose rfl rfl
    have h1 := dist_le_walkDist T p
    rw [hp, ← hd] at h1
    exact h1

/-- ★★★ **叶间距离不变**（目标定理用的最终形式）。 -/
theorem quotPhylogram_dist_leaf [Nonempty X] (hA1 : NoZeroAtLeaf T)
    (hpos : ∀ x y : X, x ≠ y → 0 < T.dist (T.leaf x) (T.leaf y)) (x y : X) :
    (quotPhylogram T hA1 hpos).dist ((quotCladogram T hA1 hpos).leaf x)
      ((quotCladogram T hA1 hpos).leaf y) = T.dist (T.leaf x) (T.leaf y) := by
  rw [quotCladogram_leaf, quotCladogram_leaf]
  exact quotPhylogram_dist T hA1 hpos (T.leaf x) (T.leaf y)

end QuotCladogram

/-! ## 9. 里程碑 C：最终组装

  `exists_realizingPhylogram_addConst`（`Phylo/PositiveRealization.lean`）给出 `δ_ε` 的**无正性保证**的实现树 `T`；
  §8 的归约把它换成 ★★★ `quotPhylogram`，其边权**全正**、叶间距离**不变**，于是目标定理落地。 -/

section FinalAssembly

set_option linter.style.haveILetI false

variable {X : Type u} [Fintype X] [DecidableEq X]

/-- ★★★ **(C) 归约**：实现 `δ.addConst ε` 的任意树 ⟹ 边权全正、叶间距离相同的实现树。 -/
theorem exists_pos_realization_of_addConst [Nonempty X] (δ : NJ.Dissimilarity X)
    (hfp : δ.FourPoint) {ε : ℝ} (hε : 0 < ε) (T : Phylogram.{u, u} X)
    (hreal : ∀ x y : X, T.dist (T.leaf x) (T.leaf y) = (δ.addConst ε).val x y) :
    ∃ T' : Phylogram.{u, u} X, (∀ e : Edge T'.toCladogram, 0 < T'.w e) ∧
      ∀ x y : X, T'.dist (T'.leaf x) (T'.leaf y) = T.dist (T.leaf x) (T.leaf y) := by
  have hA1 : NoZeroAtLeaf T := noZeroAtLeaf_of_realizes_addConst T δ hfp hε hreal
  have hpos : ∀ x y : X, x ≠ y → 0 < T.dist (T.leaf x) (T.leaf y) := fun x y hxy => by
    rw [hreal x y]
    exact NJ.Dissimilarity.addConst_val_pos δ hfp hε hxy
  exact ⟨quotPhylogram T hA1 hpos, fun e => quotPhylogram_w_pos T hA1 hpos e,
    fun x y => quotPhylogram_dist_leaf T hA1 hpos x y⟩

/-- ★★★ **目标定理**（`Phylo/PositiveRealization.lean:20-25` 的原文）：

  `δ` 满足四点条件、`|X| ≥ 4`、`ε > 0` ⟹ `δ + ε` 有**边权全正**的实现 `phylogram`。

  路线：★ `exists_realizingPhylogram_addConst`（给出无正性保证的实现树）
  → ★★★ `exists_pos_realization_of_addConst`（§8 的 (A2) 归约：零距离类商 + 正性 + 距离记账）。 -/
theorem exists_realizingPhylogram_pos_of_addConst (δ : NJ.Dissimilarity X) (hfp : δ.FourPoint)
    (hcard : 4 ≤ Fintype.card X) {ε : ℝ} (hε : 0 < ε) :
    ∃ T : Phylogram.{u, u} X, (∀ e : Edge T.toCladogram, 0 < T.w e) ∧
      ∀ x y : X, T.dist (T.leaf x) (T.leaf y) = (δ.addConst ε).val x y := by
  haveI : Nonempty X := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨T, hT⟩ := NJ.Dissimilarity.exists_realizingPhylogram_addConst δ hfp hcard hε
  obtain ⟨T', hpos', hdist'⟩ := exists_pos_realization_of_addConst δ hfp hε T hT
  exact ⟨T', hpos', fun x y => (hdist' x y).trans (hT x y)⟩

end FinalAssembly

end Contract

end Phylo