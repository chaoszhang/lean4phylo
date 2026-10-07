/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.PositiveRealization
import Phylo.CherryQuartet
import Phylo.Split

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
   与「两个邻居不相邻」（★ `not_adj_of_adj_adj_of_degree_two`，树无三角形）。

## 诚实边界（**未完成的部分**）

* **里程碑 A 的余下**：`QG` 的**树性**（`isTree_iff_connected_and_card` + 计数）与
  **`dist` 记账**（`QPhylogram.dist (leaf x) (leaf y) = T.dist (T.leaf x) (T.leaf y)`）。
  两者都卡在同一条计数引理 `|sameE| = |V| - |Q T|`
  （＝「每个零距离类诱导的子图是树 ⟹ 类内边数 = 类大小 − 1」，再对类求和）。
  ⚠️ `Phylogram.dist` 需要 `IsTree` 才能定义，**所以 `dist` 记账无法绕开树性**。
  该计数引理已由**另一条线**在 `Phylo/ContractCount.lean` 专做（见本批协调记录）。
* **里程碑 B 余下**：`suppressVertex`（删度 2 顶点 `v`、加权为 `w(va)+w(vb)` 的边 `a—b`）的
  完整构造（新顶点类型 + 图 + `IsTree` + `leaf_iff_degree_one` + `no_degree_two` + 权 + `dist` 记账），
  以及它的迭代（`Fintype.card T.V` 递减的良基递归）。**关键观察**（已核）：
  `a`、`b` 的度**不变**（各丢一条、各得一条）⇒ 抑制不产生新的度 1／度 2 顶点 ⇒ 迭代必终止。
* **里程碑 C**：`exists_pos_realization_of_dist_pos` 与目标定理
  `exists_realizingPhylogram_pos_of_addConst` 的接线**未做**（依赖 A、B）。
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

end Contract

end Phylo