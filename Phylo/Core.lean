/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Card

/-!
# `Phylo.Core` —— 树载体（cladogram）

第 1 层（必备）：**cladogram** = 纯拓扑的系统发生树（枝长不携带信息）。

叶集为 `X`（通过嵌入 `leaf : X ↪ V` 打入顶点集），且**无度 2 顶点**
（Semple & Steel 的正规化条件 —— 它同时是 §3.8 中「树由 split 系统唯一决定」的地基）。

设计依据：`CONCEPTS.md` §3.2（叶的定义）、§3.6.6（三层结构）、§3.9（binary 谓词）。
-/

open SimpleGraph

variable {X : Type*}

/-- **cladogram**（第 1 层，必备）：纯拓扑的系统发生 X-树。

* `V` —— 顶点集（有限、可判定相等）
* `graph` —— 底层简单图
* `isTree` —— `graph` 是一棵树
* `leaf` —— 叶标签嵌入 `X ↪ V`
* `leaf_iff_degree_one` —— 叶 ⟺ 度 1（「叶」两种视角的桥）
* `no_degree_two` —— 无度 2 顶点（正规化条件）
-/
structure Cladogram (X : Type*) where
  V : Type*
  fintypeV : Fintype V
  decEqV : DecidableEq V
  graph : SimpleGraph V
  decAdj : DecidableRel graph.Adj
  isTree : graph.IsTree
  leaf : X ↪ V
  leaf_iff_degree_one : ∀ v : V, (∃ x : X, leaf x = v) ↔ graph.degree v = 1
  no_degree_two : ∀ v : V, graph.degree v ≠ 2

attribute [instance] Cladogram.fintypeV Cladogram.decEqV Cladogram.decAdj

namespace Cladogram

variable {X : Type*} (T : Cladogram X)

/-- `v` 是叶 ⟺ 它是某个 taxon 标签的像。 -/
def IsLeaf (v : T.V) : Prop := ∃ x : X, T.leaf x = v

/-- 叶标签映射是单射（直接来自嵌入）。 -/
theorem leaf_injective : Function.Injective T.leaf :=
  T.leaf.injective

/-- 不同标签给出不同顶点。 -/
theorem leaf_eq_iff {x y : X} : T.leaf x = T.leaf y ↔ x = y :=
  T.leaf.injective.eq_iff

/-- **「是叶」⟺「度 1」**（两视角等价，由结构字段提供）。 -/
theorem isLeaf_iff_degree_eq_one (v : T.V) : T.IsLeaf v ↔ T.graph.degree v = 1 :=
  T.leaf_iff_degree_one v

/-- 叶的度是 1。 -/
theorem IsLeaf.degree_eq_one {v : T.V} (h : T.IsLeaf v) : T.graph.degree v = 1 :=
  (T.isLeaf_iff_degree_eq_one v).mp h

/-- 度 1 的顶点是叶。 -/
theorem degree_eq_one_isLeaf {v : T.V} (h : T.graph.degree v = 1) : T.IsLeaf v :=
  (T.isLeaf_iff_degree_eq_one v).mpr h

/-- 叶的度不为 2（由度 1 立得）。 -/
theorem IsLeaf.degree_ne_two {v : T.V} (h : T.IsLeaf v) : T.graph.degree v ≠ 2 := by
  rw [h.degree_eq_one]
  decide

/-- **树中两点间路径唯一**（M0 地基；白蹭 Mathlib 的 `isTree_iff_existsUnique_path`）。 -/
theorem existsUnique_path (u v : T.V) : ∃! p : T.graph.Walk u v, p.IsPath :=
  (isTree_iff_existsUnique_path.mp T.isTree).2 u v

end Cladogram

/-! ## 第 2 层（必备）：phylogram —— 拓扑 + 可加边权 -/

/-- 树的**边类型**：`graph.edgeSet` 作为 `Sym2 V` 的子类型。

    §3.6.5 决策（子路线 A）：`E` **派生**自 `edgeSet`，零维护 —— 不给结构新增字段。 -/
abbrev Edge {X : Type*} (T : Cladogram X) : Type _ :=
  {e : Sym2 T.V // e ∈ T.graph.edgeSet}

/-- **phylogram**（第 2 层，必备）：cladogram + 定义在**边**上的非负权重。

    「可加」（沿路径求和 = 距离）由 `dist` 承载，见 `CONCEPTS.md` §3.6.4 / §3.6.6。

    * `extends Cladogram X` —— 免费继承全部拓扑引理
    * `w : Edge → ℝ` —— 边权（定义域**只含真正的边**，无冗余）
    * `w_nonneg` —— 非负（树度量要求；负权排除） -/
structure Phylogram (X : Type*) extends Cladogram X where
  w : Edge toCladogram → ℝ
  w_nonneg : ∀ e, 0 ≤ w e

-- `Phylogram` 的实例（`Fintype V` / `DecidableEq V` / `DecidableRel Adj`）
-- 经 `Cladogram.fintypeV` 等（已注册为 instance）沿 `toCladogram` 自动找到。

namespace Phylogram

variable {X : Type*} (T : Phylogram X)

/-- 边权非负（字段的引用版）。 -/
theorem w_nonneg' (e : Edge T.toCladogram) : 0 ≤ T.w e :=
  T.w_nonneg e

/-- `w` 的定义域确实只含 `graph` 的边（由子类型保证）。 -/
theorem w_mem (e : Edge T.toCladogram) : e.1 ∈ T.graph.edgeSet :=
  e.2

section Dist

open Classical

/-- 把边权扩展到**所有**顶点对（非边取 0）—— 便于沿 `Walk` 求和。

    （`w` 本身只定义在边上；这里是求和用的技术性扩展。） -/
noncomputable def wExt (e : Sym2 T.V) : ℝ :=
  if h : e ∈ T.graph.edgeSet then T.w ⟨e, h⟩ else 0

/-- 一条 `Walk` 的**加权长度**（按边出现次数累加）。 -/
noncomputable def walkDist {u v : T.V} (p : T.graph.Walk u v) : ℝ :=
  (p.edges.map T.wExt).sum

/-- 两点间的**加权距离**：树上唯一路径的边权和。

    这正是「**可加性**」的化身（§3.6.4）—— `phylogram` 区别于 `annotated` 之处。 -/
noncomputable def dist (u v : T.V) : ℝ :=
  T.walkDist (T.existsUnique_path u v).choose

/-- `u` 到自身距离为 0。

    对树，`u → u` 的**唯一路径**必是平凡 walk（`IsPath` 无重复顶点），故边表为空。 -/
theorem dist_self (u : T.V) : T.dist u u = 0 := by
  unfold dist walkDist
  have hnil : (T.existsUnique_path u u).choose = SimpleGraph.Walk.nil :=
    ((T.existsUnique_path u u).choose_spec.2 SimpleGraph.Walk.nil (by simp)).symm
  rw [hnil]
  simp [SimpleGraph.Walk.edges]

end Dist

end Phylogram

/-! ## 树同构 `Iso`（§3.8：A 作定义） -/

/-- **保标号同构**（identity on `X`）：两棵 cladogram 之间的同构。

§3.8 决策：`Iso` 作「树相等」的**定义**（而 Splits-Equivalence 作**定理**）。
底层复用 Mathlib 的 `SimpleGraph.Iso`（记法 `G ≃g G'`），只需再保持 `leaf`。 -/
structure Iso {X : Type*} (T T' : Cladogram X) where
  gIso : T.graph ≃g T'.graph
  leaf_compat : ∀ x : X, gIso (T.leaf x) = T'.leaf x

namespace Iso

variable {X : Type*} {T T' T'' : Cladogram X}

/-- 同构关系自反。 -/
def refl (T : Cladogram X) : Iso T T where
  gIso := SimpleGraph.Iso.refl
  leaf_compat := fun _ => rfl

/-- 同构关系对称。 -/
def symm (e : Iso T T') : Iso T' T where
  gIso := e.gIso.symm
  leaf_compat := fun x => by
    have h := e.leaf_compat x
    -- gIso.symm (gIso a) = a
    have := congrArg e.gIso.symm h
    simpa using this.symm

end Iso

/-! ## restriction：`T|Y` 的顶点集（§3.7 第一步） -/

namespace Cladogram

open Classical

variable {X : Type*} (T : Cladogram X)

/-- `u` 到 `v` 的**唯一路径**上的顶点集合。 -/
noncomputable def pathVerts (u v : T.V) : Finset T.V :=
  ((T.existsUnique_path u v).choose.support).toFinset

/-- 连接 `Y` 中所有叶的**最小连通子树**的顶点集（span）。

    §3.7：`T|Y` 的顶点集取自这里（再抑制度 2 顶点）。 -/
noncomputable def spanVerts (Y : Finset X) : Finset T.V :=
  Y.biUnion fun y₁ => Y.biUnion fun y₂ => T.pathVerts (T.leaf y₁) (T.leaf y₂)

/-- 叶 `y` 的像属于 `spanVerts T Y`（当 `Y` 非空）。 -/
theorem leaf_mem_spanVerts {Y : Finset X} {y : X} (hy : y ∈ Y) :
    T.leaf y ∈ T.spanVerts Y := by
  unfold spanVerts
  refine Finset.mem_biUnion.mpr ⟨y, hy, ?_⟩
  refine Finset.mem_biUnion.mpr ⟨y, hy, ?_⟩
  unfold pathVerts
  exact List.mem_toFinset.mpr (SimpleGraph.Walk.start_mem_support _)

/-- `T` 在顶点集 `S` 上的**诱导子图**（白蹭 `SimpleGraph.induce`，它即 `comap`）。

    §3.7：`T|Y` 先取 span 上的诱导子图，再抑制度 2 顶点。 -/
abbrev inducedSubgraph (T : Cladogram X) (S : Finset T.V) :
    SimpleGraph ↥(↑S : Set T.V) :=
  SimpleGraph.induce (↑S : Set T.V) T.graph

end Cladogram
