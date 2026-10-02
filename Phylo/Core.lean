/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
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
