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

/-! ### 二叉性 —— **无根树**的表示约定

`CONCEPTS.md` §3.3（2026-10-06 老师定）：**表示无根树采取「内部节点 degree = 3」的形式**。

（`no_degree_two` 只排除度 2、允许 polytomy；`IsBinary` 进一步要求内部顶点度**恰为** 3。） -/

/-- **二叉（binary）无根树**：所有内部顶点度恰为 3。 -/
def IsBinary (T : Cladogram X) : Prop :=
  ∀ v : T.V, ¬ T.IsLeaf v → T.graph.degree v = 3

/-- 二叉树的度只有 1（叶）与 3（内部顶点）—— **无根二叉树**的特征刻画。 -/
theorem IsBinary.degree_eq_one_or_three {T : Cladogram X} (h : T.IsBinary) (v : T.V) :
    T.graph.degree v = 1 ∨ T.graph.degree v = 3 := by
  by_cases hv : T.IsLeaf v
  · exact Or.inl hv.degree_eq_one
  · exact Or.inr (h v hv)

/-- 二叉树内部顶点的度就是 3（定义的重述，便于使用）。 -/
theorem IsBinary.degree_eq_three {T : Cladogram X} (h : T.IsBinary) {v : T.V}
    (hv : ¬ T.IsLeaf v) : T.graph.degree v = 3 := h v hv

end Cladogram

/-! ## **有根树**的底层实现：`Cladogram (X ⊕ Unit)`

`CONCEPTS.md` §3.3 —— **方案 A 已定**（2026-10-02 老师拍板，2026-10-06 重申）：

> **先做无根，有根另建一层，底层暂时定义为「有名为 root 的叶子节点的无根树」。**
> 老师补充（2026-10-06）：**表示无根树采取「内部节点 degree = 3」的形式**（见 `IsBinary`）；
> **表示有根树可以弄个带 root 叶节点的无根树**，也可选择与它同构的形式。

**三条纪律**（§3.3，防类型污染）：

1. **标记叶不塞进 `X`** —— 用 `X ⊕ Unit`（真 taxon 是 `Sum.inl x`）；
2. **「根」是标记叶的唯一邻居**（一个顶点），不是标记叶本身；
3. `X ⊕ Unit` **只出现在转换引理里**，不进 rooted 侧引理签名
   （rooted 侧的抽象接口将来用 **hierarchy**：Semple–Steel 已证 rooted tree ↔ laminar cluster family）。

先例：Dress (1997)「X is augmented by an additional outgroup `*`」；arXiv:1203.5835
的计数 `|R(n)| = (2n−3)·|B(n)|` 说明「无根 + 一个标记叶」与「有根」双射。 -/

/-- **有根树的底层实现**：`Cladogram (X ⊕ Unit)`，标记叶 = `Sum.inr ()`。

真 taxon 是 `Sum.inl x`；`Sum.inr ()` 是那个「名为 root 的叶子节点」。
（指向 rooted 层抽象接口的转换引理待建，见 §3.3。） -/
abbrev RootedCladogram (X : Type*) := Cladogram (X ⊕ Unit)

/-- **有根二叉树的刻画**（底层实现视角）：**标记叶的邻居**（即有根树的 `root`）度为 2，
其余非叶顶点度为 3 —— 正是「有根二叉树 = root 度 2 + 其余内部点度 3」。

（标记叶的邻居唯一：叶度为 1。） -/
def IsRootedBinary {X : Type*} (T : RootedCladogram X) : Prop :=
  (∀ v : T.V, T.graph.Adj (T.leaf (Sum.inr ())) v → T.graph.degree v = 2) ∧
    ∀ v : T.V, ¬ T.IsLeaf v → ¬ T.graph.Adj (T.leaf (Sum.inr ())) v →
      T.graph.degree v = 3

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

/-- **同构关系传递**（`(e.trans e') (T.leaf x) = e' (e (T.leaf x))`）。

有了它 `Iso` 构成等价关系（`refl` / `symm` / `trans`）—— M1 的欠账。 -/
def trans (e : Iso T T') (e' : Iso T' T'') : Iso T T'' where
  gIso := e.gIso.trans e'.gIso
  leaf_compat := fun x => by
    have h1 : e.gIso (T.leaf x) = T'.leaf x := e.leaf_compat x
    have h2 : e'.gIso (T'.leaf x) = T''.leaf x := e'.leaf_compat x
    rw [show (e.gIso.trans e'.gIso) (T.leaf x) = e'.gIso (e.gIso (T.leaf x)) from rfl, h1, h2]

/-- 同构像唯一决定：`gIso` 与 `leaf_compat` 一起锁定了顶点对应。 -/
theorem trans_apply (e : Iso T T') (e' : Iso T' T'') (v : T.V) :
    (e.trans e').gIso v = e'.gIso (e.gIso v) := rfl

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
