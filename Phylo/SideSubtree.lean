/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.Algorithm.Cherry
import Phylo.Binary

/-!
# `Phylo.SideSubtree` —— 边的**侧分量**是子树，且两侧各有 ≥ 2 叶

**动机**：`Cladogram` 每条内部边 `e = ⟦u,v⟧` 的两侧各含 **≥ 2 个叶** —— 这是多处缺口的共同前置
（quartet → split 的恢复、KF 距离的 `Split` 构造、`QuartetDecidesTree` 的极大性论证）。

**证明路线（计数）**：设 `U = T − e` 中含 `u` 的分量。

1. **跨越 `U` 的边只有 `e`**（`eq_edge_of_adj_of_mem_sideVertices_of_notMem`）；
2. `U` 的**诱导子图是树**（连通 = 分量；无环 = `IsAcyclic.induce`）——
   `isTree_induce_sideVertices`，故 `#边 = |U| − 1`；
3. 握手引理 + `degree_induce_of_neighborSet_subset`（非 `u` 顶点的度与 `T` 中相同）给出
   `2(|U| − 1) ≥ ℓ_U + 3·i_U − 1`，而 `|U| = ℓ_U + i_U`，故 **`ℓ_U ≥ i_U + 1 ≥ 2`**
   （`u` 本身是内部顶点 ⟹ `i_U ≥ 1`）。

⇒ `2 ≤ |sideLeaves e u|`（`two_le_card_sideLeaves`）。
-/

open Phylo

universe u v

variable {X : Type u} [Fintype X] [DecidableEq X]

set_option linter.unusedSectionVars false
set_option linter.unusedSectionVars false

namespace Cladogram

variable (T : Cladogram.{u, v} X)

/-! ## 侧顶点集 -/

/-- 边 `e` 的 `u` **侧顶点集**：`T − e` 中含 `u` 的连通分量。 -/
noncomputable def sideVertices (e : Sym2 T.V) (u : T.V) : Finset T.V := by
  classical
  exact Finset.univ.filter fun w => (T.graph.deleteEdges {e}).Reachable w u

theorem mem_sideVertices {e : Sym2 T.V} {u w : T.V} :
    w ∈ T.sideVertices e u ↔ (T.graph.deleteEdges {e}).Reachable w u := by
  classical
  simp [sideVertices]

theorem self_mem_sideVertices (e : Sym2 T.V) (u : T.V) : u ∈ T.sideVertices e u := by
  classical
  rw [mem_sideVertices]

/-- **跨越 `U` 的边只有 `e` 本身**（`U` 是 `T − e` 的一个分量）。 -/
theorem eq_edge_of_adj_of_mem_sideVertices_of_notMem {e : Sym2 T.V} {u w z : T.V}
    (hadj : T.graph.Adj w z) (hw : w ∈ T.sideVertices e u) (hz : z ∉ T.sideVertices e u) :
    s(w, z) = e := by
  classical
  by_contra hne
  refine hz ?_
  rw [mem_sideVertices]
  rw [mem_sideVertices] at hw
  have hadj' : (T.graph.deleteEdges {e}).Adj w z :=
    SimpleGraph.deleteEdges_adj.mpr ⟨hadj, hne⟩
  exact ((hadj'.reachable).symm).trans hw

/-! ## 侧分量诱导一棵子树 -/

theorem preconnected_induce_sideVertices {e : Sym2 T.V} {u : T.V} :
    (T.graph.induce (↑(T.sideVertices e u) : Set T.V)).Preconnected := by
  classical
  intro a b
  have ha' : (T.graph.deleteEdges {e}).Reachable (a : T.V) u := by
    rw [← mem_sideVertices]; exact a.2
  have hb' : (T.graph.deleteEdges {e}).Reachable (b : T.V) u := by
    rw [← mem_sideVertices]; exact b.2
  have ha'' := ha'
  obtain ⟨p₁⟩ := ha'
  obtain ⟨p₂⟩ := hb'
  -- 在 `T − e` 中的 walk，再提升回 `T`
  set p' : (T.graph.deleteEdges {e}).Walk (a : T.V) (b : T.V) := p₁.append p₂.reverse with hp'
  set p : T.graph.Walk (a : T.V) (b : T.V) := p'.mapLe (SimpleGraph.deleteEdges_le {e}) with hp
  have hsupp : p.support = p'.support := by
    rw [hp, SimpleGraph.Walk.support_mapLe_eq_support]
  have hmem : ∀ x ∈ p.support, x ∈ (↑(T.sideVertices e u) : Set T.V) := by
    intro x hx
    show x ∈ T.sideVertices e u
    rw [mem_sideVertices]
    rw [hsupp] at hx
    exact ((SimpleGraph.reachable_of_mem_support p' hx).symm).trans ha''
  refine ⟨(p.induce (↑(T.sideVertices e u)) hmem).copy ?_ ?_⟩
  · exact Subtype.ext rfl
  · exact Subtype.ext rfl

/-- ★★ **侧分量的诱导子图是一棵树**（连通 = 分量 · 无环 = 子图）。 -/
theorem isTree_induce_sideVertices {e : Sym2 T.V} {u : T.V} :
    (T.graph.induce (↑(T.sideVertices e u) : Set T.V)).IsTree := by
  classical
  exact ⟨SimpleGraph.Connected.mk T.preconnected_induce_sideVertices
      (nonempty := ⟨⟨u, T.self_mem_sideVertices e u⟩⟩),
    T.isTree.isAcyclic.induce _⟩

/-- ★★ **侧分量的边数**：`#边 + 1 = |U|`。 -/
theorem card_edgeFinset_induce_sideVertices {e : Sym2 T.V} {u : T.V} :
    (T.graph.induce (↑(T.sideVertices e u) : Set T.V)).edgeFinset.card + 1
      = Fintype.card ↥(↑(T.sideVertices e u) : Set T.V) :=
  T.isTree_induce_sideVertices.card_edgeFinset

end Cladogram
/-! ## ⬜ 未完成：两侧各 ≥ 2 叶（计数部分）

**目标**：`2 ≤ (T.sideLeaves s(u,v) u).card`（`u` 非叶）。

**已就位**：侧分量的诱导子图是树（`isTree_induce_sideVertices`）⟹ `#边 = |U| − 1`（`card_edgeFinset_induce_sideVertices`）。

**计划**（握手 + 度数，路线已在 `MEMORY.md` 记录）：
* `deg_{T[U]}(x) = deg_T(x)` 当 `x ≠ u`（`SimpleGraph.degree_induce_of_neighborSet_subset`
  + 「跨越 `U` 的边只有 `e`」），`deg_{T[U]}(u) ≥ 2`；
* 于是 `Σ_{x∈U} deg_{T[U]} ≥ ℓ_U + 3(i_U − 1) + 2`，配合 `#边 = |U| − 1` 得 `ℓ_U ≥ i_U + 1 ≥ 2`。

**为什么暂缓**（2026-10-07 深夜的实测结论，避免重复踩坑）：
* `T.sideVertices` 出现在 `T.graph.induce ↑(…)` 的类型里，**每次 `whnf` 都极贵**；
  `set_option maxHeartbeats 1600000` 仍会在 `degree_induce_of_neighborSet_subset`
  的应用处超时（2 分半 compile）。
* 引入简写 `sideInduce` 可缓解，但还需 `Fintype ↑(G.neighborSet v)` 实例与
  `Set`/`Finset` 单元素记号的强制统一（`deleteEdges_adj` 接受 `Set`，
  `Finset.mem_singleton` 给 `Finset`）。
* **建议下次**：(i) 用 `abbrev` 让 `sideVertices` 透明；(ii) 或在**子类型上直接定义图**
  （不经过 `Finset → Set → induce`），把类型复杂度降到最低。
-/
