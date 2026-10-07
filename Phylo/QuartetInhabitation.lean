/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.QuartetUnique
import Phylo.Binary
import Phylo.InternalEdge

/-!
# `Phylo.QuartetInhabitation` —— binary 树在任意 4-元集上展示一个 `2|2` split

**目标（T0.6 收口，★★★）**`Cladogram.exists_displaysSplitOn_card_two`：

> binary 树 `T` 在任意 4-元叶集 `S` 上都展示一个 `2|2` split（`q.sideA.card = 2`）。

这是 `Phylo/Stat/MSC.lean` 的 `QuartetTree.q_card` 字段**可满足**的依据 —— 缺了它
`QuartetTree` 有**空真风险**。`Phylo/QuartetUnique.lean` 的 ★★★ `Cladogram.displaysSplitOn_unique`
把两个「`sideA.card = 2`」当**假设**，本文件补上「至少存在一条」。

## 证明路线（T0.6 既定计划）

1. **极小子树 `U = T(S)`**（`steinerVerts`）：取定基点 `x₀ ∈ S`，`U := ⋃_{y ∈ S} (x₀–y 路径的顶点集)`；
   关键性质：前缀封闭（`pathVerts_subset_steinerVerts`）与**凸性**
   （`pathVerts_subset_steinerVerts_of_mem`）。
2. **★ 路径内点不是叶**（`exists_two_adj_of_mem_support_of_ne`）：路径内点两侧各有一条边，
   故有两个互异邻居（`Walk.getVert` + `IsPath.getVert_injOn`）⇒ 度 ≥ 2 ⇒ 不是叶（叶度 = 1）。
   **这一步保证 `S` 外的叶不会混进 `U`。**
3. **诱导子图 `T[U]` 是一棵树**（`isTree_steinerSubgraph`）。
4. **`T[U]` 的叶恰是 `S` 的像**（`steinerDegree_eq_one_iff`）。
5. **度数记账**：`T[U]` 有度 3 顶点 `v`（计数 + 握手引理，`exists_steinerDegree_eq_three`）。
6. **分支计数**：`v` 的 3 个 `U`-邻居给出 `S` 的 3-分划（`firstStepOf` 的纤维），
   每支非空（`exists_firstStepOf_eq`）⇒ 某支恰含 2 个 `S` 元素 ⇒ 该边 `sideLeaves` 在 `S` 上
   恰 2 个元素 ⇒ 用 `Split.restrict` 收口（`exists_displaysSplitOn_card_two`）。

## 状态

* ✅ 阶段 1：路径支持集工具 + ★ 内点引理（`exists_two_adj_of_mem_support_of_ne`）
* ✅ 阶段 2：`U` 的凸性 / `T[U]` 是树 / `T[U]` 的叶 = `S`（`steinerDegree_eq_one_iff`）
* ✅ 阶段 3：度数记账（`exists_steinerDegree_eq_three`）
* ✅ 阶段 4：分支计数 + 最终 ★★★ `exists_displaysSplitOn_card_two`（**零 `sorry` / 零 `axiom`**）
* ✅ 阶段 5（收口时补）：★★★ `QuartetTree.ofBinary` —— binary 树**给出**一个 `QuartetTree`，
  即 `q_card` 字段**可被赋值** ⇒ `QuartetTree` **不是空类型**（空真风险解除）。
-/

universe u v

variable {X : Type u} [Fintype X] [DecidableEq X]

namespace Cladogram

open Classical
open SimpleGraph

set_option linter.unusedSectionVars false

variable (T : Cladogram.{u, v} X)

/-! ## 阶段 1：路径支持集工具 -/

/-- 唯一路径的选择结果等于任一给定的 `IsPath` walk。 -/
theorem existsUnique_path_choose_eq {a b : T.V} {p : T.graph.Walk a b} (hp : p.IsPath) :
    (T.existsUnique_path a b).choose = p :=
  ((T.existsUnique_path a b).choose_spec.2 p hp).symm

/-- `pathVerts a b` 就是任一 `IsPath` walk 的支持集。 -/
theorem pathVerts_eq_support_toFinset {a b : T.V} {p : T.graph.Walk a b} (hp : p.IsPath) :
    T.pathVerts a b = p.support.toFinset := by
  unfold Cladogram.pathVerts
  rw [T.existsUnique_path_choose_eq hp]

/-- `pathVerts a b` 落在**任意**连接 `a`、`b` 的 walk 的支持集里。 -/
theorem pathVerts_subset_support_toFinset {a b : T.V} (W : T.graph.Walk a b) :
    T.pathVerts a b ⊆ W.support.toFinset := by
  rw [T.pathVerts_eq_support_toFinset W.toPath.isPath]
  intro z hz
  rw [List.mem_toFinset] at hz ⊢
  exact Walk.support_toPath_subset_support W hz

/-- **前缀封闭**：`z` 在 `x–y` 路径上 ⟹ `x–z` 路径 ⊆ `x–y` 路径。 -/
theorem pathVerts_subset_of_mem_pathVerts {x y z : T.V} (hz : z ∈ T.pathVerts x y) :
    T.pathVerts x z ⊆ T.pathVerts x y := by
  classical
  have hpp : ((T.existsUnique_path x y).choose).IsPath := (T.existsUnique_path x y).choose_spec.1
  have hz' : z ∈ ((T.existsUnique_path x y).choose).support := by
    rw [Cladogram.pathVerts, List.mem_toFinset] at hz
    exact hz
  rw [T.pathVerts_eq_support_toFinset (hpp.takeUntil hz'), T.pathVerts_eq_support_toFinset hpp]
  intro w hw
  rw [List.mem_toFinset] at hw ⊢
  exact Walk.support_takeUntil_subset_support _ hz' hw

/-- 起点在路径上。 -/
theorem mem_pathVerts_left (a b : T.V) : a ∈ T.pathVerts a b := by
  rw [Cladogram.pathVerts, List.mem_toFinset]
  exact Walk.start_mem_support _

/-- 终点在路径上。 -/
theorem mem_pathVerts_right (a b : T.V) : b ∈ T.pathVerts a b := by
  rw [Cladogram.pathVerts, List.mem_toFinset]
  exact Walk.end_mem_support _

/-- 路径与其反向的顶点集相同。 -/
theorem pathVerts_comm (a b : T.V) : T.pathVerts a b = T.pathVerts b a := by
  classical
  have hpp : ((T.existsUnique_path a b).choose).IsPath := (T.existsUnique_path a b).choose_spec.1
  rw [T.pathVerts_eq_support_toFinset hpp,
    T.pathVerts_eq_support_toFinset (p := ((T.existsUnique_path a b).choose).reverse) hpp.reverse,
    Walk.support_reverse]
  ext z
  simp

/-- ★ **路径内点至少有两个互异的邻居，且两个邻居都在路径上**。

证明：把内点写成 `p.getVert i`（`0 < i < p.length`），两个邻居为
`p.getVert (i-1)` 与 `p.getVert (i+1)`；它们互异由 `IsPath.getVert_injOn` 保证。 -/
theorem exists_two_adj_of_mem_support_of_ne {a b v : T.V} {p : T.graph.Walk a b}
    (hp : p.IsPath) (hv : v ∈ p.support) (hva : v ≠ a) (hvb : v ≠ b) :
    ∃ z₁ z₂ : T.V, z₁ ≠ z₂ ∧ T.graph.Adj v z₁ ∧ T.graph.Adj v z₂ ∧
      z₁ ∈ p.support ∧ z₂ ∈ p.support := by
  classical
  obtain ⟨i, hiv, hi⟩ := Walk.mem_support_iff_exists_getVert.mp hv
  have hpos : 0 < i := by
    rcases Nat.eq_zero_or_pos i with h | h
    · subst h
      rw [Walk.getVert_zero] at hiv
      exact absurd hiv.symm hva
    · exact h
  have hlt : i < p.length := by
    rcases lt_or_eq_of_le hi with h | h
    · exact h
    · subst h
      rw [Walk.getVert_length] at hiv
      exact absurd hiv.symm hvb
  refine ⟨p.getVert (i - 1), p.getVert (i + 1), ?_, ?_, ?_,
    Walk.getVert_mem_support _ _, Walk.getVert_mem_support _ _⟩
  · intro h
    have hinj : i - 1 = i + 1 :=
      hp.getVert_injOn (show i - 1 ≤ p.length by omega)
        (show i + 1 ≤ p.length by omega) h
    omega
  · have hadj := p.adj_getVert_succ (i := i - 1) (show i - 1 < p.length by omega)
    rw [show i - 1 + 1 = i from by omega, hiv] at hadj
    exact hadj.symm
  · have hadj := p.adj_getVert_succ (i := i) hlt
    rwa [hiv] at hadj

/-! ## 阶段 2：极小子树 `T(S)` -/

/-- **极小子树 `T(S)` 的顶点集**（基点 `x₀ ∈ S`）：`x₀` 到每个 `y ∈ S` 的路径顶点之并。 -/
noncomputable def steinerVerts (x₀ : X) (S : Finset X) : Finset T.V :=
  S.biUnion fun y => T.pathVerts (T.leaf x₀) (T.leaf y)

/-- `T(S)` 的顶点类型。 -/
abbrev SteinerVert (x₀ : X) (S : Finset X) : Type _ :=
  ↥(↑(T.steinerVerts x₀ S) : Set T.V)

/-- `T(S)` 的诱导子图。 -/
noncomputable abbrev steinerSubgraph (x₀ : X) (S : Finset X) : SimpleGraph (T.SteinerVert x₀ S) :=
  T.inducedSubgraph (T.steinerVerts x₀ S)

/-- 把 `T.V` 中的点（已知在 `U` 中）包装成 `T(S)` 的顶点。 -/
noncomputable def steinerVertOf {x₀ : X} {S : Finset X} (z : T.V)
    (hz : z ∈ T.steinerVerts x₀ S) : T.SteinerVert x₀ S :=
  ⟨z, by simpa using hz⟩

@[simp] theorem steinerVertOf_val {x₀ : X} {S : Finset X} (z : T.V)
    (hz : z ∈ T.steinerVerts x₀ S) : (T.steinerVertOf z hz : T.V) = z := rfl

/-- `U` 的成员判定。 -/
theorem mem_steinerVerts {x₀ : X} {S : Finset X} {z : T.V} :
    z ∈ T.steinerVerts x₀ S ↔ ∃ y ∈ S, z ∈ T.pathVerts (T.leaf x₀) (T.leaf y) :=
  Finset.mem_biUnion

/-- `S` 中元素的像落在 `U` 中。 -/
theorem leaf_mem_steinerVerts {x₀ y : X} {S : Finset X} (hy : y ∈ S) :
    T.leaf y ∈ T.steinerVerts x₀ S :=
  Finset.mem_biUnion.mpr ⟨y, hy, T.mem_pathVerts_right _ _⟩

/-- `T(S)` 的顶点的底层点在 `U` 中。 -/
theorem steinerVert_mem {x₀ : X} {S : Finset X} (v : T.SteinerVert x₀ S) :
    (v : T.V) ∈ T.steinerVerts x₀ S :=
  v.2

/-- `S` 的元素作为 `T(S)` 的顶点（叶的像）。 -/
noncomputable def steinerLeafOf (x₀ : X) (S : Finset X) (x : {x // x ∈ S}) :
    T.SteinerVert x₀ S :=
  T.steinerVertOf (T.leaf x.1) (T.leaf_mem_steinerVerts x.2)

@[simp] theorem steinerLeafOf_val (x₀ : X) (S : Finset X) (x : {x // x ∈ S}) :
    ((T.steinerLeafOf x₀ S x : T.SteinerVert x₀ S) : T.V) = T.leaf x.1 := rfl

/-- **前缀封闭**：`z ∈ U` ⟹ 基点 `x₀` 到 `z` 的路径全在 `U` 中。 -/
theorem pathVerts_subset_steinerVerts {x₀ : X} {S : Finset X} {z : T.V}
    (hz : z ∈ T.steinerVerts x₀ S) :
    T.pathVerts (T.leaf x₀) z ⊆ T.steinerVerts x₀ S := by
  obtain ⟨y, hy, hzy⟩ := T.mem_steinerVerts.mp hz
  exact (T.pathVerts_subset_of_mem_pathVerts hzy).trans
    fun _ hw => Finset.mem_biUnion.mpr ⟨y, hy, hw⟩

/-- ★★ **凸性**：连接 `U` 中两点的路径全在 `U` 中。 -/
theorem pathVerts_subset_steinerVerts_of_mem {x₀ : X} {S : Finset X} {a b : T.V}
    (ha : a ∈ T.steinerVerts x₀ S) (hb : b ∈ T.steinerVerts x₀ S) :
    T.pathVerts a b ⊆ T.steinerVerts x₀ S := by
  classical
  have h1 : T.pathVerts a (T.leaf x₀) ⊆ T.steinerVerts x₀ S := by
    rw [T.pathVerts_comm]
    exact T.pathVerts_subset_steinerVerts ha
  have h2 : T.pathVerts (T.leaf x₀) b ⊆ T.steinerVerts x₀ S :=
    T.pathVerts_subset_steinerVerts hb
  have hW := T.pathVerts_subset_support_toFinset
    (((T.existsUnique_path a (T.leaf x₀)).choose).append
      ((T.existsUnique_path (T.leaf x₀) b)).choose)
  intro z hz
  have hz' : z ∈ ((((T.existsUnique_path a (T.leaf x₀)).choose).append
      ((T.existsUnique_path (T.leaf x₀) b)).choose)).support := by
    have h := hW hz
    rwa [List.mem_toFinset] at h
  rw [Walk.mem_support_append_iff] at hz'
  rcases hz' with hz' | hz'
  · exact h1 (by
      rw [T.pathVerts_eq_support_toFinset (T.existsUnique_path a (T.leaf x₀)).choose_spec.1]
      exact List.mem_toFinset.mpr hz')
  · exact h2 (by
      rw [T.pathVerts_eq_support_toFinset (T.existsUnique_path (T.leaf x₀) b).choose_spec.1]
      exact List.mem_toFinset.mpr hz')

/-- ★★ **`T(S)` 的诱导子图连通**。 -/
theorem preconnected_steinerSubgraph {x₀ : X} {S : Finset X} :
    (T.steinerSubgraph x₀ S).Preconnected := by
  classical
  intro a b
  have hmem : ∀ z ∈ ((T.existsUnique_path (a : T.V) (b : T.V)).choose).support,
      z ∈ (↑(T.steinerVerts x₀ S) : Set T.V) := by
    intro z hz
    exact T.pathVerts_subset_steinerVerts_of_mem (T.steinerVert_mem a) (T.steinerVert_mem b) (by
      rw [T.pathVerts_eq_support_toFinset (T.existsUnique_path (a : T.V) (b : T.V)).choose_spec.1]
      exact List.mem_toFinset.mpr hz)
  exact ⟨(((T.existsUnique_path (a : T.V) (b : T.V)).choose).induce
    (↑(T.steinerVerts x₀ S)) hmem).copy (Subtype.ext rfl) (Subtype.ext rfl)⟩

/-- ★★ **`T(S)` 是一棵树**（连通 = 凸性 + 路径提升；无环 = 子图）。 -/
theorem isTree_steinerSubgraph {x₀ : X} {S : Finset X} (hne : (T.steinerVerts x₀ S).Nonempty) :
    (T.steinerSubgraph x₀ S).IsTree :=
  ⟨SimpleGraph.Connected.mk T.preconnected_steinerSubgraph (nonempty := by
      obtain ⟨z, hz⟩ := hne
      exact ⟨T.steinerVertOf z hz⟩),
    T.isTree.isAcyclic.induce _⟩

/-- `z` 在 `T(S)` 中的**度**：`T` 中邻居与 `U` 的交的大小（`induce` 的度 = 交）。 -/
noncomputable def steinerDegree (x₀ : X) (S : Finset X) (z : T.V) : ℕ :=
  (T.graph.neighborFinset z ∩ T.steinerVerts x₀ S).card

/-- `steinerDegree` 就是诱导子图中的度。 -/
theorem steinerDegree_eq_degree {x₀ : X} {S : Finset X} {z : T.V}
    (hz : z ∈ T.steinerVerts x₀ S) :
    T.steinerDegree x₀ S z = (T.steinerSubgraph x₀ S).degree (T.steinerVertOf z hz) :=
  (T.degree_induce_eq_card_inter (T.steinerVerts x₀ S) z hz).symm

/-- 诱导子图中顶点的度 = `steinerDegree`（`T(S)` 顶点的形式，便于 `rw`）。 -/
theorem degree_steinerSubgraph_eq (x₀ : X) (S : Finset X) (v : T.SteinerVert x₀ S) :
    (T.steinerSubgraph x₀ S).degree v = T.steinerDegree x₀ S (v : T.V) :=
  T.degree_induce_eq_card_inter (T.steinerVerts x₀ S) (v : T.V) (T.steinerVert_mem v)


/-- `T(S)` 的度 ≤ 3（binary 树的度 ∈ {1,3}）。 -/
theorem steinerDegree_le_three (hT : T.IsBinary) (x₀ : X) (S : Finset X) (z : T.V) :
    T.steinerDegree x₀ S z ≤ 3 := by
  show (T.graph.neighborFinset z ∩ T.steinerVerts x₀ S).card ≤ 3
  have hle : (T.graph.neighborFinset z ∩ T.steinerVerts x₀ S).card
      ≤ (T.graph.neighborFinset z).card := Finset.card_le_card Finset.inter_subset_left
  have hcard : (T.graph.neighborFinset z).card = T.graph.degree z :=
    SimpleGraph.card_neighborFinset_eq_degree T.graph z
  rcases hT.degree_eq_one_or_three z with h | h <;> omega

/-- ★ 路径内点在 `T(S)` 中的度 ≥ 2（两侧的边都在 `U` 中）。 -/
theorem two_le_steinerDegree_of_mem_support_of_ne {x₀ : X} {S : Finset X} {a b z : T.V}
    {p : T.graph.Walk a b} (hp : p.IsPath)
    (hpsub : ∀ w ∈ p.support, w ∈ T.steinerVerts x₀ S)
    (hz : z ∈ p.support) (hza : z ≠ a) (hzb : z ≠ b) :
    2 ≤ T.steinerDegree x₀ S z := by
  classical
  rcases T.exists_two_adj_of_mem_support_of_ne hp hz hza hzb with
    ⟨z1, z2, hne, hadj1, hadj2, hm1, hm2⟩
  show 2 ≤ (T.graph.neighborFinset z ∩ T.steinerVerts x₀ S).card
  have hsub : ({z1, z2} : Finset T.V) ⊆ T.graph.neighborFinset z ∩ T.steinerVerts x₀ S := by
    rw [Finset.insert_subset_iff, Finset.singleton_subset_iff]
    exact ⟨Finset.mem_inter.mpr
        ⟨(SimpleGraph.mem_neighborFinset T.graph z z1).mpr hadj1, hpsub z1 hm1⟩,
      Finset.mem_inter.mpr
        ⟨(SimpleGraph.mem_neighborFinset T.graph z z2).mpr hadj2, hpsub z2 hm2⟩⟩
  have hcard := Finset.card_le_card hsub
  rwa [Finset.card_pair hne] at hcard

/-- 若 `z` 在 `x₀–y` 路径（`y ∈ S`）的内点上，则它在 `T(S)` 中的度 ≥ 2。 -/
theorem two_le_steinerDegree_of_mem_pathVerts {x₀ : X} {S : Finset X} {y : X} (hy : y ∈ S)
    {z : T.V} (hz : z ∈ T.pathVerts (T.leaf x₀) (T.leaf y))
    (hz₀ : z ≠ T.leaf x₀) (hzy : z ≠ T.leaf y) :
    2 ≤ T.steinerDegree x₀ S z := by
  classical
  have hp : ((T.existsUnique_path (T.leaf x₀) (T.leaf y)).choose).IsPath :=
    (T.existsUnique_path _ _).choose_spec.1
  refine T.two_le_steinerDegree_of_mem_support_of_ne hp ?_ ?_ hz₀ hzy
  · intro w hw
    exact Finset.mem_biUnion.mpr ⟨y, hy, by
      rw [T.pathVerts_eq_support_toFinset hp]
      exact List.mem_toFinset.mpr hw⟩
  · have h := hz
    rwa [T.pathVerts_eq_support_toFinset hp, List.mem_toFinset] at h

/-- 若 `z ∈ T(S)` 不是 `S` 的像，则它在 `T(S)` 中的度 ≥ 2。 -/
theorem two_le_steinerDegree_of_not_mem_image {x₀ : X} {S : Finset X} (hx₀ : x₀ ∈ S)
    {z : T.V} (hz : z ∈ T.steinerVerts x₀ S) (hnot : ∀ x ∈ S, T.leaf x ≠ z) :
    2 ≤ T.steinerDegree x₀ S z := by
  obtain ⟨y, hy, hzy⟩ := T.mem_steinerVerts.mp hz
  exact T.two_le_steinerDegree_of_mem_pathVerts hy hzy (hnot x₀ hx₀).symm (hnot y hy).symm

/-- ★★ **`T(S)` 的叶恰是 `S` 的像**（`|S| ≥ 2`）。 -/
theorem steinerDegree_eq_one_iff {x₀ : X} {S : Finset X} (hx₀ : x₀ ∈ S) (hS2 : 2 ≤ S.card)
    {z : T.V} (hz : z ∈ T.steinerVerts x₀ S) :
    T.steinerDegree x₀ S z = 1 ↔ ∃ x ∈ S, T.leaf x = z := by
  classical
  constructor
  · intro h1
    by_contra hcon
    have h2 := T.two_le_steinerDegree_of_not_mem_image hx₀ hz
      (fun x hx hxz => hcon ⟨x, hx, hxz⟩)
    omega
  · rintro ⟨x, hx, rfl⟩
    have hleaf : T.graph.degree (T.leaf x) = 1 :=
      (T.isLeaf_iff_degree_eq_one (T.leaf x)).mp ⟨x, rfl⟩
    have hup : (T.graph.neighborFinset (T.leaf x) ∩ T.steinerVerts x₀ S).card ≤ 1 := by
      have h := Finset.card_le_card
        (Finset.inter_subset_left :
          (T.graph.neighborFinset (T.leaf x) ∩ T.steinerVerts x₀ S)
            ⊆ T.graph.neighborFinset (T.leaf x))
      rwa [SimpleGraph.card_neighborFinset_eq_degree, hleaf] at h
    have hlow : 1 ≤ (T.graph.neighborFinset (T.leaf x) ∩ T.steinerVerts x₀ S).card := by
      obtain ⟨y, hy, hyx⟩ : ∃ y ∈ S, y ≠ x := by
        obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < S.card)
        by_cases hax : a = x
        · exact ⟨b, hb, fun h => hab (hax.trans h.symm)⟩
        · exact ⟨a, ha, hax⟩
      have hne : T.leaf x ≠ T.leaf y := fun h => hyx (T.leaf.injective h).symm
      let p := (T.existsUnique_path (T.leaf x) (T.leaf y)).choose
      have hp : p.IsPath := (T.existsUnique_path (T.leaf x) (T.leaf y)).choose_spec.1
      have hpos : 0 < p.length := by
        rcases Nat.eq_zero_or_pos p.length with h | h
        · exact absurd (Walk.eq_of_length_eq_zero h) hne
        · exact h
      have hadj : T.graph.Adj (T.leaf x) (p.getVert 1) := by
        have h := p.adj_getVert_succ (i := 0) hpos
        rw [Walk.getVert_zero] at h
        simpa using h
      have hmemU : p.getVert 1 ∈ T.steinerVerts x₀ S :=
        T.pathVerts_subset_steinerVerts_of_mem (T.leaf_mem_steinerVerts hx)
          (T.leaf_mem_steinerVerts hy) (by
            rw [T.pathVerts_eq_support_toFinset (p := p) hp]
            exact List.mem_toFinset.mpr (Walk.getVert_mem_support p 1))
      exact Finset.card_pos.mpr ⟨p.getVert 1,
        Finset.mem_inter.mpr
          ⟨(SimpleGraph.mem_neighborFinset T.graph _ _).mpr hadj, hmemU⟩⟩
    show (T.graph.neighborFinset (T.leaf x) ∩ T.steinerVerts x₀ S).card = 1
    omega

/-- `S` 的像是 `T(S)` 中互异的度 1 顶点。 -/
theorem steinerLeafOf_injective (x₀ : X) (S : Finset X) :
    Function.Injective (T.steinerLeafOf x₀ S) := by
  intro a b hab
  have h1 : T.leaf a.1 = T.leaf b.1 := by
    have h := congrArg (fun v : T.SteinerVert x₀ S => (v : T.V)) hab
    simpa using h
  exact Subtype.ext (T.leaf.injective h1)

/-! ## 阶段 3：`T(S)` 有度 3 顶点 -/

/-- ★★ **`T(S)` 有度 3 顶点**（`|S| = 4`：4 个叶 + 握手引理）。

反证：若无度 3 顶点，则每个顶点的度 ∈ {1,2}（由 ★ 内点引理与 binary 性），
度 1 顶点 ≥ 4 个（`S` 的像），于是 `ℓ + 2m = 2(|V|-1) = 2(ℓ+m-1)` 给出 `ℓ = 2`，矛盾。 -/
theorem exists_steinerDegree_eq_three (hT : T.IsBinary) {x₀ : X} {S : Finset X}
    (hx₀ : x₀ ∈ S) (hScard : S.card = 4) :
    ∃ z ∈ T.steinerVerts x₀ S, T.steinerDegree x₀ S z = 3 := by
  classical
  have hS2 : 2 ≤ S.card := by omega
  have hTtree : (T.steinerSubgraph x₀ S).IsTree :=
    T.isTree_steinerSubgraph ⟨T.leaf x₀, T.leaf_mem_steinerVerts hx₀⟩
  by_contra hcon
  have hcon' : ∀ z ∈ T.steinerVerts x₀ S, T.steinerDegree x₀ S z ≠ 3 := by
    intro z hz h3
    exact hcon ⟨z, hz, h3⟩
  let L : Finset (T.SteinerVert x₀ S) :=
    Finset.univ.filter fun v => (T.steinerSubgraph x₀ S).degree v = 1
  let Mi : Finset (T.SteinerVert x₀ S) :=
    Finset.univ.filter fun v => ¬ (T.steinerSubgraph x₀ S).degree v = 1
  have hLeq : L = Finset.univ.filter
      (fun v => (T.steinerSubgraph x₀ S).degree v = 1) := rfl
  have hMieq : Mi = Finset.univ.filter
      (fun v => ¬ (T.steinerSubgraph x₀ S).degree v = 1) := rfl
  -- 度 1 顶点 ≥ 4
  have hL4 : 4 ≤ L.card := by
    have hsub : S.attach.image (T.steinerLeafOf x₀ S) ⊆ L := by
      intro v hv
      obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hv
      have hmem : (T.steinerSubgraph x₀ S).degree (T.steinerLeafOf x₀ S x) = 1 := by
        rw [T.degree_steinerSubgraph_eq x₀ S (T.steinerLeafOf x₀ S x)]
        exact (T.steinerDegree_eq_one_iff hx₀ hS2 (T.leaf_mem_steinerVerts x.2)).mpr
          ⟨x.1, x.2, rfl⟩
      show (T.steinerLeafOf x₀ S x) ∈ Finset.univ.filter
        (fun v => (T.steinerSubgraph x₀ S).degree v = 1)
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hmem⟩
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ (T.steinerLeafOf_injective x₀ S),
      Finset.card_attach, hScard] at h1
    exact h1
  -- 非度 1 顶点的度恰为 2
  have hMi2 : ∀ v ∈ Mi, (T.steinerSubgraph x₀ S).degree v = 2 := by
    intro v hv
    rw [hMieq] at hv
    have hv' : ¬ (T.steinerSubgraph x₀ S).degree v = 1 := (Finset.mem_filter.mp hv).2
    have hle : (T.steinerSubgraph x₀ S).degree v ≤ 3 := by
      rw [T.degree_steinerSubgraph_eq x₀ S v]
      exact T.steinerDegree_le_three hT x₀ S (v : T.V)
    have hge : 2 ≤ (T.steinerSubgraph x₀ S).degree v := by
      rw [T.degree_steinerSubgraph_eq x₀ S v]
      by_cases hex : ∃ x ∈ S, T.leaf x = (v : T.V)
      · exact absurd
          ((T.steinerDegree_eq_one_iff hx₀ hS2 (T.steinerVert_mem v)).mpr hex)
          (fun h => hv' (by rwa [T.degree_steinerSubgraph_eq x₀ S v]))
      · exact T.two_le_steinerDegree_of_not_mem_image hx₀ (T.steinerVert_mem v)
          (fun x hx hxz => hex ⟨x, hx, hxz⟩)
    have hne3 : (T.steinerSubgraph x₀ S).degree v ≠ 3 := by
      intro h
      rw [T.degree_steinerSubgraph_eq x₀ S v] at h
      exact hcon' (v : T.V) (T.steinerVert_mem v) h
    omega
  -- 求和（握手引理）
  have hsum : (∑ v : T.SteinerVert x₀ S, (T.steinerSubgraph x₀ S).degree v)
      = 2 * (T.steinerSubgraph x₀ S).edgeFinset.card :=
    SimpleGraph.sum_degrees_eq_twice_card_edges _
  have hE : (T.steinerSubgraph x₀ S).edgeFinset.card + 1
      = Fintype.card (T.SteinerVert x₀ S) := hTtree.card_edgeFinset
  have hLsum : L.sum (fun v => (T.steinerSubgraph x₀ S).degree v) = L.card := by
    have hc : L.sum (fun v => (T.steinerSubgraph x₀ S).degree v) = L.sum (fun _ => 1) :=
      Finset.sum_congr rfl fun v hv => by
        rw [hLeq] at hv
        exact (Finset.mem_filter.mp hv).2
    rw [hc, Finset.sum_const, smul_eq_mul, mul_one]
  have hMisum : Mi.sum (fun v => (T.steinerSubgraph x₀ S).degree v) = 2 * Mi.card := by
    have hc : Mi.sum (fun v => (T.steinerSubgraph x₀ S).degree v) = Mi.sum (fun _ => 2) :=
      Finset.sum_congr rfl fun v hv => hMi2 v (by rwa [hMieq] at hv)
    rw [hc, Finset.sum_const, smul_eq_mul]
    ring
  have hsplit : L.sum (fun v => (T.steinerSubgraph x₀ S).degree v)
      + Mi.sum (fun v => (T.steinerSubgraph x₀ S).degree v)
      = ∑ v : T.SteinerVert x₀ S, (T.steinerSubgraph x₀ S).degree v := by
    have h := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (T.SteinerVert x₀ S))
      (fun v => (T.steinerSubgraph x₀ S).degree v = 1)
      (fun v => (T.steinerSubgraph x₀ S).degree v)
    simpa only [← hLeq, ← hMieq] using h
  have hcardV : Fintype.card (T.SteinerVert x₀ S) = L.card + Mi.card := by
    have h := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (T.SteinerVert x₀ S)))
      (fun v => (T.steinerSubgraph x₀ S).degree v = 1)
    rw [Finset.card_univ] at h
    simp only [← hLeq, ← hMieq] at h
    exact h.symm
  omega

/-! ## 阶段 4：分支计数与收口 -/

/-- **删边可达性（按边表）**：walk 的边表不含 `e` ⟹ 删去 `e` 后仍可达。 -/
theorem reachable_deleteEdges_of_edges_notMem {V : Type*} {G : SimpleGraph V} {e : Sym2 V}
    {u v : V} (p : G.Walk u v) (h : e ∉ p.edges) : (G.deleteEdges {e}).Reachable u v := by
  induction p with
  | nil => exact Reachable.refl _
  | cons hadj p ih =>
    refine Reachable.trans ?_ (ih ?_)
    · refine (deleteEdges_adj.mpr ⟨hadj, ?_⟩).reachable
      intro hmem
      simp only [Set.mem_singleton_iff] at hmem
      exact h (by rw [Walk.edges_cons, hmem]; exact List.mem_cons_self ..)
    · intro hmem
      exact h (by rw [Walk.edges_cons]; exact List.mem_cons_of_mem _ hmem)

/-- **唯一路径的第一步**（`v → T.leaf x`）。 -/
noncomputable def firstStepOf (v : T.V) (x : X) : T.V :=
  ((T.existsUnique_path v (T.leaf x)).choose).getVert 1

/-- 若 `T.leaf x ≠ v`，则路径非平凡，第一步是 `v` 的邻居。 -/
theorem adj_firstStepOf {v : T.V} {x : X} (hne : T.leaf x ≠ v) :
    T.graph.Adj v (T.firstStepOf v x) := by
  have hp : ((T.existsUnique_path v (T.leaf x)).choose).IsPath :=
    (T.existsUnique_path v (T.leaf x)).choose_spec.1
  have hnil : ¬ ((T.existsUnique_path v (T.leaf x)).choose).Nil := fun h =>
    hne ((hp.nil_iff_eq.mp h).symm)
  have hpos : 0 < ((T.existsUnique_path v (T.leaf x)).choose).length :=
    Walk.not_nil_iff_lt_length.mp hnil
  have hadj := ((T.existsUnique_path v (T.leaf x)).choose).adj_getVert_succ (i := 0) hpos
  rw [Walk.getVert_zero] at hadj
  simpa [Cladogram.firstStepOf] using hadj

/-- 第一步落在 `v → T.leaf x` 的路径上。 -/
theorem firstStepOf_mem_pathVerts (v : T.V) (x : X) :
    T.firstStepOf v x ∈ T.pathVerts v (T.leaf x) := by
  have hp : ((T.existsUnique_path v (T.leaf x)).choose).IsPath :=
    (T.existsUnique_path v (T.leaf x)).choose_spec.1
  rw [T.pathVerts_eq_support_toFinset (p := (T.existsUnique_path v (T.leaf x)).choose) hp]
  exact List.mem_toFinset.mpr (Walk.getVert_mem_support _ 1)

/-- 第一步是 `T(S)` 中的顶点（`x ∈ S`，`v ∈ U`）。 -/
theorem firstStepOf_mem_steinerVerts {x₀ : X} {S : Finset X} {v : T.V}
    (hv : v ∈ T.steinerVerts x₀ S) {x : X} (hx : x ∈ S) :
    T.firstStepOf v x ∈ T.steinerVerts x₀ S :=
  T.pathVerts_subset_steinerVerts_of_mem hv (T.leaf_mem_steinerVerts hx)
    (T.firstStepOf_mem_pathVerts v x)

/-- **`x` 在边 `⟦v,z⟧` 的 `z` 侧 ⟹ 第一步就是 `z`**。 -/
theorem firstStepOf_eq_of_inSide {v z : T.V} (hadj : T.graph.Adj v z) {x : X}
    (h : T.inSide s(v, z) z (T.leaf x)) :
    T.firstStepOf v x = z := by
  classical
  obtain ⟨W⟩ := h
  have hnotv : v ∉ W.support := by
    intro hvs
    obtain ⟨W1, W2, -⟩ := Walk.mem_support_iff_exists_append.mp hvs
    have hr : (T.graph.deleteEdges {s(v, z)}).Reachable z v := ⟨W1⟩
    refine T.not_reachable_deleteEdges_of_adj hadj.symm ?_
    rw [Sym2.eq_swap]
    exact hr
  have hWt_path : ((W.mapLe (SimpleGraph.deleteEdges_le {s(v, z)})).toPath :
      T.graph.Walk z (T.leaf x)).IsPath :=
    ((W.mapLe (SimpleGraph.deleteEdges_le {s(v, z)})).toPath).isPath
  have hWt_supp : ((W.mapLe (SimpleGraph.deleteEdges_le {s(v, z)})).toPath :
      T.graph.Walk z (T.leaf x)).support ⊆ W.support := by
    intro a ha
    have h1 : a ∈ (W.mapLe (SimpleGraph.deleteEdges_le {s(v, z)})).support :=
      Walk.support_toPath_subset_support _ ha
    rwa [Walk.support_mapLe_eq_support] at h1
  have hV : (Walk.cons hadj
      (((W.mapLe (SimpleGraph.deleteEdges_le {s(v, z)})).toPath) :
        T.graph.Walk z (T.leaf x))).IsPath := by
    rw [Walk.cons_isPath_iff]
    exact ⟨hWt_path, fun hmem => hnotv (hWt_supp hmem)⟩
  show ((T.existsUnique_path v (T.leaf x)).choose).getVert 1 = z
  rw [T.existsUnique_path_choose_eq hV]
  simp only [Walk.getVert_cons_succ, Walk.getVert_zero]

/-- **第一步是 `z` ⟹ `x` 在边 `⟦v,z⟧` 的 `z` 侧**（用 `cons` 分解排除「边被走两次」）。 -/
theorem inSide_of_firstStepOf_eq {v z : T.V} {x : X} (hne : T.leaf x ≠ v)
    (hz : T.firstStepOf v x = z) : T.inSide s(v, z) z (T.leaf x) := by
  classical
  obtain ⟨u', hadj, q, hpq⟩ := Walk.exists_eq_cons_of_ne (fun h => hne h.symm)
    ((T.existsUnique_path v (T.leaf x)).choose)
  have hu' : u' = z := by
    have h := congrArg (fun w : T.graph.Walk v (T.leaf x) => w.getVert 1) hpq
    simp only [Walk.getVert_cons_succ, Walk.getVert_zero] at h
    exact h.symm.trans hz
  have hnot : s(v, u') ∉ q.edges := by
    have hp : ((T.existsUnique_path v (T.leaf x)).choose).IsPath :=
      (T.existsUnique_path v (T.leaf x)).choose_spec.1
    have ht : ((T.existsUnique_path v (T.leaf x)).choose).edges.Nodup :=
      (Walk.isTrail_def _).mp hp.isTrail
    rw [hpq, Walk.edges_cons] at ht
    exact (List.nodup_cons.mp ht).1
  have hreach : (T.graph.deleteEdges {s(v, z)}).Reachable z (T.leaf x) := by
    rw [← hu']
    exact reachable_deleteEdges_of_edges_notMem q hnot
  exact hreach

/-- ★★ **每个分支都含一个 `S` 元素**（分支计数的不变量）。

`z` 是 `v` 在 `T(S)` 中的邻居 ⟹ `z` 所在的一侧必含 `S` 的像：
取 `z ∈ P(x₀,y)`（`y ∈ S`），沿 `z → y` 或反向的 `x₀ → z` 走；
若两个方向都用到边 `⟦v,z⟧`，则 `v` 在路径 `q` 的支持集中出现两次，与 `q` 是路径矛盾。 -/
theorem exists_firstStepOf_eq {x₀ : X} {S : Finset X} {v : T.V}
    (hx₀ : x₀ ∈ S) (hS2 : 2 ≤ S.card)
    (hv3 : T.steinerDegree x₀ S v = 3) {z : T.V}
    (hz : z ∈ T.graph.neighborFinset v ∩ T.steinerVerts x₀ S) :
    ∃ x ∈ S, T.firstStepOf v x = z := by
  classical
  obtain ⟨hzadj, hzU⟩ := Finset.mem_inter.mp hz
  have hzv : z ≠ v := ((SimpleGraph.mem_neighborFinset T.graph v z).mp hzadj).ne'
  have hleaf_ne : ∀ x ∈ S, T.leaf x ≠ v := by
    intro x hx h
    have h1 : T.steinerDegree x₀ S v = 1 := by
      rw [← h]
      exact (T.steinerDegree_eq_one_iff hx₀ hS2 (T.leaf_mem_steinerVerts hx)).mpr
        ⟨x, hx, rfl⟩
    omega
  obtain ⟨y, hy, hzy⟩ := T.mem_steinerVerts.mp hzU
  let q := (T.existsUnique_path (T.leaf x₀) (T.leaf y)).choose
  have hq : q.IsPath := (T.existsUnique_path (T.leaf x₀) (T.leaf y)).choose_spec.1
  have hzq : z ∈ q.support := by
    have h := hzy
    rwa [T.pathVerts_eq_support_toFinset (p := q) hq, List.mem_toFinset] at h
  let R := q.takeUntil z hzq
  let R' := q.dropUntil z hzq
  have hsupp : R.support ++ R'.support.tail = q.support := by
    have h := congrArg (fun w : T.graph.Walk (T.leaf x₀) (T.leaf y) => w.support)
      (Walk.take_spec q hzq)
    rw [Walk.support_append] at h
    exact h
  have hnd : (R.support ++ R'.support.tail).Nodup := hsupp ▸ (Walk.isPath_def q).mp hq
  by_cases hedge : s(v, z) ∈ R'.edges
  · have h2 : s(v, z) ∉ R.edges := by
      intro hmem
      have hvR : v ∈ R.support :=
        Walk.mem_support_of_mem_edges hmem (Sym2.mem_iff.mpr (Or.inl rfl))
      have hvR' : v ∈ R'.support :=
        Walk.mem_support_of_mem_edges hedge (Sym2.mem_iff.mpr (Or.inl rfl))
      have hvR't : v ∈ R'.support.tail := by
        rcases (Walk.mem_support_iff R').mp hvR' with h | h
        · exact absurd h hzv.symm
        · exact h
      have hdisj := (List.nodup_append.mp hnd).2.2
      exact (hdisj v hvR v hvR't) rfl
    have hnot : s(v, z) ∉ R.reverse.edges := by
      intro hmem
      exact h2 (by rwa [Walk.edges_reverse, List.mem_reverse] at hmem)
    have hreach : (T.graph.deleteEdges {s(v, z)}).Reachable z (T.leaf x₀) :=
      reachable_deleteEdges_of_edges_notMem R.reverse hnot
    exact ⟨x₀, hx₀, T.firstStepOf_eq_of_inSide
      ((SimpleGraph.mem_neighborFinset T.graph v z).mp hzadj) hreach⟩
  · have hreach : (T.graph.deleteEdges {s(v, z)}).Reachable z (T.leaf y) :=
      reachable_deleteEdges_of_edges_notMem R' hedge
    exact ⟨y, hy, T.firstStepOf_eq_of_inSide
      ((SimpleGraph.mem_neighborFinset T.graph v z).mp hzadj) hreach⟩

/-- 子类型 `↥S` 上的 filter 与 `S` 上的 filter 同基数。 -/
theorem card_filter_subtype {Y : Type*} [Fintype Y] [DecidableEq Y] (S : Finset Y)
    (p : Y → Prop) [DecidablePred p] :
    (Finset.univ.filter (fun a : ↥S => p (a : Y))).card = (S.filter p).card := by
  classical
  refine Finset.card_bij (fun (a : ↥S)
      (_ : a ∈ Finset.univ.filter (fun a : ↥S => p (a : Y))) => (a : Y)) ?_ ?_ ?_
  · intro a ha
    rw [Finset.mem_filter]
    exact ⟨a.2, (Finset.mem_filter.mp ha).2⟩
  · intro a₁ _ a₂ _ h
    exact Subtype.ext h
  · intro b hb
    rw [Finset.mem_filter] at hb
    exact ⟨⟨b, hb.1⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb.2⟩, rfl⟩

/-- ★★★ **binary 树在任意 4-元集上展示一个 `2|2` split**。

取 `v ∈ T(S)` 的度 3 顶点，其三个分支各含 `S` 的一个像（`exists_firstStepOf_eq`），
于是三个分支的 `S`-计数之和 = 4、各 ≥ 1 ⟹ 某支恰含 2 个 `S` 元素；
该支对应的边在新 split 上恰给出一个 `2|2` 划分。 -/
theorem exists_displaysSplitOn_card_two {T : Cladogram.{u, v} X} (hT : T.IsBinary)
    {S : Finset X} (hS : S.card = 4) :
    ∃ q : Split ↥S, T.DisplaysSplitOn S q ∧ q.sideA.card = 2 := by
  classical
  obtain ⟨x₀, hx₀⟩ := Finset.card_pos.mp (by omega : 0 < S.card)
  have hS2 : 2 ≤ S.card := by omega
  obtain ⟨v, hvU, hv3⟩ := T.exists_steinerDegree_eq_three hT hx₀ hS
  have hleaf_ne : ∀ x ∈ S, T.leaf x ≠ v := by
    intro x hx h
    have h1 : T.steinerDegree x₀ S v = 1 := by
      rw [← h]
      exact (T.steinerDegree_eq_one_iff hx₀ hS2 (T.leaf_mem_steinerVerts hx)).mpr
        ⟨x, hx, rfl⟩
    omega
  have hcard3 : (T.graph.neighborFinset v ∩ T.steinerVerts x₀ S).card = 3 := hv3
  obtain ⟨z1, z2, z3, hz12, hz13, hz23, hzEq⟩ := Finset.card_eq_three.mp hcard3
  have hz1 : z1 ∈ T.graph.neighborFinset v ∩ T.steinerVerts x₀ S := by rw [hzEq]; simp
  have hz2 : z2 ∈ T.graph.neighborFinset v ∩ T.steinerVerts x₀ S := by rw [hzEq]; simp
  have hz3 : z3 ∈ T.graph.neighborFinset v ∩ T.steinerVerts x₀ S := by rw [hzEq]; simp
  let A1 : Finset X := S.filter fun x => T.firstStepOf v x = z1
  let A2 : Finset X := S.filter fun x => T.firstStepOf v x = z2
  let A3 : Finset X := S.filter fun x => T.firstStepOf v x = z3
  have hA1eq : A1 = S.filter (fun x => T.firstStepOf v x = z1) := rfl
  have hA2eq : A2 = S.filter (fun x => T.firstStepOf v x = z2) := rfl
  have hA3eq : A3 = S.filter (fun x => T.firstStepOf v x = z3) := rfl
  have hne1 : A1.Nonempty := by
    obtain ⟨x, hx, hstep⟩ := T.exists_firstStepOf_eq hx₀ hS2 hv3 hz1
    exact ⟨x, by rw [hA1eq, Finset.mem_filter]; exact ⟨hx, hstep⟩⟩
  have hne2 : A2.Nonempty := by
    obtain ⟨x, hx, hstep⟩ := T.exists_firstStepOf_eq hx₀ hS2 hv3 hz2
    exact ⟨x, by rw [hA2eq, Finset.mem_filter]; exact ⟨hx, hstep⟩⟩
  have hne3 : A3.Nonempty := by
    obtain ⟨x, hx, hstep⟩ := T.exists_firstStepOf_eq hx₀ hS2 hv3 hz3
    exact ⟨x, by rw [hA3eq, Finset.mem_filter]; exact ⟨hx, hstep⟩⟩
  have hdisj12 : Disjoint A1 A2 := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    rw [hA1eq, Finset.mem_filter] at hx1
    rw [hA2eq, Finset.mem_filter] at hx2
    exact hz12 (hx1.2.symm.trans hx2.2)
  have hdisj13 : Disjoint A1 A3 := by
    rw [Finset.disjoint_left]
    intro x hx1 hx3
    rw [hA1eq, Finset.mem_filter] at hx1
    rw [hA3eq, Finset.mem_filter] at hx3
    exact hz13 (hx1.2.symm.trans hx3.2)
  have hdisj23 : Disjoint A2 A3 := by
    rw [Finset.disjoint_left]
    intro x hx2 hx3
    rw [hA2eq, Finset.mem_filter] at hx2
    rw [hA3eq, Finset.mem_filter] at hx3
    exact hz23 (hx2.2.symm.trans hx3.2)
  have hcover : ∀ x ∈ S, x ∈ A1 ∨ x ∈ A2 ∨ x ∈ A3 := by
    intro x hx
    have hstep : T.firstStepOf v x ∈ T.graph.neighborFinset v ∩ T.steinerVerts x₀ S :=
      Finset.mem_inter.mpr
        ⟨(SimpleGraph.mem_neighborFinset T.graph v _).mpr (T.adj_firstStepOf (hleaf_ne x hx)),
          T.firstStepOf_mem_steinerVerts hvU hx⟩
    rw [hzEq] at hstep
    simp only [Finset.mem_insert, Finset.mem_singleton] at hstep
    rcases hstep with h | h | h
    · exact Or.inl (by rw [hA1eq, Finset.mem_filter]; exact ⟨hx, h⟩)
    · exact Or.inr (Or.inl (by rw [hA2eq, Finset.mem_filter]; exact ⟨hx, h⟩))
    · exact Or.inr (Or.inr (by rw [hA3eq, Finset.mem_filter]; exact ⟨hx, h⟩))
  have hunion : A1 ∪ A2 ∪ A3 = S := by
    ext x
    constructor
    · intro hx
      rcases Finset.mem_union.mp hx with hx' | hx3
      · rcases Finset.mem_union.mp hx' with h1 | h2
        · rw [hA1eq, Finset.mem_filter] at h1; exact h1.1
        · rw [hA2eq, Finset.mem_filter] at h2; exact h2.1
      · rw [hA3eq, Finset.mem_filter] at hx3; exact hx3.1
    · intro hx
      rcases hcover x hx with h | h | h
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl h)))
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr h)))
      · exact Finset.mem_union.mpr (Or.inr h)
  have hdisjU : Disjoint (A1 ∪ A2) A3 := by
    rw [Finset.disjoint_left]
    intro x hx hx3
    rcases Finset.mem_union.mp hx with h | h
    · exact (Finset.disjoint_left.mp hdisj13) h hx3
    · exact (Finset.disjoint_left.mp hdisj23) h hx3
  have hcard : A1.card + A2.card + A3.card = 4 := by
    calc A1.card + A2.card + A3.card
        = (A1 ∪ A2).card + A3.card := by rw [Finset.card_union_of_disjoint hdisj12]
      _ = (A1 ∪ A2 ∪ A3).card := by rw [Finset.card_union_of_disjoint hdisjU]
      _ = S.card := by rw [hunion]
      _ = 4 := hS
  have htwo : A1.card = 2 ∨ A2.card = 2 ∨ A3.card = 2 := by
    have h1 : 1 ≤ A1.card := Finset.card_pos.mpr hne1
    have h2 : 1 ≤ A2.card := Finset.card_pos.mpr hne2
    have h3 : 1 ≤ A3.card := Finset.card_pos.mpr hne3
    by_cases h : A1.card = 2
    · exact Or.inl h
    · by_cases h' : A2.card = 2
      · exact Or.inr (Or.inl h')
      · exact Or.inr (Or.inr (by omega))
  have key : ∀ z ∈ T.graph.neighborFinset v ∩ T.steinerVerts x₀ S,
      (S.filter fun x => T.firstStepOf v x = z).card = 2 →
      ∃ q : Split ↥S, T.DisplaysSplitOn S q ∧ q.sideA.card = 2 := by
    intro z hz hzc
    have hzadj : T.graph.Adj v z :=
      (SimpleGraph.mem_neighborFinset T.graph v z).mp (Finset.mem_inter.mp hz).1
    have hfiber_eq : (S ∩ T.sideLeaves s(v, z) z)
        = S.filter (fun x => T.firstStepOf v x = z) := by
      ext x
      rw [Finset.mem_inter, Finset.mem_filter]
      constructor
      · rintro ⟨hxS, hsl⟩
        exact ⟨hxS, T.firstStepOf_eq_of_inSide hzadj
          (T.mem_sideLeaves_iff_inSide.mp hsl)⟩
      · rintro ⟨hxS, hstep⟩
        exact ⟨hxS, T.mem_sideLeaves_iff_inSide.mpr
          (T.inSide_of_firstStepOf_eq (hleaf_ne x hxS) hstep)⟩
    have hinter : (S ∩ T.sideLeaves s(v, z) z).card = 2 := by
      rw [hfiber_eq]; exact hzc
    obtain ⟨x₂, hx₂⟩ := Finset.card_pos.mp (by omega : 0 < (S ∩ T.sideLeaves s(v, z) z).card)
    have hx₂S : x₂ ∈ S := (Finset.mem_inter.mp hx₂).1
    have hx₂side : x₂ ∈ T.sideLeaves s(v, z) z := (Finset.mem_inter.mp hx₂).2
    have hx₁ : ∃ x ∈ S, x ∉ T.sideLeaves s(v, z) z := by
      by_contra hcon
      have hsub : S ⊆ T.sideLeaves s(v, z) z := by
        intro x hx
        by_contra hxnot
        exact hcon ⟨x, hx, hxnot⟩
      have hEq : S ∩ T.sideLeaves s(v, z) z = S := Finset.inter_eq_left.mpr hsub
      rw [hEq, hS] at hinter
      omega
    obtain ⟨x₁, hx₁S, hx₁not⟩ := hx₁
    have hA : (T.sideLeaves s(v, z) z).Nonempty := ⟨x₂, hx₂side⟩
    have hB : (Finset.univ \ T.sideLeaves s(v, z) z).Nonempty :=
      ⟨x₁, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hx₁not⟩⟩
    let s₀ : Split X := T.splitOfEdge s(v, z) z hA hB
    have hs₀ : s₀.sideA = T.sideLeaves s(v, z) z := rfl
    have hIsSplit : T.IsSplitOf s₀ := ⟨v, z, hzadj, z, rfl⟩
    have hA' : (s₀.restrictSide S 0).Nonempty :=
      ⟨⟨x₂, hx₂S⟩, by
        simp only [Split.restrictSide, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [show s₀.parts 0 = T.sideLeaves s(v, z) z from hs₀]
        exact hx₂side⟩
    have hB' : (s₀.restrictSide S 1).Nonempty :=
      ⟨⟨x₁, hx₁S⟩, by
        simp only [Split.restrictSide, Finset.mem_filter, Finset.mem_univ, true_and]
        show (x₁ : X) ∈ s₀.parts 1
        show (x₁ : X) ∈ s₀.sideB
        rw [Split.sideB_eq_compl, show s₀.sideA = T.sideLeaves s(v, z) z from hs₀,
          Finset.mem_compl]
        exact hx₁not⟩
    refine ⟨s₀.restrict S hA' hB', ⟨s₀, hIsSplit, ?_⟩, ?_⟩
    · intro x
      show x ∈ (s₀.restrict S hA' hB').sideA ↔ (x : X) ∈ s₀.sideA
      simp [Split.restrict, Split.restrictSide, Split.sideA]
    · show (s₀.restrict S hA' hB').sideA.card = 2
      have hqc : (s₀.restrict S hA' hB').sideA
          = Finset.univ.filter (fun a : ↥S => (a : X) ∈ s₀.sideA) := rfl
      rw [hqc, card_filter_subtype S (fun x => x ∈ s₀.sideA)]
      have h2 : S.filter (fun x => x ∈ s₀.sideA) = S ∩ T.sideLeaves s(v, z) z := by
        rw [hs₀]
        ext x
        simp [Finset.mem_filter, Finset.mem_inter]
      rw [h2]
      exact hinter
  rcases htwo with h | h | h
  · exact key z1 hz1 (by rw [← hA1eq]; exact h)
  · exact key z2 hz2 (by rw [← hA2eq]; exact h)
  · exact key z3 hz3 (by rw [← hA3eq]; exact h)

end Cladogram

/-- ★★★ **binary 树给出一个 `QuartetTree`** —— 这证明 `QuartetTree`
（`Phylo/Stat/MSC.lean`，T0.6 给它加了 `q_card : sideA.card = 2` 字段）**不是空类型**，
即该字段**可被赋值**：本项目「#1 风险类（空真）」的收尾。

`q S hS` 取 ★★★ `Cladogram.exists_displaysSplitOn_card_two` 的存在性见证；
由 ★★★ `Cladogram.displaysSplitOn_unique` 知它在模 `swap` 下**唯一**，
故这个选择与文献的「树的 quartet 系统」一致。 -/
noncomputable def QuartetTree.ofBinary {T : Cladogram.{u, v} X} (hT : T.IsBinary) :
    QuartetTree X where
  tree := T
  q := fun _ hS => (T.exists_displaysSplitOn_card_two hT hS).choose
  q_card := fun _ hS => (T.exists_displaysSplitOn_card_two hT hS).choose_spec.2
  displays := fun _ hS => (T.exists_displaysSplitOn_card_two hT hS).choose_spec.1
