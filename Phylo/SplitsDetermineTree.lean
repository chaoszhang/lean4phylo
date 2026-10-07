/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.Laminar
import Phylo.SplitsMaximal
import Phylo.QuartetInhabitation

/-!
# `Phylo.SplitsDetermineTree` —— **树由 split 系统决定**（Semple & Steel §3.8 的同构版）

**主定理**（`|X| ≤ 2` 的退化情形由 `Phylo/SplitsDetermineTreeBase.lean` 负责）：

```
theorem Cladogram.iso_of_isSplitOf_iff {X : Type u} [Fintype X] [DecidableEq X]
    {T T' : Cladogram.{u, v} X} (hcard : 3 ≤ Fintype.card X)
    (h : ∀ s : Split X, T.IsSplitOf s ↔ T'.IsSplitOf s) : Nonempty (Iso T T')
```

**路线**（固定叶 `x₀`，`C v := Cluster T x₀ v`，`p v := p T x₀ v`；**不碰 `Laminar`**）：

1. **A1** `Cluster_injective`：`C` 在 `T.V \ {T.leaf x₀}` 上单射；
2. **A2** `two_le_card_Cluster`：`¬ IsLeaf v ⟹ 2 ≤ #(C v)`（T2 `two_le_card_sideLeaves` 的直接推论）；
3. **A3** `adj_iff_parent`：`Adj v w ↔ p v = w ∨ p w = v`；
4. **核心** `Cluster_subset_iff`：`C v ⊆ C u ↔ u ∈ pathVerts v (T.leaf x₀)`（「簇包含 ⟺ 祖先」）；
5. **A4** `Cluster_ssubset_parent`：`C (p v)` 是 `C v` 在簇族 `{C u}` 中的**最小真超集**
   （由 4 的两个方向 + 路径尾巴引理给出）；
6. **B**：相同 split 系统 ⟹ `exists_cluster_eq` 给出搬运 `psi`（`Cluster_psi` 保簇），
  `psi_injective` / `psi_surjective` 说明它是双射，`psi_parent` 证明它**保父亲**
  （两棵树各自的 A4 最小性夹出相等，再用 A1 收口），
  `adj_iff_adj_psi` 由 A3 + 保父亲给出**保邻接**，最后由 `RelIso.mk` 装配出 `Iso T T'`。

## 完成清单（全部为完整证明：无占位符、无新公理）

* 基础：`p`、`adj_p`、`inSide_p`、`Cluster`、`mem_Cluster`、`Cluster_eq_sideLeaves`、`notMem_Cluster_x₀`
* A1–A4：`Cluster_injective`、`two_le_card_Cluster`、`Cluster_leaf`、`Cluster_nonempty`、
  `adj_iff_parent`、`Cluster_subset_iff`、`Cluster_ssubset_parent`
* 路径工具：`mem_pathVerts_of_mem_Cluster`、`mem_Cluster_of_mem_pathVerts`、
  `pathVerts_mem_trans`、`pathVerts_eq_insert_firstStepOf`
* 根：`existsUnique_adj_leaf`、`rootNb`、`adj_rootNb`、`eq_rootNb_of_adj`、`p_rootNb`、`Cluster_rootNb`
* 搬运：`exists_cluster_eq`、`psi`、`psi_leaf₀`、`psi_ne_leaf₀`、`Cluster_psi`、`psi_leaf`、
  `psi_injective`、`psi_surjective`、`psi_rootNb`、`psi_parent`、`adj_iff_adj_psi`
* 主定理：`Cladogram.iso_of_isSplitOf_iff`

（退化基数在 `Phylo/SplitsDetermineTreeBase.lean`：`Cladogram.iso_of_card_le_two`。）
-/

namespace Phylo

open Classical
open SimpleGraph

universe u v

variable {X : Type*} [Fintype X] [DecidableEq X]

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

/-! ## 第 1 层：`p` 与 `Cluster` -/

/-- `v` 通向叶 `x₀` 的第一步（**只对 `T.leaf x₀ ≠ v` 使用**）。 -/
noncomputable def p (T : Cladogram X) (x₀ : X) (v : T.V) : T.V := T.firstStepOf v x₀

theorem adj_p {T : Cladogram X} {x₀ : X} {v : T.V} (hv : T.leaf x₀ ≠ v) :
    T.graph.Adj v (p T x₀ v) := T.adj_firstStepOf hv

/-- `p T x₀ v` 所在的一侧含 `T.leaf x₀`。 -/
theorem inSide_p {T : Cladogram X} {x₀ : X} {v : T.V} (hv : T.leaf x₀ ≠ v) :
    T.inSide s(v, p T x₀ v) (p T x₀ v) (T.leaf x₀) :=
  T.inSide_of_firstStepOf_eq hv rfl

/-- **`v` 的 cluster**：删去边 `⟦v, p T x₀ v⟧` 后与 `v` 同侧的叶集（**避开 `T.leaf x₀`**）。 -/
noncomputable def Cluster (T : Cladogram X) (x₀ : X) (v : T.V) : Finset X :=
  Finset.univ.filter fun x => (T.graph.deleteEdges {s(v, p T x₀ v)}).Reachable (T.leaf x) v

theorem mem_Cluster {T : Cladogram X} {x₀ : X} {v : T.V} {x : X} :
    x ∈ Cluster T x₀ v ↔ (T.graph.deleteEdges {s(v, p T x₀ v)}).Reachable (T.leaf x) v := by
  classical
  simp [Cluster]

/-- **`Cluster` 就是 `sideLeaves`**（定义式相等）—— 故 `Cluster T x₀ v` 是 `Σ(T)` 中
一条 split 的「避开 `x₀`」的一侧。 -/
theorem Cluster_eq_sideLeaves {T : Cladogram X} {x₀ : X} {v : T.V} :
    Cluster T x₀ v = T.sideLeaves s(v, p T x₀ v) v := by
  classical
  ext x
  simp only [mem_Cluster, Cladogram.mem_sideLeaves]

/-- **`x₀ ∉ Cluster T x₀ v`**（cluster 定义即「避开 `x₀` 的那一侧」）。 -/
theorem notMem_Cluster_x₀ {T : Cladogram X} {x₀ : X} {v : T.V} (hv : T.leaf x₀ ≠ v) :
    x₀ ∉ Cluster T x₀ v := by
  classical
  intro hx
  rw [mem_Cluster] at hx
  have hreach : (T.graph.deleteEdges {s(v, p T x₀ v)}).Reachable v (p T x₀ v) := by
    have h1 : (T.graph.deleteEdges {s(v, p T x₀ v)}).Reachable (T.leaf x₀) v := hx
    have h2 : (T.graph.deleteEdges {s(v, p T x₀ v)}).Reachable v (T.leaf x₀) := h1.symm
    have h3 : (T.graph.deleteEdges {s(v, p T x₀ v)}).Reachable (T.leaf x₀) (p T x₀ v) :=
      (inSide_p (T := T) (x₀ := x₀) (v := v) hv).symm
    exact h2.trans h3
  exact T.not_reachable_deleteEdges_of_adj (adj_p hv) hreach

/-! ## A2：非叶顶点的 cluster 至少 2 片叶 -/

/-- **A2**：`v` 非叶 ⟹ `2 ≤ #(C v)`。

`C v = sideLeaves ⟦v, p v⟧ v`，对端点 `v`（`degree v ≠ 1`）用 T2
`Cladogram.two_le_card_sideLeaves`。 -/
theorem two_le_card_Cluster {T : Cladogram X} {x₀ : X} {v : T.V} (hv : T.leaf x₀ ≠ v)
    (hnl : ¬ T.IsLeaf v) : 2 ≤ (Cluster T x₀ v).card := by
  have hdeg : T.graph.degree v ≠ 1 := fun h => hnl ((T.isLeaf_iff_degree_eq_one v).mpr h)
  simpa [Cluster_eq_sideLeaves] using T.two_le_card_sideLeaves (adj_p hv) hdeg

/-- **叶的 cluster 是单点**（`x ≠ x₀`）：`C (T.leaf x) = {x}`。

删去叶的唯一边后该叶孤立，故 `sideLeaves` 退化为 `{x}`。 -/
theorem Cluster_leaf {T : Cladogram X} {x₀ x : X} (hx : x₀ ≠ x) :
    Cluster T x₀ (T.leaf x) = {x} := by
  have hne : T.leaf x₀ ≠ T.leaf x := fun h => hx (T.leaf.injective h)
  rw [Cluster_eq_sideLeaves]
  exact T.sideLeaves_leaf_edge (adj_p hne)

/-- `C v` 非空（`v ≠ T.leaf x₀`）。 -/
theorem Cluster_nonempty {T : Cladogram X} {x₀ : X} {v : T.V} (hv : T.leaf x₀ ≠ v) :
    (Cluster T x₀ v).Nonempty := by
  by_cases hl : T.IsLeaf v
  · obtain ⟨x, rfl⟩ := hl
    have hx : x₀ ≠ x := fun h => hv (by rw [h])
    rw [Cluster_leaf hx]
    exact Finset.singleton_nonempty x
  · exact Finset.card_pos.mp (by have := two_le_card_Cluster hv hl; omega)

/-! ## A1：`Cluster` 在非 `x₀` 叶的顶点上单射 -/

/-- **A1**：`C v = C w ⟹ v = w`（`v, w ≠ T.leaf x₀`）。

`C v = sideLeaves ⟦v,p v⟧ v`，故由 ★★★ `Cladogram.eq_of_sideLeaves_eq` 得两条边相等；
若 `v = p w`（另一支），则 `v` 与 `w` 在 `T - ⟦v,w⟧` 中经 `T.leaf x₀` 相连，
与「每条边都是桥」矛盾。 -/
theorem Cluster_injective {T : Cladogram X} {x₀ : X} {v w : T.V}
    (hv : T.leaf x₀ ≠ v) (hw : T.leaf x₀ ≠ w) (h : Cluster T x₀ v = Cluster T x₀ w) :
    v = w := by
  have hside : T.sideLeaves s(v, p T x₀ v) v = T.sideLeaves s(w, p T x₀ w) w := by
    rw [← Cluster_eq_sideLeaves (T := T) (x₀ := x₀) (v := v),
      ← Cluster_eq_sideLeaves (T := T) (x₀ := x₀) (v := w)]
    exact h
  have hedge : s(v, p T x₀ v) = s(w, p T x₀ w) :=
    T.eq_of_sideLeaves_eq (adj_p hv) (adj_p hw) hside
  rcases Sym2.eq_iff.mp hedge with ⟨h1, -⟩ | ⟨h1, h2⟩
  · exact h1
  · exfalso
    have hw_side : T.inSide s(v, w) w (T.leaf x₀) := by
      have hh := inSide_p (T := T) (x₀ := x₀) (v := v) hv
      rwa [h2] at hh
    have hv_side : T.inSide s(v, w) v (T.leaf x₀) := by
      have hh := inSide_p (T := T) (x₀ := x₀) (v := w) hw
      rw [← h1] at hh
      exact Sym2.eq_swap ▸ hh
    have hbridge := T.not_reachable_deleteEdges_of_adj (adj_p hv)
    rw [h2] at hbridge
    exact hbridge (hv_side.trans hw_side.symm)

/-! ## A3：相邻 ⟺ 一个是另一个朝 `x₀` 的父亲 -/

/-- **A3**：`v, w ≠ T.leaf x₀` 时，`Adj v w ↔ p v = w ∨ p w = v`。

`→`：`T.leaf x₀` 落在删去 `⟦v,w⟧` 后两个分量之一；若它在 `w` 侧，
则 `p v = w`（`firstStepOf_eq_of_inSide`），否则 `p w = v`。
`←`：`adj_p`。 -/
theorem adj_iff_parent {T : Cladogram X} {x₀ : X} {v w : T.V}
    (hv : T.leaf x₀ ≠ v) (hw : T.leaf x₀ ≠ w) :
    T.graph.Adj v w ↔ p T x₀ v = w ∨ p T x₀ w = v := by
  constructor
  · intro hab
    rcases T.inSide_or_inSide hab (x := T.leaf x₀) with h | h
    · refine Or.inr (T.firstStepOf_eq_of_inSide hab.symm ?_)
      exact (T.inSide_comm s(w, v) (T.leaf x₀) v).mp (Sym2.eq_swap ▸ h)
    · refine Or.inl (T.firstStepOf_eq_of_inSide hab ?_)
      exact (T.inSide_comm s(v, w) (T.leaf x₀) w).mp h
  · rintro (h | h)
    · have hh := adj_p (T := T) (x₀ := x₀) (v := v) hv
      rw [h] at hh
      exact hh
    · have hh := adj_p (T := T) (x₀ := x₀) (v := w) hw
      rw [h] at hh
      exact hh.symm

/-! ## 路径 ↔ cluster：`y ∈ C z ↔ z ∈ pathVerts (T.leaf y) (T.leaf x₀)` -/

/-- `y ∈ C z` ⟹ `z` 在 `T.leaf y → T.leaf x₀` 的唯一路径上。

`T.leaf y` 与 `T.leaf x₀` 分居 `T - ⟦z,p z⟧` 两侧，故连接二者的 walk 必用那条边
（`Cladogram.mem_pair_of_mem_sideVertices`），边的 `z` 端在 walk 上。 -/
theorem mem_pathVerts_of_mem_Cluster {T : Cladogram X} {x₀ : X} {z : T.V}
    (hz : T.leaf x₀ ≠ z) {y : X} (hy : y ∈ Cluster T x₀ z) :
    z ∈ T.pathVerts (T.leaf y) (T.leaf x₀) := by
  have hzD : T.leaf y ∈ T.sideVertices s(z, p T x₀ z) z := by
    rw [T.mem_sideVertices]
    exact mem_Cluster.mp hy
  have hx₀D : T.leaf x₀ ∉ T.sideVertices s(z, p T x₀ z) z := by
    rw [T.mem_sideVertices]
    exact fun hr => notMem_Cluster_x₀ (T := T) (x₀ := x₀) (v := z) hz (mem_Cluster.mpr hr)
  have hmem : z ∈ ((T.existsUnique_path (T.leaf x₀) (T.leaf y)).choose).support :=
    T.mem_pair_of_mem_sideVertices (e := s(z, p T x₀ z)) (u := z) (z := T.leaf y)
      (w := T.leaf x₀) hzD hx₀D ((T.existsUnique_path (T.leaf x₀) (T.leaf y)).choose)
      (v := z) (Sym2.mem_iff.mpr (Or.inl rfl))
  rw [T.pathVerts_comm]
  exact List.mem_toFinset.mpr hmem

/-- `z` 在 `T.leaf y → T.leaf x₀` 的唯一路径上 ⟹ `y ∈ C z`。

反证：若 `T.leaf y ∉ C z`，则 `T.leaf y` 与 `T.leaf x₀` 都落在 `T - ⟦z,p z⟧` 的
`p z` 侧，故存在一条**不用**该边的 walk `W : T.leaf y → T.leaf x₀`；
`pathVerts` 落在 `W.support` 里而 `z ∉ W.support`（否则 `z` 与该 walk 同侧，与假设矛盾）。 -/
theorem mem_Cluster_of_mem_pathVerts {T : Cladogram X} {x₀ : X} {z : T.V}
    (hz : T.leaf x₀ ≠ z) {y : X} (hy : z ∈ T.pathVerts (T.leaf y) (T.leaf x₀)) :
    y ∈ Cluster T x₀ z := by
  by_contra hcon
  have hy_nr : ¬ (T.graph.deleteEdges {s(z, p T x₀ z)}).Reachable (T.leaf y) z :=
    fun hr => hcon (mem_Cluster.mpr hr)
  have hx_nr : ¬ (T.graph.deleteEdges {s(z, p T x₀ z)}).Reachable (T.leaf x₀) z :=
    fun hr => notMem_Cluster_x₀ (T := T) (x₀ := x₀) (v := z) hz (mem_Cluster.mpr hr)
  have hpy : (T.graph.deleteEdges {s(z, p T x₀ z)}).Reachable (T.leaf y) (p T x₀ z) := by
    rcases T.inSide_or_inSide (adj_p hz) (x := T.leaf y) with h | h
    · exact absurd h hy_nr
    · exact h
  have hpx : (T.graph.deleteEdges {s(z, p T x₀ z)}).Reachable (T.leaf x₀) (p T x₀ z) := by
    rcases T.inSide_or_inSide (adj_p hz) (x := T.leaf x₀) with h | h
    · exact absurd h hx_nr
    · exact h
  obtain ⟨W₀⟩ := hpy.trans hpx.symm
  have hsub := T.pathVerts_subset_support_toFinset
    (W₀.mapLe (deleteEdges_le {s(z, p T x₀ z)}))
  rw [SimpleGraph.Walk.support_mapLe_eq_support] at hsub
  have hmem : z ∈ W₀.support := List.mem_toFinset.mp (hsub hy)
  exact hy_nr (SimpleGraph.reachable_of_mem_support W₀ hmem)

/-- **路径的中转性**：`c ∈ path(a,b)`、`d ∈ path(c,b)` ⟹ `d ∈ path(a,b)`。 -/
theorem pathVerts_mem_trans {T : Cladogram X} {a b c d : T.V}
    (hac : c ∈ T.pathVerts a b) (hcd : d ∈ T.pathVerts c b) : d ∈ T.pathVerts a b := by
  have h1 : d ∈ T.pathVerts b c := by rwa [T.pathVerts_comm] at hcd
  have h2 : c ∈ T.pathVerts b a := by rwa [T.pathVerts_comm] at hac
  rw [T.pathVerts_comm]
  exact T.pathVerts_subset_of_mem_pathVerts h2 h1

/-- 由 `p v` 出发的路径去掉 `v` 就是 `v` 路径的尾巴：
`pathVerts v x₀ = insert v (pathVerts (p v) x₀)`。 -/
theorem pathVerts_eq_insert_firstStepOf {T : Cladogram X} {x₀ : X} {v : T.V}
    (hv : T.leaf x₀ ≠ v) :
    T.pathVerts v (T.leaf x₀) = insert v (T.pathVerts (p T x₀ v) (T.leaf x₀)) := by
  have hnot : v ∉ T.pathVerts (p T x₀ v) (T.leaf x₀) := by
    intro hmem
    obtain ⟨W₀⟩ := inSide_p (T := T) (x₀ := x₀) (v := v) hv
    have hsub := T.pathVerts_subset_support_toFinset
      (W₀.mapLe (deleteEdges_le {s(v, p T x₀ v)}))
    rw [SimpleGraph.Walk.support_mapLe_eq_support] at hsub
    exact T.not_reachable_deleteEdges_of_adj (adj_p hv)
      (SimpleGraph.reachable_of_mem_support W₀ (List.mem_toFinset.mp (hsub hmem))).symm
  have hpath : (SimpleGraph.Walk.cons (adj_p hv)
      ((T.existsUnique_path (p T x₀ v) (T.leaf x₀)).choose)).IsPath := by
    rw [SimpleGraph.Walk.cons_isPath_iff]
    exact ⟨(T.existsUnique_path (p T x₀ v) (T.leaf x₀)).choose_spec.1,
      fun h => hnot (List.mem_toFinset.mpr h)⟩
  have key : T.pathVerts v (T.leaf x₀)
      = (SimpleGraph.Walk.cons (adj_p hv)
          ((T.existsUnique_path (p T x₀ v) (T.leaf x₀)).choose)).support.toFinset :=
    T.pathVerts_eq_support_toFinset hpath
  rw [key, SimpleGraph.Walk.support_cons, List.toFinset_cons]
  rfl

/-- **核心引理**：`C v ⊆ C u ↔ u ∈ pathVerts v (T.leaf x₀)`（「簇包含 ⟺ 祖先」。

`→`：`subset_of_preconnected_of_leaf_subset'` 把叶包含升级为**顶点集包含**
`D v ⊆ D u`；于是 `v ∈ D u`，而 `v`、`T.leaf x₀` 分居 `T - ⟦u,pu⟧` 两侧，
故 `u` 在 `v → x₀` 的唯一路径上（`mem_pair_of_mem_sideVertices`）。
`←`：路径中转 + 两侧的「路径 ↔ cluster」引理。 -/
theorem Cluster_subset_iff {T : Cladogram X} {x₀ : X} {u v : T.V}
    (hu : T.leaf x₀ ≠ u) (hv : T.leaf x₀ ≠ v) :
    Cluster T x₀ v ⊆ Cluster T x₀ u ↔ u ∈ T.pathVerts v (T.leaf x₀) := by
  constructor
  · intro hsub
    have hD : T.sideVertices s(v, p T x₀ v) v ⊆ T.sideVertices s(u, p T x₀ u) u :=
      T.subset_of_preconnected_of_leaf_subset' (U := T.sideVertices s(v, p T x₀ v) v)
        (W := T.sideVertices s(u, p T x₀ u) u) (adj_p hv) rfl
        (T.preconnected_induce_sideVertices (e := s(u, p T x₀ u)) (u := u))
        (fun x hx => by
          rw [T.mem_sideVertices] at hx ⊢
          exact mem_Cluster.mp (hsub (mem_Cluster.mpr hx)))
    have hvu : v ∈ T.sideVertices s(u, p T x₀ u) u := hD (T.self_mem_sideVertices _ _)
    have hx₀D : T.leaf x₀ ∉ T.sideVertices s(u, p T x₀ u) u := by
      rw [T.mem_sideVertices]
      exact fun hr => notMem_Cluster_x₀ hu (mem_Cluster.mpr hr)
    have hmem : u ∈ ((T.existsUnique_path (T.leaf x₀) v).choose).support :=
      T.mem_pair_of_mem_sideVertices (e := s(u, p T x₀ u)) (u := u) (z := v) (w := T.leaf x₀)
        hvu hx₀D ((T.existsUnique_path (T.leaf x₀) v).choose) (v := u)
        (Sym2.mem_iff.mpr (Or.inl rfl))
    rw [T.pathVerts_comm]
    exact List.mem_toFinset.mpr hmem
  · intro huv y hy
    exact mem_Cluster_of_mem_pathVerts hu
      (pathVerts_mem_trans (mem_pathVerts_of_mem_Cluster hv hy) huv)

/-! ## A4：父亲的 cluster 是最小真超集 -/

/-- **A4**：设 `p v ≠ T.leaf x₀`（`v` 不是「根」）。则 `C (p v)` 是 `C v` 在簇族
`{C u}` 中的**最小真超集**：

* `C v ⊊ C (p v)`（包含由核心引理，真包含由 A1 单射性）；
* `C v ⊊ C u ⟹ C (p v) ⊆ C u`（由核心引理两方向 + 路径尾巴引理）。 -/
theorem Cluster_ssubset_parent {T : Cladogram X} {x₀ : X} {v : T.V}
    (hv : T.leaf x₀ ≠ v) (hpv : T.leaf x₀ ≠ p T x₀ v) :
    Cluster T x₀ v ⊂ Cluster T x₀ (p T x₀ v) ∧
      ∀ u : T.V, T.leaf x₀ ≠ u → Cluster T x₀ v ⊂ Cluster T x₀ u →
        Cluster T x₀ (p T x₀ v) ⊆ Cluster T x₀ u := by
  have hsub : Cluster T x₀ v ⊆ Cluster T x₀ (p T x₀ v) :=
    (Cluster_subset_iff (u := p T x₀ v) (v := v) hpv hv).mpr
      (T.firstStepOf_mem_pathVerts v x₀)
  have hne : Cluster T x₀ v ≠ Cluster T x₀ (p T x₀ v) := fun heq =>
    (adj_p hv).ne (Cluster_injective hv hpv heq)
  refine ⟨Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩, ?_⟩
  intro u hu hss
  obtain ⟨hsubvu, hnevu⟩ := Finset.ssubset_iff_subset_ne.mp hss
  have huv : u ∈ T.pathVerts v (T.leaf x₀) := (Cluster_subset_iff (u := u) (v := v) hu hv).mp hsubvu
  have huv' : u ≠ v := fun h => hnevu (by rw [h])
  have hmem : u ∈ insert v (T.pathVerts (p T x₀ v) (T.leaf x₀)) := by
    rw [← pathVerts_eq_insert_firstStepOf hv]
    exact huv
  rcases Finset.mem_insert.mp hmem with h | h
  · exact absurd h huv'
  · exact (Cluster_subset_iff (u := u) (v := p T x₀ v) hu hpv).mpr h

/-! ## 根（`x₀` 叶的唯一邻居） -/

/-- 叶 `T.leaf x₀` 的邻居唯一（度 1 ⟹ `∃!`）。 -/
theorem existsUnique_adj_leaf (T : Cladogram X) (x₀ : X) :
    ∃! r : T.V, T.graph.Adj (T.leaf x₀) r :=
  SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp
    ((T.isLeaf_iff_degree_eq_one (T.leaf x₀)).mp ⟨x₀, rfl⟩)

/-- 叶 `T.leaf x₀` 的唯一邻居（度 1 ⟹ 邻居唯一）。 -/
noncomputable def rootNb (T : Cladogram X) (x₀ : X) : T.V :=
  Classical.choose (existsUnique_adj_leaf T x₀)

theorem adj_rootNb (T : Cladogram X) (x₀ : X) :
    T.graph.Adj (T.leaf x₀) (rootNb T x₀) :=
  (Classical.choose_spec (existsUnique_adj_leaf T x₀)).1

/-- 叶 `T.leaf x₀` 的任一邻居都等于 `rootNb T x₀`。 -/
theorem eq_rootNb_of_adj {T : Cladogram X} {x₀ : X} {y : T.V}
    (hy : T.graph.Adj (T.leaf x₀) y) : y = rootNb T x₀ :=
  (Classical.choose_spec (existsUnique_adj_leaf T x₀)).2 y hy

/-- `rootNb` 朝 `x₀` 的第一步就是 `T.leaf x₀`。 -/
theorem p_rootNb (T : Cladogram X) (x₀ : X) : p T x₀ (rootNb T x₀) = T.leaf x₀ :=
  T.firstStepOf_eq_of_inSide (adj_rootNb T x₀).symm
    (T.inSide_self s(rootNb T x₀, T.leaf x₀) (T.leaf x₀))

/-- **`rootNb` 的 cluster 是全集去掉 `x₀`**。 -/
theorem Cluster_rootNb {T : Cladogram X} {x₀ : X} :
    Cluster T x₀ (rootNb T x₀) = Finset.univ \ {x₀} := by
  have h2 : T.sideLeaves s(rootNb T x₀, T.leaf x₀) (T.leaf x₀) = {x₀} :=
    Sym2.eq_swap ▸ T.sideLeaves_leaf_edge (adj_rootNb T x₀)
  have hc := T.sideLeaves_compl_adj (adj_rootNb T x₀).symm
  rw [Cluster_eq_sideLeaves, p_rootNb]
  rw [show T.sideLeaves s(rootNb T x₀, T.leaf x₀) (rootNb T x₀)
      = (T.sideLeaves s(rootNb T x₀, T.leaf x₀) (T.leaf x₀))ᶜ from by rw [hc, compl_compl],
    h2, Finset.compl_eq_univ_sdiff]

/-! ## 阶段 B：搬运簇族 -/

/-- **搬运的存在性**：相同 split 系统 ⟹ `T` 的每个簇都在 `T'` 中实现，
且实现顶点不是 `T'.leaf x₀`。

取 `w ≠ T.leaf x₀`，`C w` 是 `T` 的一条边侧 ⟹ 给出 `splitOfEdge`；
由 `h` 它也是 `T'` 的 split，即 `T'` 的某条边 `⟦a,b⟧` 与端点 `u₀`。
`x₀ ∉ C w` 说明 `x₀` 落在另一侧，于是 `u₀` 与 `⟦a,b⟧` 的「远离 `x₀`」端点同侧；
该端点 `u` 满足 `p' u` 指向另一个端点，故 `C' u = C w`。 -/
theorem exists_cluster_eq {T T' : Cladogram X} {x₀ : X}
    (hmatch : ∀ s : Split X, T.IsSplitOf s ↔ T'.IsSplitOf s)
    {w : T.V} (hw : T.leaf x₀ ≠ w) :
    ∃ u : T'.V, T'.leaf x₀ ≠ u ∧ Cluster T' x₀ u = Cluster T x₀ w := by
  classical
  have hAne : (Cluster T x₀ w).Nonempty := Cluster_nonempty hw
  have hBne : (Finset.univ \ Cluster T x₀ w).Nonempty := by
    rw [Cluster_eq_sideLeaves]
    exact T.sideLeaves_sdiff_nonempty (adj_p hw)
  let sp : Split X := T.splitOfEdge s(w, p T x₀ w) w hAne hBne
  have hsp : sp.sideA = Cluster T x₀ w := by
    show T.sideLeaves s(w, p T x₀ w) w = Cluster T x₀ w
    rw [Cluster_eq_sideLeaves]
  have hsplit : T.IsSplitOf sp := ⟨w, p T x₀ w, adj_p hw, w, hsp⟩
  obtain ⟨a, b, hab, u₀, hu₀⟩ := (hmatch sp).mp hsplit
  have hBeq : T'.sideLeaves s(a, b) u₀ = Cluster T x₀ w := hu₀.symm.trans hsp
  have hx₀A : x₀ ∉ Cluster T x₀ w := notMem_Cluster_x₀ hw
  have hx₀u₀ : ¬ (T'.graph.deleteEdges {s(a, b)}).Reachable (T'.leaf x₀) u₀ :=
    fun hr => hx₀A (hBeq ▸ T'.mem_sideLeaves.mpr hr)
  rcases T'.inSide_or_inSide hab (x := T'.leaf x₀) with hxa | hxb
  · have hu₀b : T'.inSide s(a, b) u₀ b := by
      rcases T'.inSide_or_inSide hab (x := u₀) with h | h
      · exact absurd (hxa.trans h.symm) hx₀u₀
      · exact h
    have hpb : p T' x₀ b = a :=
      T'.firstStepOf_eq_of_inSide hab.symm (Sym2.eq_swap ▸ hxa.symm)
    have hBb : T'.sideLeaves s(a, b) b = Cluster T x₀ w :=
      (T'.sideLeaves_eq_of_inSide hu₀b).symm.trans hBeq
    refine ⟨b, fun hb => hx₀A (hBb ▸ (hb ▸ T'.mem_sideLeaves_self s(a, b) x₀)), ?_⟩
    rw [Cluster_eq_sideLeaves, hpb, Sym2.eq_swap]
    exact hBb
  · have hu₀a : T'.inSide s(a, b) u₀ a := by
      rcases T'.inSide_or_inSide hab (x := u₀) with h | h
      · exact h
      · exact absurd (hxb.trans h.symm) hx₀u₀
    have hpa : p T' x₀ a = b := T'.firstStepOf_eq_of_inSide hab hxb.symm
    have hAa : T'.sideLeaves s(a, b) a = Cluster T x₀ w :=
      (T'.sideLeaves_eq_of_inSide hu₀a).symm.trans hBeq
    refine ⟨a, fun ha => hx₀A (hAa ▸ (ha ▸ T'.mem_sideLeaves_self s(a, b) x₀)), ?_⟩
    rw [Cluster_eq_sideLeaves, hpa]
    exact hAa

/-- **`psi`**：把 `T` 的顶点搬到 `T'`（`T.leaf x₀ ↦ T'.leaf x₀`，其余由 `Cluster` 决定）。 -/
noncomputable def psi {T T' : Cladogram X} {x₀ : X}
    (hmatch : ∀ s : Split X, T.IsSplitOf s ↔ T'.IsSplitOf s) (v : T.V) : T'.V :=
  if hv : T.leaf x₀ = v then T'.leaf x₀
  else Classical.choose (exists_cluster_eq (T := T) (T' := T') hmatch hv)

theorem psi_leaf₀ {T T' : Cladogram X} {x₀ : X}
    (hmatch : ∀ s : Split X, T.IsSplitOf s ↔ T'.IsSplitOf s) :
    psi (T := T) (T' := T') (x₀ := x₀) hmatch (T.leaf x₀) = T'.leaf x₀ := by
  unfold psi
  exact dite_eq_left rfl

theorem psi_ne_leaf₀ {T T' : Cladogram X} {x₀ : X}
    (hmatch : ∀ s : Split X, T.IsSplitOf s ↔ T'.IsSplitOf s) {v : T.V}
    (hv : T.leaf x₀ ≠ v) : T'.leaf x₀ ≠ psi (T := T) (T' := T') (x₀ := x₀) hmatch v := by
  unfold psi
  rw [dite_eq_right hv]
  exact (Classical.choose_spec (exists_cluster_eq (T := T) (T' := T') hmatch hv)).1

/-- **`psi` 保簇**：`C' (psi v) = C v`。 -/
theorem Cluster_psi {T T' : Cladogram X} {x₀ : X}
    (hmatch : ∀ s : Split X, T.IsSplitOf s ↔ T'.IsSplitOf s) {v : T.V}
    (hv : T.leaf x₀ ≠ v) :
    Cluster T' x₀ (psi (T := T) (T' := T') (x₀ := x₀) hmatch v) = Cluster T x₀ v := by
  unfold psi
  rw [dite_eq_right hv]
  exact (Classical.choose_spec (exists_cluster_eq (T := T) (T' := T') hmatch hv)).2

/-- **`psi` 把叶送到叶**（`x ≠ x₀`）。 -/
theorem psi_leaf {T T' : Cladogram X} {x₀ : X}
    (hmatch : ∀ s : Split X, T.IsSplitOf s ↔ T'.IsSplitOf s) {x : X} (hx : x ≠ x₀) :
    psi (T := T) (T' := T') (x₀ := x₀) hmatch (T.leaf x) = T'.leaf x := by
  have hv : T.leaf x₀ ≠ T.leaf x := fun h => hx (T.leaf.injective h).symm
  have hx' : x₀ ≠ x := fun h => hx h.symm
  refine Cluster_injective (T := T') (x₀ := x₀)
    (v := psi (T := T) (T' := T') (x₀ := x₀) hmatch (T.leaf x)) (w := T'.leaf x)
    (psi_ne_leaf₀ (T := T) (T' := T') (x₀ := x₀) hmatch hv)
    (fun h => hx (T'.leaf.injective h).symm) ?_
  rw [Cluster_psi (T := T) (T' := T') (x₀ := x₀) hmatch hv,
    Cluster_leaf (T := T) hx', Cluster_leaf (T := T') hx']

/-- **`psi` 单射**。 -/
theorem psi_injective {T T' : Cladogram X} {x₀ : X}
    (hmatch : ∀ s : Split X, T.IsSplitOf s ↔ T'.IsSplitOf s) :
    Function.Injective (psi (T := T) (T' := T') (x₀ := x₀) hmatch) := by
  intro v w hvw
  by_cases hv : v = T.leaf x₀
  · subst hv
    by_cases hw : w = T.leaf x₀
    · exact hw.symm
    · exfalso
      rw [psi_leaf₀ (T := T) (T' := T') (x₀ := x₀) hmatch] at hvw
      exact psi_ne_leaf₀ (T := T) (T' := T') (x₀ := x₀) hmatch
        (fun h => hw h.symm) hvw
  · by_cases hw : w = T.leaf x₀
    · exfalso
      rw [hw] at hvw
      rw [psi_leaf₀ (T := T) (T' := T') (x₀ := x₀) hmatch] at hvw
      exact psi_ne_leaf₀ (T := T) (T' := T') (x₀ := x₀) hmatch
        (fun h => hv h.symm) hvw.symm
    · have hv' : T.leaf x₀ ≠ v := fun h => hv h.symm
      have hw' : T.leaf x₀ ≠ w := fun h => hw h.symm
      exact Cluster_injective hv' hw' (by
        rw [← Cluster_psi (T := T) (T' := T') (x₀ := x₀) hmatch hv', hvw,
          Cluster_psi (T := T) (T' := T') (x₀ := x₀) hmatch hw'])

/-- **`psi` 满射**（用 `exists_cluster_eq` 反向搬运 + A1 唯一性）。 -/
theorem psi_surjective {T T' : Cladogram X} {x₀ : X}
    (hmatch : ∀ s : Split X, T.IsSplitOf s ↔ T'.IsSplitOf s) :
    Function.Surjective (psi (T := T) (T' := T') (x₀ := x₀) hmatch) := by
  intro u
  by_cases hu : u = T'.leaf x₀
  · exact ⟨T.leaf x₀, by
      rw [hu, psi_leaf₀ (T := T) (T' := T') (x₀ := x₀) hmatch]⟩
  · have hu' : T'.leaf x₀ ≠ u := fun h => hu h.symm
    have hmatch' : ∀ s : Split X, T'.IsSplitOf s ↔ T.IsSplitOf s := fun s => (hmatch s).symm
    obtain ⟨v, hv_ne, hv_eq⟩ := exists_cluster_eq (T := T') (T' := T) (x₀ := x₀) hmatch' hu'
    exact ⟨v, Cluster_injective (T := T') (x₀ := x₀)
      (v := psi (T := T) (T' := T') (x₀ := x₀) hmatch v) (w := u)
      (psi_ne_leaf₀ (T := T) (T' := T') (x₀ := x₀) hmatch hv_ne) hu'
      ((Cluster_psi (T := T) (T' := T') (x₀ := x₀) hmatch hv_ne).trans hv_eq)⟩

/-- **`psi` 把根送到根**。 -/
theorem psi_rootNb {T T' : Cladogram X} {x₀ : X}
    (hmatch : ∀ s : Split X, T.IsSplitOf s ↔ T'.IsSplitOf s) :
    psi (T := T) (T' := T') (x₀ := x₀) hmatch (rootNb T x₀) = rootNb T' x₀ := by
  have hr : T.leaf x₀ ≠ rootNb T x₀ := (adj_rootNb T x₀).ne
  refine Cluster_injective (T := T') (x₀ := x₀)
    (v := psi (T := T) (T' := T') (x₀ := x₀) hmatch (rootNb T x₀)) (w := rootNb T' x₀)
    (psi_ne_leaf₀ (T := T) (T' := T') (x₀ := x₀) hmatch hr) (adj_rootNb T' x₀).ne ?_
  rw [Cluster_psi (T := T) (T' := T') (x₀ := x₀) hmatch hr, Cluster_rootNb, Cluster_rootNb]

/-- **父亲交换律**（阶段 B 步骤 3）：`psi (p v) = p' (psi v)`。

证：把「`C (p v)` 是 `C v` 的最小真超集」（A4）用 `Cluster_psi` 搬到 `T'` 两边，
`surj` 给出 `p' (psi v) = psi w`，于是 `C w` 也是 `C v` 的真超集
（`T'` 侧 A4 给出中间量），`T` 侧 A4 的最小性给 `C (p v) ⊆ C w`，
`T'` 侧 A4 的最小性给 `C w ⊆ C (p v)`，二者相等再由 A1 收口。 -/
theorem psi_parent {T T' : Cladogram X} {x₀ : X}
    (hmatch : ∀ s : Split X, T.IsSplitOf s ↔ T'.IsSplitOf s)
    (hsurj : Function.Surjective (psi (T := T) (T' := T') (x₀ := x₀) hmatch))
    {v : T.V} (hv : T.leaf x₀ ≠ v) :
    psi (T := T) (T' := T') (x₀ := x₀) hmatch (p T x₀ v)
      = p T' x₀ (psi (T := T) (T' := T') (x₀ := x₀) hmatch v) := by
  by_cases hq : p T x₀ v = T.leaf x₀
  · have hroot : v = rootNb T x₀ := eq_rootNb_of_adj ((hq ▸ adj_p hv).symm)
    rw [hroot, psi_rootNb (T := T) (T' := T') (x₀ := x₀) hmatch, p_rootNb, p_rootNb,
      psi_leaf₀ (T := T) (T' := T') (x₀ := x₀) hmatch]
  · have hq' : T.leaf x₀ ≠ p T x₀ v := fun h => hq h.symm
    have hvroot : v ≠ rootNb T x₀ := by
      intro h
      rw [h] at hq
      exact hq (p_rootNb T x₀)
    have hq'ne : T'.leaf x₀ ≠ p T' x₀ (psi (T := T) (T' := T') (x₀ := x₀) hmatch v) := by
      intro hcon
      have hadj : T'.graph.Adj (T'.leaf x₀) (psi (T := T) (T' := T') (x₀ := x₀) hmatch v) :=
        (hcon ▸ adj_p (psi_ne_leaf₀ (T := T) (T' := T') (x₀ := x₀) hmatch hv)).symm
      have hroot : psi (T := T) (T' := T') (x₀ := x₀) hmatch v = rootNb T' x₀ :=
        eq_rootNb_of_adj hadj
      exact hvroot (psi_injective (T := T) (T' := T') (x₀ := x₀) hmatch (by
        rw [hroot, psi_rootNb (T := T) (T' := T') (x₀ := x₀) hmatch]))
    obtain ⟨w, hw⟩ := hsurj (p T' x₀ (psi (T := T) (T' := T') (x₀ := x₀) hmatch v))
    have hw' : T.leaf x₀ ≠ w := fun h =>
      hq'ne (by rw [← hw, ← h, psi_leaf₀ (T := T) (T' := T') (x₀ := x₀) hmatch])
    have hA4' := Cluster_ssubset_parent (T := T') (x₀ := x₀)
      (v := psi (T := T) (T' := T') (x₀ := x₀) hmatch v)
      (psi_ne_leaf₀ (T := T) (T' := T') (x₀ := x₀) hmatch hv) hq'ne
    have hA4 := Cluster_ssubset_parent (T := T) (x₀ := x₀) (v := v) hv hq'
    have hthis : Cluster T' x₀ (psi (T := T) (T' := T') (x₀ := x₀) hmatch v) ⊂
        Cluster T' x₀ (psi (T := T) (T' := T') (x₀ := x₀) hmatch (p T x₀ v)) := by
      rw [Cluster_psi (T := T) (T' := T') (x₀ := x₀) hmatch hv,
        Cluster_psi (T := T) (T' := T') (x₀ := x₀) hmatch hq']
      exact hA4.1
    have h1 : Cluster T' x₀ (p T' x₀ (psi (T := T) (T' := T') (x₀ := x₀) hmatch v))
        ⊆ Cluster T' x₀ (psi (T := T) (T' := T') (x₀ := x₀) hmatch (p T x₀ v)) :=
      hA4'.2 (psi (T := T) (T' := T') (x₀ := x₀) hmatch (p T x₀ v))
        (psi_ne_leaf₀ (T := T) (T' := T') (x₀ := x₀) hmatch hq') hthis
    have hw_eq : Cluster T x₀ w = Cluster T' x₀ (p T' x₀ (psi (T := T) (T' := T') (x₀ := x₀) hmatch v)) := by
      rw [← Cluster_psi (T := T) (T' := T') (x₀ := x₀) hmatch hw', hw]
    have h2 : Cluster T x₀ w ⊆ Cluster T x₀ (p T x₀ v) := by
      rw [hw_eq, ← Cluster_psi (T := T) (T' := T') (x₀ := x₀) hmatch hq']
      exact h1
    have h3 : Cluster T x₀ v ⊂ Cluster T x₀ w := by
      rw [hw_eq, ← Cluster_psi (T := T) (T' := T') (x₀ := x₀) hmatch hv]
      exact hA4'.1
    have h4 : Cluster T x₀ (p T x₀ v) ⊆ Cluster T x₀ w := hA4.2 w hw' h3
    have h6 : p T x₀ v = w :=
      Cluster_injective hq' hw' (Finset.Subset.antisymm h4 h2)
    rw [h6]
    exact hw

/-- **邻接对应**：`T'.Adj (psi v) (psi w) ↔ T.Adj v w`。

两个顶点都不是 `T.leaf x₀` 时用 A3 + 父亲交换律；是 `T.leaf x₀` 时
用「`x₀` 叶的唯一邻居」的刻画。 -/
theorem adj_iff_adj_psi {T T' : Cladogram X} {x₀ : X}
    (hmatch : ∀ s : Split X, T.IsSplitOf s ↔ T'.IsSplitOf s)
    (hpar : ∀ v : T.V, T.leaf x₀ ≠ v →
      psi (T := T) (T' := T') (x₀ := x₀) hmatch (p T x₀ v)
        = p T' x₀ (psi (T := T) (T' := T') (x₀ := x₀) hmatch v))
    (v w : T.V) :
    T'.graph.Adj (psi (T := T) (T' := T') (x₀ := x₀) hmatch v)
      (psi (T := T) (T' := T') (x₀ := x₀) hmatch w) ↔ T.graph.Adj v w := by
  by_cases hv : v = T.leaf x₀
  · subst hv
    rw [psi_leaf₀ (T := T) (T' := T') (x₀ := x₀) hmatch]
    constructor
    · intro h
      have hw : psi (T := T) (T' := T') (x₀ := x₀) hmatch w = rootNb T' x₀ :=
        eq_rootNb_of_adj h
      have hwr : w = rootNb T x₀ := psi_injective (T := T) (T' := T') (x₀ := x₀) hmatch
        (by rw [hw, psi_rootNb (T := T) (T' := T') (x₀ := x₀) hmatch])
      rw [hwr]
      exact adj_rootNb T x₀
    · intro h
      have hw : w = rootNb T x₀ := eq_rootNb_of_adj h
      rw [hw, psi_rootNb (T := T) (T' := T') (x₀ := x₀) hmatch]
      exact adj_rootNb T' x₀
  · by_cases hw0 : w = T.leaf x₀
    · subst hw0
      rw [psi_leaf₀ (T := T) (T' := T') (x₀ := x₀) hmatch]
      constructor
      · intro h
        have hv2 : psi (T := T) (T' := T') (x₀ := x₀) hmatch v = rootNb T' x₀ :=
          eq_rootNb_of_adj h.symm
        have hvr : v = rootNb T x₀ := psi_injective (T := T) (T' := T') (x₀ := x₀) hmatch
          (by rw [hv2, psi_rootNb (T := T) (T' := T') (x₀ := x₀) hmatch])
        rw [hvr]
        exact (adj_rootNb T x₀).symm
      · intro h
        have hv2 : v = rootNb T x₀ := eq_rootNb_of_adj h.symm
        rw [hv2, psi_rootNb (T := T) (T' := T') (x₀ := x₀) hmatch]
        exact (adj_rootNb T' x₀).symm
    · have hv' : T.leaf x₀ ≠ v := fun h => hv h.symm
      have hw' : T.leaf x₀ ≠ w := fun h => hw0 h.symm
      constructor
      · intro h
        rcases (adj_iff_parent (T := T') (x₀ := x₀)
          (v := psi (T := T) (T' := T') (x₀ := x₀) hmatch v)
          (w := psi (T := T) (T' := T') (x₀ := x₀) hmatch w)
          (psi_ne_leaf₀ (T := T) (T' := T') (x₀ := x₀) hmatch hv')
          (psi_ne_leaf₀ (T := T) (T' := T') (x₀ := x₀) hmatch hw')).mp h with h' | h'
        · rw [← hpar v hv'] at h'
          exact (adj_iff_parent (T := T) (x₀ := x₀) hv' hw').mpr
            (Or.inl (psi_injective (T := T) (T' := T') (x₀ := x₀) hmatch h'))
        · rw [← hpar w hw'] at h'
          exact (adj_iff_parent (T := T) (x₀ := x₀) hv' hw').mpr
            (Or.inr (psi_injective (T := T) (T' := T') (x₀ := x₀) hmatch h'))
      · intro h
        rcases (adj_iff_parent (T := T) (x₀ := x₀) hv' hw').mp h with h' | h'
        · rw [← h', hpar v hv']
          exact adj_p (psi_ne_leaf₀ (T := T) (T' := T') (x₀ := x₀) hmatch hv')
        · rw [← h', hpar w hw']
          exact (adj_p (psi_ne_leaf₀ (T := T) (T' := T') (x₀ := x₀) hmatch hw')).symm

end Phylo

/-! ## 主定理 -/

namespace Cladogram

open Classical SimpleGraph
open Phylo

variable {X : Type u} [Fintype X] [DecidableEq X]

/-- **主定理（`3 ≤ |X|`）**：两棵 cladogram 的 split 系统相同 ⟹ 它们同构。

取固定叶 `x₀`；`psi` 由 `Cluster T x₀` 的簇族搬运给出（`exists_cluster_eq`），
`Cluster_psi`/`psi_injective`/`psi_surjective` 说明它是双射，
`psi_parent` 说明它保父亲，`adj_iff_adj_psi` 把它升级为图的同构。 -/
theorem iso_of_isSplitOf_iff {T T' : Cladogram.{u, v} X}
    (hcard : 3 ≤ Fintype.card X)
    (h : ∀ s : Split X, T.IsSplitOf s ↔ T'.IsSplitOf s) : Nonempty (Iso T T') := by
  classical
  obtain ⟨x₀⟩ := Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card X)
  have hInj := psi_injective (T := T) (T' := T') (x₀ := x₀) h
  have hSurj := psi_surjective (T := T) (T' := T') (x₀ := x₀) h
  have hpar : ∀ v : T.V, T.leaf x₀ ≠ v →
      psi (T := T) (T' := T') (x₀ := x₀) h (p T x₀ v)
        = p T' x₀ (psi (T := T) (T' := T') (x₀ := x₀) h v) :=
    fun v hv => psi_parent (T := T) (T' := T') (x₀ := x₀) h hSurj hv
  let e : T.V ≃ T'.V :=
    { toFun := psi (T := T) (T' := T') (x₀ := x₀) h
      invFun := fun u => Classical.choose (hSurj u)
      left_inv := fun v => hInj (Classical.choose_spec (hSurj (psi (T := T) (T' := T') (x₀ := x₀) h v)))
      right_inv := fun u => Classical.choose_spec (hSurj u) }
  refine ⟨{ gIso := RelIso.mk e ?_, leaf_compat := ?_ }⟩
  · exact fun {a b} => adj_iff_adj_psi (T := T) (T' := T') (x₀ := x₀) h hpar a b
  · intro x
    show e (T.leaf x) = T'.leaf x
    by_cases hx : x = x₀
    · rw [hx]
      exact psi_leaf₀ (T := T) (T' := T') (x₀ := x₀) h
    · exact psi_leaf (T := T) (T' := T') (x₀ := x₀) h hx

end Cladogram
