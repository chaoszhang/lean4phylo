/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.InternalEdge
import Phylo.Algorithm.BinaryCount

/-!
# `Phylo.SplitsMaximal` —— binary 树的 split 系统极大（目标 T0.1 第 3 步收尾）

`Phylo/InternalEdge.lean` 把 T0.1 第 3 步隔离成**唯一**输入 `BinarySplitsMaximal`：
`T.IsBinary ⟹ T.SplitsMaximal`。本文件补上它。

## 路线（计数 / 极大相容族）

设 `ρ : X`，`S := {s : Split X // T.IsSplitOf s}`（作为 `Finset`）。两步：

1. **下界 `2 · #E(T) ≤ #S`**：`T` 的每条边 `e = ⟦v,u⟧` 给出**两个** split
   （`v` 侧与 `u` 侧），且映射 `(v,u) ↦ ` 「`(v,u)` 侧的叶集」是**单射**
   （★ `Finset.card_le_card` + ★★ `isSplitOf_sideLeaves_injective`）。
   配合 `★ #E(T) = 2·|X| − 3`（`IsBinary.card_edgeFinset` + ★★ `card_leafFinset`）得
   `4|X| − 6 ≤ #S`。
2. **上界（已证）**：`Finset.card_add_six_le_four_mul_card_of_pairwise_compatible`
   （`Phylo/LaminarCount.lean` ★★★）：`X` 上两两相容的 split 族至多 `4|X| − 6` 条。

若 `s` 与 `Σ(T)` 的每个 split 相容而 `s ∉ Σ(T)`，则 `Σ(T) ∪ {s, s.swap}` 是大小为
`#S + 2` 的两两相容族，于是 `#S + 8 ≤ 4|X|`；与下界 `4|X| ≤ #S + 6` 矛盾。

## 单射性（本文件的核心）

`(v,u) ↦ T.sideLeaves ⟦v,u⟧ v` 的单射性归结为**「叶集决定边侧」**：

> ★★ `sideVertices_eq_of_sideLeaves_eq`：若 `U = T.sideVertices e w`、`W = T.sideVertices f w'`
> 都以 `w`（分别 `w'`）为边界点，`T.leaf ρ` 不在两侧，且两侧叶集相同，则 `U = W`。

这由 **最小性引理** ★★ `subset_of_preconnected_of_leaf_subset` 完成：分量的顶点集是「包含其全部
叶、且连通」的**最小**顶点集。证明用「以 `w` 为根、按唯一路径长度极大化」的论证，
关键工具是 `IsAcyclic.eq_penultimate_of_adj_end`（叶的存在性）与
`no_degree_two`（极大点若是内部顶点则度 ≥ 3，必有第二个「向下」的邻居 —— 矛盾）。
-/

open Phylo
open SimpleGraph

universe u v

namespace Cladogram

variable {X : Type u} [Fintype X] [DecidableEq X]

set_option linter.unusedSectionVars false

variable (T : Cladogram.{u, v} X)

/-! ## 叶数 -/

/-- ★★ **`T` 的叶数恰为 `|X|`**（`leaf` 是嵌入；`leaf_iff_degree_one` 保证「叶」= 「`leaf` 的像」）。 -/
theorem card_leafFinset : T.leafFinset.card = Fintype.card X := by
  have himg : T.leafFinset = Finset.univ.image T.leaf := by
    ext v
    simp only [T.mem_leafFinset, Cladogram.IsLeaf, Finset.mem_image, Finset.mem_univ, true_and]
  rw [himg, Finset.card_image_of_injective _ T.leaf.injective, Finset.card_univ]

/-! ## 边的两侧：`T.leaf ρ` 恰在一边 -/

/-- ★ **`T.leaf ρ` 不在 `a` 侧 ⟺ 它在 `b` 侧**（`T − ⟦a,b⟧` 恰有两个分量）。 -/
theorem notMem_sideVertices_left_iff_mem_right {ρ : X} {a b : T.V} (hab : T.graph.Adj a b) :
    T.leaf ρ ∉ T.sideVertices s(a, b) a ↔ T.leaf ρ ∈ T.sideVertices s(a, b) b := by
  have hmem : ∀ u : T.V, (T.leaf ρ ∈ T.sideVertices s(a, b) u)
      ↔ (T.graph.deleteEdges {s(a, b)}).Reachable (T.leaf ρ) u :=
    fun u => T.mem_sideVertices (e := s(a, b)) (u := u) (w := T.leaf ρ)
  constructor
  · intro h
    rcases T.inSide_or_inSide hab (x := T.leaf ρ) with h' | h'
    · exact absurd ((hmem a).mpr h') h
    · exact (hmem b).mpr h'
  · intro h h'
    exact T.not_inSide_both hab
      ⟨reachable_comm.mpr ((hmem a).mp h'), reachable_comm.mpr ((hmem b).mp h)⟩

/-! ## 最小性引理

设 `U` 是删去边 `⟦w,w'⟧` 后含 `w` 的**分量**。则 `U` 是「包含 `U` 的全部叶、且连通」的
**最小**顶点集：任何连通且包含这些叶与 `w` 的 `W` 都满足 `U ⊆ W`。

证明（对唯一路径长度作极大化）：固定 `p ∈ U`，令
`B := {q ∈ U : p 在 w → q 的唯一路径上}`（非空，含 `p`），取 `ζ ∈ B` 使路径长度极大。

* 若 `ζ` 不是叶，则 `deg ζ ≥ 3`（`three_le_degree_of_not_isLeaf`）。除 `path(w,ζ)` 的
  倒数第二点 `pen` 外，每个邻居 `u` 都满足 `u ∉ path(w,ζ)`（`IsAcyclic.eq_penultimate_of_adj_end`
  + `eq_penultimate_of_adj_end`），于是 `u → ζ → w` 是一条路径，故 `p` 也在 `w → u` 的唯一路径上，
  即 `u ∈ B`，而 `u` 的路径长度比 `ζ` 大 `1` —— 与极大性矛盾。
* 故 `ζ` 是叶 `T.leaf x`，由 `hleaf` 得 `ζ ∈ W`；`W` 连通 ⟹ 把 `T[W]` 中的 walk 映回 `T` 再
  `bypass`，由唯一性得「`w → ζ` 的唯一路径的支撑 ⊆ `W`」。而 `p` 在该支撑上，故 `p ∈ W`。 -/

/-- ★★ **最小性引理**：分量是「包含其全部叶」的最小连通顶点集。 -/
theorem subset_of_preconnected_of_leaf_subset
    {U W : Finset T.V} {w w' : T.V} (hww' : T.graph.Adj w w')
    (hU : U = T.sideVertices s(w, w') w)
    (hWconn : (T.graph.induce (↑W : Set T.V)).Preconnected)
    (hwW : w ∈ W)
    (hleaf : ∀ x : X, T.leaf x ∈ U → T.leaf x ∈ W) :
    U ⊆ W := by
  classical
  intro p hpU
  by_cases hpw : p = w
  · subst hpw; exact hwW
  -- 以 `w` 为根的「唯一路径」函数
  let pathOf : (q : T.V) → T.graph.Walk w q := fun q => Classical.choose (T.existsUnique_path w q)
  have pathOf_isPath : ∀ q, (pathOf q).IsPath :=
    fun q => (Classical.choose_spec (T.existsUnique_path w q)).1
  have pathOf_unique : ∀ q (r : T.graph.Walk w q), r.IsPath → r = pathOf q :=
    fun q r hr => (Classical.choose_spec (T.existsUnique_path w q)).2 r hr
  set B : Finset T.V := Finset.univ.filter (fun q => q ∈ U ∧ p ∈ (pathOf q).support) with hB
  have hpB : p ∈ B := by
    rw [hB, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hpU, Walk.end_mem_support (pathOf p)⟩
  obtain ⟨ζ, hζB, hζmax⟩ := Finset.exists_max_image B (fun q => (pathOf q).length) ⟨p, hpB⟩
  have hζB' := hζB
  rw [hB, Finset.mem_filter] at hζB'
  have hζU : ζ ∈ U := hζB'.2.1
  have hζp : p ∈ (pathOf ζ).support := hζB'.2.2
  have hζne : ζ ≠ w := by
    intro h
    have hnil : pathOf w = Walk.nil := (pathOf_unique w Walk.nil Walk.IsPath.nil).symm
    have hζp' : p ∈ (pathOf w).support := h ▸ hζp
    rw [hnil, Walk.support_nil, List.mem_singleton] at hζp'
    exact hpw hζp'
  have hζleaf : T.IsLeaf ζ := by
    by_contra hnl
    have hζmemU : ζ ∈ T.sideVertices s(w, w') w := hU ▸ hζU
    have hnilp : ¬(pathOf ζ).Nil := fun h => hζne (Walk.Nil.eq h).symm
    have hcard : 3 ≤ T.graph.degree ζ :=
      T.three_le_degree_of_not_isLeaf (T.two_le_card_of_adj hww') hnl
    have hpen_mem : (pathOf ζ).penultimate ∈ T.graph.neighborFinset ζ :=
      (mem_neighborFinset T.graph ζ _).mpr (Walk.adj_penultimate hnilp).symm
    have hcardErase : 0 < ((T.graph.neighborFinset ζ).erase (pathOf ζ).penultimate).card := by
      have h1 := Finset.card_erase_add_one hpen_mem
      have h2 : (T.graph.neighborFinset ζ).card = T.graph.degree ζ :=
        card_neighborFinset_eq_degree T.graph ζ
      omega
    obtain ⟨u, hu⟩ := Finset.card_pos.mp hcardErase
    obtain ⟨hu_ne, hu_mem⟩ := Finset.mem_erase.mp hu
    have hadj : T.graph.Adj ζ u := (mem_neighborFinset T.graph ζ u).mp hu_mem
    -- `u` 仍在 `U` 中（跨越 `U` 的边只有一条，且它在 `w` 处）
    have huU : u ∈ U := by
      by_contra huU'
      have hpair : s(ζ, u) = s(w, w') :=
        T.eq_edge_of_adj_of_mem_sideVertices_of_notMem hadj hζmemU (hU ▸ huU')
      have hmemζ : ζ ∈ s(w, w') :=
        hpair ▸ (Sym2.mem_iff.mpr (Or.inl rfl) : ζ ∈ s(ζ, u))
      rcases Sym2.mem_iff.mp hmemζ with h | h
      · exact hζne h
      · exact (T.notMem_sideVertices_of_adj hww') (h ▸ hζmemU)
    -- `u` 不在 `path(w,ζ)` 上，于是 `u → ζ → w` 给出更长的路径
    have hsupp : u ∉ (pathOf ζ).support := by
      intro hsu
      exact hu_ne (T.isTree.isAcyclic.eq_penultimate_of_adj_end (pathOf_isPath ζ) hadj hsu)
    have hRpath : (Walk.cons hadj.symm (pathOf ζ).reverse).IsPath :=
      (Walk.cons_isPath_iff hadj.symm (pathOf ζ).reverse).mpr
        ⟨(pathOf_isPath ζ).reverse, by rw [Walk.support_reverse, List.mem_reverse]; exact hsupp⟩
    have hRu : (Walk.cons hadj.symm (pathOf ζ).reverse).reverse = pathOf u :=
      pathOf_unique u _ hRpath.reverse
    have hpu : p ∈ (pathOf u).support := by
      have h2 : p ∈ (Walk.cons hadj.symm (pathOf ζ).reverse).support := by
        rw [Walk.support_cons]
        exact List.mem_cons_of_mem _
          (by rw [Walk.support_reverse, List.mem_reverse]; exact hζp)
      rw [← hRu, Walk.support_reverse, List.mem_reverse]
      exact h2
    have huB : u ∈ B := by
      rw [hB, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, huU, hpu⟩
    have hlen : (pathOf u).length = (pathOf ζ).length + 1 := by
      rw [← hRu, Walk.length_reverse, Walk.length_cons, Walk.length_reverse]
    have := hζmax u huB
    omega
  -- `ζ` 是叶：由 `hleaf` 得 `ζ ∈ W`，再用 `W` 的连通性把唯一路径搬进 `W`
  have hζW : ζ ∈ W := by
    obtain ⟨x, hx⟩ := hζleaf
    exact hx ▸ hleaf x (hx.symm ▸ hζU)
  have hpathW : ∀ q ∈ (pathOf ζ).support, q ∈ W := by
    obtain ⟨R⟩ := hWconn ⟨w, hwW⟩ ⟨ζ, hζW⟩
    let R' : T.graph.Walk w ζ :=
      Walk.map (SimpleGraph.Embedding.induce (↑W : Set T.V)).toHom R
    have heq : R'.bypass = pathOf ζ := pathOf_unique ζ _ R'.bypass_isPath
    have hsuppR' : ∀ q ∈ R'.support, q ∈ W := by
      intro q hq
      have hq' : q ∈ (Walk.map (SimpleGraph.Embedding.induce (↑W : Set T.V)).toHom R).support := hq
      rw [Walk.support_map] at hq'
      obtain ⟨y, -, hyq⟩ := List.mem_map.mp hq'
      rw [← hyq]
      exact y.2
    intro q hq
    exact hsuppR' q (R'.support_bypass_subset_support (heq.symm ▸ hq))
  exact hpathW p hζp

end Cladogram
