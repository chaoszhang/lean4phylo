/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.InternalEdge
import Phylo.Algorithm.BinaryCount
import Phylo.LaminarCount

/-!
# `Phylo.SplitsMaximal` —— binary 树的 split 系统极大（目标 T0.1 第 3 步收尾）

`Phylo/InternalEdge.lean` 把 T0.1 第 3 步隔离成**唯一**输入 `BinarySplitsMaximal`：
`T.IsBinary ⟹ T.SplitsMaximal`。本文件补上它（无 `sorry`、无新公理）。

## 路线（计数 / 极大相容族）

设 `S := Finset.univ.filter T.IsSplitOf`（即 `Σ(T)` 作为 `Finset`）。两步：

1. **下界 `2 · #E(T) ≤ #S`**（★★★ `two_mul_card_edgeFinset_le_card_splits`）：`T` 的每条边
   `⟦v,u⟧` 给出**两个**有向对 `(v,u)`、`(u,v)`，映射到「`v` 侧叶集」给出的 split；该映射单射，
   关键在 ★★★ `eq_of_sideLeaves_eq`（**叶集决定边**）。配合 `IsBinary.card_edgeFinset`
   （`#E = 2ℓ − 3`）与 ★★ `card_leafFinset`（`ℓ = |X|`）得 `4|X| − 6 ≤ #S`。
2. **上界（库里已证）**：`Finset.card_add_six_le_four_mul_card_of_pairwise_compatible`
   （`Phylo/LaminarCount.lean` ★★★）：`X` 上两两相容的 split 族至多 `4|X| − 6` 条。

若 `s` 与 `Σ(T)` 的每个 split 相容而 `s ∉ Σ(T)`，则 `Σ(T) ∪ {s, s.swap}` 是大小为 `#S + 2` 的
两两相容族，于是 `#S + 8 ≤ 4|X|`，与下界 `4|X| ≤ #S + 6` 矛盾。

## 单射性（本文件的核心）

★★★ `eq_of_sideLeaves_eq`：若边 `⟦a,b⟧` 的 `a` 侧叶集等于边 `⟦c,d⟧` 的 `c` 侧叶集，则两边相同。
两侧各用一次 ★★★ `subset_of_preconnected_of_leaf_subset'`（**删边分量是「包含其全部叶、且连通」
的最小顶点集**）得两个分量相等，再用跨越引理
`eq_edge_of_adj_of_mem_sideVertices_of_notMem`（`Phylo/SideSubtree.lean`）读出边。

★★★ `subset_of_preconnected_of_leaf_subset'` 的证明分两步：

* **`w ∈ W`**：`w` 是叶时平凡；`w` 是内部顶点时由 `no_degree_two` 得 `deg_T w ≥ 3`，而 `w` 至多
  有一个邻居（对侧端点）在分量外，故 `w` 在分量内至少有 2 个邻居；两支各含一片分量内的叶
  （★★ `leaf_in_branch`），这两片叶都在 `W` 中，而它们之间的唯一路径必经 `w`，`W` 连通 ⟹ `w ∈ W`。
* **`U ⊆ W`**：对 `p ∈ U`，在「以 `w` 为根、按唯一路径长度极大化」的论证中取极大点 `ζ`；`ζ` 若不是
  叶则 `deg_T ζ ≥ 3` 给出一个不在该路径上的邻居，从而是更长的路径（与极大性矛盾），故 `ζ = T.leaf x`
  是叶，由假设落在 `W` 里；再把 `w → ζ` 的唯一路径搬进 `W`（把 `T[W]` 的 walk 映回 `T` 后 `bypass`，
  用路径唯一性），即得 `p ∈ W`。

**⚠️ `no_degree_two` 不可去**：没有它时「分支必含叶」为假（度 2 顶点处两个方向给出同一叶集），
`eq_of_sideLeaves_eq` 随之不成立（路径 `x—y—z—w` 上 `⟦x,y⟧` 的 `x` 侧与 `⟦y,z⟧` 的 `y` 侧叶集
都是 `{x}`）。
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

/-! ## walk 与「删边分量」的相互位置

这一节把「分量」的语言翻译成「walk 的边表 / 支撑集」的语言，供后面的分支引理使用。 -/

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- ★ **不使用边 `e` 的 walk 完全落在 `G - e` 中**。 -/
theorem reachable_deleteEdges_of_notMem_edges {e : Sym2 V} {x y : V} (p : G.Walk x y)
    (h : e ∉ p.edges) : (G.deleteEdges {e}).Reachable x y :=
  Walk.recOn p
    (motive := fun a b p => e ∉ p.edges → (G.deleteEdges {e}).Reachable a b)
    (fun _ => Reachable.refl _)
    (fun {a b c} hadj q ih hh => by
      have hne : s(a, b) ≠ e := by
        intro he
        exact hh (by rw [Walk.edges_cons hadj q, he]; exact List.mem_cons_self)
      have hq : e ∉ q.edges := fun hq => hh (List.mem_cons_of_mem _ hq)
      exact ((deleteEdges_adj.mpr ⟨hadj, by simpa using hne⟩).reachable).trans (ih hq)) h

/-- ★ **支撑集不含 `w` 的 walk 不使用任何以 `w` 为端点的边**（故落在 `G - s(w,z)` 中）。 -/
theorem reachable_deleteEdges_of_notMem_support {w z x y : V} (p : G.Walk x y)
    (h : w ∉ p.support) : (G.deleteEdges {s(w, z)}).Reachable x y :=
  reachable_deleteEdges_of_notMem_edges p fun he =>
    h (Walk.mem_support_of_mem_edges he (Sym2.mem_iff.mpr (Or.inl rfl)))

end SimpleGraph

namespace Cladogram

variable {X : Type u} [Fintype X] [DecidableEq X]

variable (T : Cladogram.{u, v} X)

/-- ★★ **跨越分量侧界的 walk 必然使用那条边**（本文件所有「侧」论证的引擎）。 -/
theorem mem_edges_of_walk_of_mem_sideVertices_of_notMem {e : Sym2 T.V} {u z₁ z₂ : T.V}
    (h₁ : z₁ ∈ T.sideVertices e u) (h₂ : z₂ ∉ T.sideVertices e u)
    (p : T.graph.Walk z₂ z₁) : e ∈ p.edges := by
  by_contra h
  have hreach : (T.graph.deleteEdges {e}).Reachable z₂ z₁ :=
    SimpleGraph.reachable_deleteEdges_of_notMem_edges p h
  have h₁' : (T.graph.deleteEdges {e}).Reachable z₁ u := T.mem_sideVertices.mp h₁
  exact h₂ (T.mem_sideVertices.mpr (hreach.trans h₁'))

/-- ★★ **分量的两个端点在跨越侧界的 walk 的支撑集里**。 -/
theorem mem_pair_of_mem_sideVertices {e : Sym2 T.V} {u z w : T.V}
    (hz : z ∈ T.sideVertices e u) (hw : w ∉ T.sideVertices e u)
    (p : T.graph.Walk w z) {v : T.V} (hv : v ∈ e) : v ∈ p.support :=
  Walk.mem_support_of_mem_edges (T.mem_edges_of_walk_of_mem_sideVertices_of_notMem hz hw p) hv

/-- ★★ **唯一路径经过 `u` ⟺ 落在 `u` 一侧**（`u` 与 `w` 相邻）。

用于「分支」论证：`z` 在以 `w` 为根、经过邻居 `u` 的那一支里，当且仅当唯一路径 `w → z` 经过 `u`。 -/
theorem mem_sideVertices_of_adj_of_mem_support {w u : T.V} (hwu : T.graph.Adj w u)
    {z : T.V} {p : T.graph.Walk w z} (hp : p.IsPath) (hu : u ∈ p.support) :
    z ∈ T.sideVertices s(w, u) u := by
  have hnotnil : ¬p.Nil := fun h => by
    have hs : p.support = [w] := Walk.nil_iff_support_eq.mp h
    rw [hs, List.mem_singleton] at hu
    exact hwu.ne hu.symm
  have hsnd : u = p.snd := T.isTree.isAcyclic.eq_snd_of_adj_start hp hwu hu
  have hwtail : w ∉ p.tail.support := by
    rw [Walk.support_tail_of_not_nil p hnotnil]
    have hnd := hp.support_nodup
    rw [← Walk.cons_tail_support p] at hnd
    exact (List.nodup_cons.mp hnd).1
  have hreach : (T.graph.deleteEdges {s(w, u)}).Reachable p.snd z :=
    SimpleGraph.reachable_deleteEdges_of_notMem_support p.tail hwtail
  rw [← hsnd] at hreach
  exact T.mem_sideVertices.mpr hreach.symm

/-- ★★ **`w` 的邻居 `u` 的整支都落在 `w` 的分量内**（跨越 `U` 的边只有一条，且在 `w` 处）。 -/
theorem sideVertices_adj_subset {w w' u : T.V} (hww' : T.graph.Adj w w')
    (hwu : T.graph.Adj w u) (huU : u ∈ T.sideVertices s(w, w') w) :
    T.sideVertices s(w, u) u ⊆ T.sideVertices s(w, w') w := by
  intro q hq
  obtain ⟨Q⟩ := T.mem_sideVertices.mp hq
  have hwQ : w ∉ Q.support := by
    intro hw
    have h1 : (T.graph.deleteEdges {s(w, u)}).Reachable q w := reachable_of_mem_support Q hw
    have h2 : (T.graph.deleteEdges {s(w, u)}).Reachable w u :=
      h1.symm.trans ((T.mem_sideVertices (e := s(w, u)) (u := u) (w := q)).mp hq)
    exact T.not_reachable_deleteEdges_of_adj hwu h2
  let P : T.graph.Walk q w := (Q.mapLe (deleteEdges_le {s(w, u)})).concat hwu.symm
  have hPedge : s(w, w') ∉ P.edges := by
    show s(w, w') ∉ ((Q.mapLe (deleteEdges_le {s(w, u)})).concat hwu.symm).edges
    rw [Walk.edges_concat]
    simp only [List.concat_eq_append, List.mem_append, List.mem_singleton, not_or]
    constructor
    · intro he
      have hwmem : w ∈ Q.support := by
        have hmem := Walk.mem_support_of_mem_edges he (Sym2.mem_iff.mpr (Or.inl rfl))
        rwa [Walk.support_mapLe_eq_support] at hmem
      exact hwQ hwmem
    · intro heq
      rcases Sym2.eq_iff.mp heq with ⟨h, -⟩ | ⟨-, h⟩
      · exact hwu.ne h
      · exact (T.notMem_sideVertices_of_adj hww') (h.symm ▸ huU)
  exact T.mem_sideVertices.mpr
    (SimpleGraph.reachable_deleteEdges_of_notMem_edges P hPedge)

/-- ★★ **`w` 的邻居 `u` 的分支里必有一片落在 `w` 分量内的叶**。 -/
theorem leaf_in_branch {w w' u : T.V} (hww' : T.graph.Adj w w') (hwu : T.graph.Adj w u)
    (huU : u ∈ T.sideVertices s(w, w') w) :
    ∃ x : X, T.leaf x ∈ T.sideVertices s(w, u) u ∧ T.leaf x ∈ T.sideVertices s(w, w') w := by
  obtain ⟨x, hx⟩ := T.sideLeaves_nonempty_of_adj hwu.symm
  have hxU : x ∈ T.sideLeaves s(w, u) u := by simpa [Sym2.eq_swap] using hx
  have hxS : T.leaf x ∈ T.sideVertices s(w, u) u :=
    T.mem_sideVertices.mpr ((T.mem_sideLeaves (e := s(w, u)) (u := u) (x := x)).mp hxU)
  exact ⟨x, hxS, T.sideVertices_adj_subset hww' hwu huU hxS⟩

/-- ★★★ **最小性引理（强形式）**：删边分量是「包含其全部叶」的最小连通顶点集。

与 `subset_of_preconnected_of_leaf_subset` 的区别：**不需要假设 `w ∈ W`** —— 它由另外两条推出。
关键（也是 `no_degree_two` 唯一被用到的地方）：若 `w` 是内部顶点，则 `deg_T w ≥ 3` 而 `w` 至多有一个
邻居（`w'`）在 `U` 外，故 `w` 在 `U` 内至少有 **2** 个邻居；两支各含一片 `U` 中的叶
（★ `leaf_in_branch`），这两片叶在 `W` 中，而它们之间的唯一路径必经 `w`，`W` 连通 ⟹ `w ∈ W`。

（若没有 `no_degree_two`，`deg_U w = 1` 的情形会出现，本引理为假 —— 见路径反例。） -/
theorem subset_of_preconnected_of_leaf_subset'
    {U W : Finset T.V} {w w' : T.V} (hww' : T.graph.Adj w w')
    (hU : U = T.sideVertices s(w, w') w)
    (hWconn : (T.graph.induce (↑W : Set T.V)).Preconnected)
    (hleaf : ∀ x : X, T.leaf x ∈ U → T.leaf x ∈ W) :
    U ⊆ W := by
  classical
  have hwU' : w ∈ T.sideVertices s(w, w') w := T.self_mem_sideVertices s(w, w') w
  have hwU : w ∈ U := hU ▸ hwU'
  have hleaf' : ∀ x : X, T.leaf x ∈ T.sideVertices s(w, w') w → T.leaf x ∈ W :=
    fun x hx => hleaf x (hU.symm ▸ hx)
  have hwW : w ∈ W := by
    by_cases hwl : T.IsLeaf w
    · obtain ⟨x, hx⟩ := hwl
      exact hx ▸ hleaf' x (hx.symm ▸ hwU')
    · -- `w` 是内部顶点：度 ≥ 3，故 `U` 内至少两个邻居
      have hcross : ∀ y, T.graph.Adj w y → y ∉ U → y = w' := by
        intro y hwy hyU
        have hpair : s(w, y) = s(w, w') :=
          T.eq_edge_of_adj_of_mem_sideVertices_of_notMem hwy hwU' (hU ▸ hyU)
        rcases Sym2.eq_iff.mp hpair with ⟨-, h⟩ | ⟨h, -⟩
        · exact h
        · exact absurd h hww'.ne
      have hsdiff : (T.graph.neighborFinset w \ U).card ≤ 1 := by
        calc (T.graph.neighborFinset w \ U).card ≤ ({w'} : Finset T.V).card :=
              Finset.card_le_card fun y hy => by
                rw [Finset.mem_sdiff] at hy
                exact Finset.mem_singleton.mpr
                  (hcross y ((mem_neighborFinset T.graph w y).mp hy.1) hy.2)
          _ = 1 := Finset.card_singleton w'
      have hcardInter : 2 ≤ (T.graph.neighborFinset w ∩ U).card := by
        have hsplit := Finset.card_inter_add_card_sdiff (T.graph.neighborFinset w) U
        have hcard : (T.graph.neighborFinset w).card = T.graph.degree w :=
          card_neighborFinset_eq_degree T.graph w
        have hdeg : 3 ≤ T.graph.degree w :=
          T.three_le_degree_of_not_isLeaf (T.two_le_card_of_adj hww') hwl
        omega
      obtain ⟨u₁, hu₁⟩ := Finset.card_pos.mp (by omega : 0 < (T.graph.neighborFinset w ∩ U).card)
      have hErase : 0 < ((T.graph.neighborFinset w ∩ U).erase u₁).card := by
        rw [Finset.card_erase_of_mem hu₁]; omega
      obtain ⟨u₂, hu₂⟩ := Finset.card_pos.mp hErase
      obtain ⟨hu₂ne, hu₂mem⟩ := Finset.mem_erase.mp hu₂
      have hadj₁ : T.graph.Adj w u₁ :=
        (mem_neighborFinset T.graph w u₁).mp (Finset.mem_inter.mp hu₁).1
      have hadj₂ : T.graph.Adj w u₂ :=
        (mem_neighborFinset T.graph w u₂).mp (Finset.mem_inter.mp hu₂mem).1
      have hu₁U : u₁ ∈ U := (Finset.mem_inter.mp hu₁).2
      have hu₂U : u₂ ∈ U := (Finset.mem_inter.mp hu₂mem).2
      -- 两支各取一片叶
      obtain ⟨x₁, hx₁S, hx₁U⟩ := T.leaf_in_branch hww' hadj₁ (hU ▸ hu₁U)
      obtain ⟨x₂, hx₂S, hx₂U⟩ := T.leaf_in_branch hww' hadj₂ (hU ▸ hu₂U)
      have hx₁W : T.leaf x₁ ∈ W := hleaf' x₁ hx₁U
      have hx₂W : T.leaf x₂ ∈ W := hleaf' x₂ hx₂U
      -- 第二片叶不在第一支里（否则唯一路径 `w → ζ₂` 的第二个点既要是 `u₁` 又要是 `u₂`）
      have hnotS : T.leaf x₂ ∉ T.sideVertices s(w, u₁) u₁ := by
        intro hz
        let P : T.graph.Walk w (T.leaf x₂) := Classical.choose (T.existsUnique_path w (T.leaf x₂))
        have hPpath : P.IsPath := (Classical.choose_spec (T.existsUnique_path w (T.leaf x₂))).1
        have hmem₁ : u₁ ∈ P.support :=
          T.mem_pair_of_mem_sideVertices (e := s(w, u₁)) (u := u₁) (z := T.leaf x₂) (w := w)
            hz (by simpa [Sym2.eq_swap] using T.notMem_sideVertices_of_adj hadj₁.symm)
            (p := P) (v := u₁) (Sym2.mem_iff.mpr (Or.inr rfl))
        have hmem₂ : u₂ ∈ P.support :=
          T.mem_pair_of_mem_sideVertices (e := s(w, u₂)) (u := u₂) (z := T.leaf x₂) (w := w)
            hx₂S (by simpa [Sym2.eq_swap] using T.notMem_sideVertices_of_adj hadj₂.symm)
            (p := P) (v := u₂) (Sym2.mem_iff.mpr (Or.inr rfl))
        have hs₁ : u₁ = P.snd := T.isTree.isAcyclic.eq_snd_of_adj_start hPpath hadj₁ hmem₁
        have hs₂ : u₂ = P.snd := T.isTree.isAcyclic.eq_snd_of_adj_start hPpath hadj₂ hmem₂
        exact hu₂ne (hs₂.trans hs₁.symm)
      -- `W` 内两叶之间的 walk 必经 `w`
      obtain ⟨R⟩ := hWconn ⟨T.leaf x₁, hx₁W⟩ ⟨T.leaf x₂, hx₂W⟩
      let R' : T.graph.Walk (T.leaf x₁) (T.leaf x₂) :=
        Walk.map (SimpleGraph.Embedding.induce (↑W : Set T.V)).toHom R
      have hwR : w ∈ R'.support := by
        have hmem := T.mem_pair_of_mem_sideVertices (e := s(w, u₁)) (u := u₁) (z := T.leaf x₁)
          (w := T.leaf x₂) hx₁S hnotS (p := R'.reverse) (v := w)
          (Sym2.mem_iff.mpr (Or.inl rfl))
        rwa [Walk.support_reverse, List.mem_reverse] at hmem
      have hsuppR'W : ∀ q ∈ R'.support, q ∈ W := by
        intro q hq
        have hq' : q ∈ (Walk.map (SimpleGraph.Embedding.induce (↑W : Set T.V)).toHom R).support := hq
        rw [Walk.support_map] at hq'
        obtain ⟨y, -, hyq⟩ := List.mem_map.mp hq'
        rw [← hyq]
        exact y.2
      exact hsuppR'W w hwR
  exact T.subset_of_preconnected_of_leaf_subset hww' hU hWconn hwW hleaf

/-- ★★★ **叶集决定边侧**：若边 `s(a,b)` 的 `a` 侧与边 `s(c,d)` 的 `c` 侧**叶集相同**，则两边相同。

两侧各用一次 ★★★ `subset_of_preconnected_of_leaf_subset'` 得两个分量相等，再用跨越引理
`eq_edge_of_adj_of_mem_sideVertices_of_notMem`（`a ∈ U = W`、`b ∉ U = W`）读出边。
（`no_degree_two` 通过 `subset_of_preconnected_of_leaf_subset'` 在此被用到。） -/
theorem eq_of_sideLeaves_eq {a b c d : T.V} (hab : T.graph.Adj a b) (hcd : T.graph.Adj c d)
    (hA : T.sideLeaves s(a, b) a = T.sideLeaves s(c, d) c) :
    s(a, b) = s(c, d) := by
  classical
  have hleaf₁ : ∀ x : X, T.leaf x ∈ T.sideVertices s(a, b) a →
      T.leaf x ∈ T.sideVertices s(c, d) c := by
    intro x hx
    have hx' : x ∈ T.sideLeaves s(a, b) a :=
      (T.mem_sideLeaves (e := s(a, b)) (u := a) (x := x)).mpr
        ((T.mem_sideVertices (e := s(a, b)) (u := a) (w := T.leaf x)).mp hx)
    rw [hA] at hx'
    exact (T.mem_sideVertices (e := s(c, d)) (u := c) (w := T.leaf x)).mpr
      ((T.mem_sideLeaves (e := s(c, d)) (u := c) (x := x)).mp hx')
  have hleaf₂ : ∀ x : X, T.leaf x ∈ T.sideVertices s(c, d) c →
      T.leaf x ∈ T.sideVertices s(a, b) a := by
    intro x hx
    have hx' : x ∈ T.sideLeaves s(c, d) c :=
      (T.mem_sideLeaves (e := s(c, d)) (u := c) (x := x)).mpr
        ((T.mem_sideVertices (e := s(c, d)) (u := c) (w := T.leaf x)).mp hx)
    rw [← hA] at hx'
    exact (T.mem_sideVertices (e := s(a, b)) (u := a) (w := T.leaf x)).mpr
      ((T.mem_sideLeaves (e := s(a, b)) (u := a) (x := x)).mp hx')
  have hsub₁ : T.sideVertices s(a, b) a ⊆ T.sideVertices s(c, d) c :=
    T.subset_of_preconnected_of_leaf_subset' (U := T.sideVertices s(a, b) a)
      (W := T.sideVertices s(c, d) c) (w := a) (w' := b) hab rfl
      T.preconnected_induce_sideVertices hleaf₁
  have hsub₂ : T.sideVertices s(c, d) c ⊆ T.sideVertices s(a, b) a :=
    T.subset_of_preconnected_of_leaf_subset' (U := T.sideVertices s(c, d) c)
      (W := T.sideVertices s(a, b) a) (w := c) (w' := d) hcd rfl
      T.preconnected_induce_sideVertices hleaf₂
  have hU : T.sideVertices s(a, b) a = T.sideVertices s(c, d) c :=
    Finset.Subset.antisymm hsub₁ hsub₂
  exact T.eq_edge_of_adj_of_mem_sideVertices_of_notMem hab
    (hU ▸ T.self_mem_sideVertices s(a, b) a) (hU ▸ T.notMem_sideVertices_of_adj hab)

/-! ## 计数下界 -/

/-- ★ **`u` 一侧叶集的补非空**（`splitOfEdge` 的非空性前提；由另一侧含叶 + 两侧互补）。 -/
theorem sideLeaves_sdiff_nonempty {u v : T.V} (huv : T.graph.Adj u v) :
    (Finset.univ \ T.sideLeaves s(u, v) u).Nonempty := by
  obtain ⟨y, hy⟩ := T.sideLeaves_nonempty_of_adj huv.symm
  have hy2 : y ∈ T.sideLeaves s(u, v) v := by simpa [Sym2.eq_swap] using hy
  have hy3 : y ∉ T.sideLeaves s(u, v) u :=
    Finset.mem_compl.mp ((T.sideLeaves_compl_adj huv) ▸ hy2)
  exact ⟨y, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hy3⟩⟩

open Classical in
/-- ★★★ **`S.card ≥ 2 · #E(T)`**（`S := {s // T.IsSplitOf s}` 作为 `Finset`）。

每条边 `⟦v,u⟧` 贡献**两个**有向对 `(v,u)`、`(u,v)`；映射 `(v,u) ↦ `「`v` 侧的叶集给出的 split」
落在 `S` 里，且由 ★★★ `eq_of_sideLeaves_eq` 它是**单射**：叶集相同 ⟹ 边相同；若朝向相反，
两侧叶集互补、各自非空，不可能相等。 -/
theorem two_mul_card_edgeFinset_le_card_splits :
    2 * T.graph.edgeFinset.card
      ≤ ((Finset.univ : Finset (Split X)).filter T.IsSplitOf).card := by
  classical
  set OE : Finset (Σ _ : T.V, T.V) :=
    (Finset.univ : Finset T.V).sigma (fun v => T.graph.neighborFinset v) with hOE
  have hOEcard : OE.card = 2 * T.graph.edgeFinset.card := by
    rw [hOE, Finset.card_sigma]
    rw [show (∑ a ∈ (Finset.univ : Finset T.V), (T.graph.neighborFinset a).card)
        = ∑ a ∈ (Finset.univ : Finset T.V), T.graph.degree a from
      Finset.sum_congr rfl fun a _ => card_neighborFinset_eq_degree T.graph a]
    simpa using SimpleGraph.sum_degrees_eq_twice_card_edges T.graph
  have hadj : ∀ p : ↥OE, T.graph.Adj p.1.1 p.1.2 := fun p =>
    (mem_neighborFinset T.graph p.1.1 p.1.2).mp (Finset.mem_sigma.mp p.2).2
  let f : ↥OE → Split X := fun p =>
    T.splitOfEdge s(p.1.1, p.1.2) p.1.1 (T.sideLeaves_nonempty_of_adj (hadj p))
      (T.sideLeaves_sdiff_nonempty (hadj p))
  have hfS : ∀ p : ↥OE, T.IsSplitOf (f p) := fun p =>
    ⟨p.1.1, p.1.2, hadj p, p.1.1, rfl⟩
  have hf_inj : Function.Injective f := by
    intro p q hpq
    have hside : T.sideLeaves s(p.1.1, p.1.2) p.1.1
        = T.sideLeaves s(q.1.1, q.1.2) q.1.1 := by
      have h := congrArg Split.sideA hpq
      simpa [f] using h
    have hedge : s(p.1.1, p.1.2) = s(q.1.1, q.1.2) :=
      T.eq_of_sideLeaves_eq (hadj p) (hadj q) hside
    have hpair : p.1 = q.1 := by
      rcases Sym2.eq_iff.mp hedge with h | h
      · exact Sigma.ext h.1 (heq_of_eq h.2)
      · exfalso
        have hA₂ : T.sideLeaves s(p.1.1, p.1.2) p.1.1
            = T.sideLeaves s(p.1.1, p.1.2) p.1.2 := by
          calc T.sideLeaves s(p.1.1, p.1.2) p.1.1
              = T.sideLeaves s(q.1.1, q.1.2) q.1.1 := hside
            _ = T.sideLeaves s(p.1.2, p.1.1) p.1.2 := by rw [← h.2, ← h.1]
            _ = T.sideLeaves s(p.1.1, p.1.2) p.1.2 :=
                congrArg (fun e : Sym2 T.V => T.sideLeaves e p.1.2) Sym2.eq_swap
        have hcomp := hA₂.trans (T.sideLeaves_compl_adj (hadj p))
        obtain ⟨y, hy⟩ := T.sideLeaves_nonempty_of_adj (hadj p)
        exact (Finset.mem_compl.mp (hcomp ▸ hy)) hy
    exact Subtype.ext hpair
  have hcard := Finset.card_image_of_injective (f := f) OE.attach hf_inj
  have hle : (OE.attach.image f).card
      ≤ ((Finset.univ : Finset (Split X)).filter T.IsSplitOf).card := by
    refine Finset.card_le_card fun t ht => ?_
    obtain ⟨p, -, rfl⟩ := Finset.mem_image.mp ht
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hfS p⟩
  calc 2 * T.graph.edgeFinset.card = OE.card := hOEcard.symm
    _ = OE.attach.card := (Finset.card_attach (s := OE)).symm
    _ = (OE.attach.image f).card := hcard.symm
    _ ≤ ((Finset.univ : Finset (Split X)).filter T.IsSplitOf).card := hle

/-! ## 主定理：binary ⟹ `SplitsMaximal` -/

/-- ★★★ **binary 树的 split 系统极大**（目标 T0.1 第 3 步的唯一剩余输入）。

设 `s` 与 `Σ(T)` 的每个 split 相容。若 `s ∉ Σ(T)`，则 `S' := Σ(T) ∪ {s, s.swap}` 是**两两相容**族，
`#S' = #Σ(T) + 2`；由 ★★★ `card_add_six_le_four_mul_card_of_pairwise_compatible`
（`Phylo/LaminarCount.lean`）`#S' + 6 ≤ 4|X|`，而由 ★★★ `two_mul_card_edgeFinset_le_card_splits`
与 `IsBinary.card_edgeFinset`（`#E = 2ℓ − 3`）、`card_leafFinset`（`ℓ = |X|`）得 `#Σ(T) ≥ 4|X| − 6`，
于是 `#Σ(T) + 8 ≤ 4|X| ≤ #Σ(T) + 6` —— 矛盾。 -/
theorem splitsMaximal_of_isBinary (hT : T.IsBinary) : T.SplitsMaximal := by
  classical
  intro s hs
  by_contra hsS
  -- `s` 的两侧都非空 ⟹ `2 ≤ |X|`（并得到基点 `ρ`）
  have hcardX : 2 ≤ Fintype.card X := by
    have h1 : 0 < s.sideA.card := Finset.card_pos.mpr (by simpa [Split.sideA] using s.nonempty 0)
    have h2 : 0 < s.sideB.card := Finset.card_pos.mpr (by simpa [Split.sideB] using s.nonempty 1)
    have h := Finset.card_union_of_disjoint s.disjoint_sides
    rw [s.union_sides, Finset.card_univ] at h
    omega
  obtain ⟨ρ⟩ := Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card X)
  set S : Finset (Split X) := (Finset.univ : Finset (Split X)).filter T.IsSplitOf with hS
  -- `s ∉ S`、`s.swap ∉ S`、`s ≠ s.swap`
  have hnotS : s ∉ S := fun h => hsS (Finset.mem_filter.mp h).2
  have hswapNotS : s.swap ∉ S := fun h =>
    hnotS (Finset.mem_filter.mpr ⟨Finset.mem_univ _, T.isSplitOf_swap (Finset.mem_filter.mp h).2⟩)
  have hsne : s ≠ s.swap := by
    intro h
    have hAB : s.sideA = s.sideB := by
      rw [← Split.swap_sideA]
      exact congrArg Split.sideA h
    obtain ⟨x, hx⟩ := s.nonempty 0
    exact (Finset.disjoint_left.mp s.disjoint_sides) hx (hAB ▸ hx)
  set S' : Finset (Split X) := insert s (insert s.swap S) with hS'
  have hcardS' : S'.card = S.card + 2 := by
    have h1 : s ∉ insert s.swap S := by
      simp only [Finset.mem_insert, not_or]
      exact ⟨hsne, hnotS⟩
    rw [hS', Finset.card_insert_of_notMem h1, Finset.card_insert_of_notMem hswapNotS]
  -- `S'` 两两相容
  have hmemS' : ∀ t : Split X, t ∈ S' ↔ t = s ∨ t = s.swap ∨ t ∈ S := by
    intro t
    rw [hS', Finset.mem_insert, Finset.mem_insert]
  have hcompat : ∀ s₁ ∈ S', ∀ s₂ ∈ S', s₁ ≠ s₂ → Split.Compatible s₁ s₂ := by
    intro s₁ hs₁ s₂ hs₂ hne
    rw [hmemS'] at hs₁ hs₂
    rcases hs₁ with h₁ | h₁ | hs₁
    · rcases hs₂ with h₂ | h₂ | hs₂
      · exact absurd (h₁.trans h₂.symm) hne
      · rw [h₁, h₂]; exact Split.compatible_swap_self s
      · rw [h₁]; exact hs s₂ (Finset.mem_filter.mp hs₂).2
    · rcases hs₂ with h₂ | h₂ | hs₂
      · rw [h₁, h₂]
        exact (Split.compatible_comm s.swap s).mpr (Split.compatible_swap_self s)
      · exact absurd (h₁.trans h₂.symm) hne
      · rw [h₁]
        exact Split.compatible_swap_left.mpr (hs s₂ (Finset.mem_filter.mp hs₂).2)
    · rcases hs₂ with h₂ | h₂ | hs₂
      · rw [h₂]
        exact (Split.compatible_comm s₁ s).mpr (hs s₁ (Finset.mem_filter.mp hs₁).2)
      · rw [h₂]
        exact Split.compatible_swap_right.mpr
          ((Split.compatible_comm s₁ s).mpr (hs s₁ (Finset.mem_filter.mp hs₁).2))
      · exact pairwiseCompatible T s₁ (Finset.mem_filter.mp hs₁).2 s₂ (Finset.mem_filter.mp hs₂).2
  -- 下界与上界
  have hlow : 4 * Fintype.card X ≤ S.card + 6 := by
    have h1 := T.two_mul_card_edgeFinset_le_card_splits
    rw [← hS] at h1
    have h2 := hT.card_edgeFinset
    have h3 := T.card_leafFinset
    have h4 := hT.two_le_leafFinset_card
    omega
  have hhigh : S.card + 8 ≤ 4 * Fintype.card X := by
    have h1 := Finset.card_add_six_le_four_mul_card_of_pairwise_compatible S' ρ hcardX hcompat
    omega
  omega

end Cladogram

/-- ★★★ **binary 树的 split 系统极大**（`BinarySplitsMaximal` 本身，替代原 ⬜ 陈述）。 -/
theorem binarySplitsMaximal (X : Type u) [Fintype X] [DecidableEq X] :
    BinarySplitsMaximal.{u, v} X :=
  fun T hT => T.splitsMaximal_of_isBinary hT

/-- ★★★ **binary 树的 clade 刻画**（目标 T0.1 第 3 步的最终形式，无条件）。 -/
theorem Cladogram.isClade_iff_isClan_of_isBinary {X : Type u} [Fintype X] [DecidableEq X]
    {T : Cladogram.{u, v} X} (hT : T.IsBinary) {A : Finset X}
    (hA : A.Nonempty) (hAc : (Aᶜ).Nonempty) :
    T.IsClade A ↔ T.IsClan A :=
  Cladogram.isClade_iff_isClan_of_binary (binarySplitsMaximal X) hT hA hAc
