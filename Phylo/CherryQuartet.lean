/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.TreeDistance
import Phylo.Algorithm.Cherry
import Mathlib.Tactic.Linarith

/-!
# `Phylo.CherryQuartet` —— 樱桃 ⟹ 四点和不等式（T0.3 的最后一步）

**目标（T0.3 收尾，纯树距离代数，★★★）**：

```
Cladogram.dist_add_le_of_isCherry {T : Phylogram X} {a b : X} (hc : T.IsCherry a b)
    {i j : X} (hi : i ≠ a) (hib : i ≠ b) (hj : j ≠ a) (hjb : j ≠ b) (hij : i ≠ j) :
  d(a,b) + d(i,j) ≤ d(a,i) + d(b,j) ∧ d(a,b) + d(i,j) ≤ d(a,j) + d(b,i)
```

其中 `Cladogram.IsCherry a b := a ≠ b ∧ ∃ v, Adj (leaf a) v ∧ Adj (leaf b) v`
（`Phylo/Algorithm/Cherry.lean:37`）。

## 证明路线

取樱桃 `{a,b}` 的**公共邻居** `w`（樱桃中点）：

1. 叶 `leaf a` 的**唯一**邻居是 `w`（叶度 = 1 + `SimpleGraph.degree_eq_one_iff_existsUnique_adj`）
   ⇒ 由 `Walk.exists_eq_cons_of_ne` 把 `x → z` 的唯一路径写成 `cons`，首边必是 `⟦x,w⟧`
   ⇒ `w` 在该路径的 support 上（`Phylogram.mem_support_of_isPath_of_adj_leaf`）；
2. 由 ★★ `Phylo.TreeDist.dist_eq_add_of_mem_support` 得**距离可加**：
   `d(leaf x, z) = d(leaf x, w) + d(w, z)`（`Phylogram.dist_eq_add_of_adj_leaf_dist`）；
3. 于是两条不等式都归约成**在 `w` 处的三角不等式**（`Phylogram.dist_triangle`，本文件新证）：
   `d(a,b) + d(i,j) ≤ [d(a,w)+d(w,b)] + [d(w,i)+d(w,j)] = d(a,i) + d(b,j)`（后一条由 `i↔j` 对称）。

`dist_triangle` 走「走法比较」而不走中位点：把 `x→y`、`y→z` 的唯一路径**拼**成一条 walk `W`，
`walkDist W = d(x,y) + d(y,z)`；而 `W.toPath`（`= W.bypass`，`bypass` 的 darts 是 `W` 的 **sublist**）
的边权和 ≤ `W` 的边权和（`List.Sublist.sum_le_sum` + 边权非负）。

## 状态

* ✅ `Phylogram.mem_support_of_adj_leaf`
* ✅ `Phylogram.dist_eq_add_of_adj_leaf_dist`
* ✅ ★★ `Phylogram.dist_triangle`
* ✅ ★★★ `Cladogram.dist_add_le_of_isCherry`（**零 `sorry` / 零 `axiom`**）
-/

universe u v

variable {X : Type u}

namespace Phylogram

open SimpleGraph
open List

variable (T : Phylogram.{u, v} X)

/-- ★ **叶的唯一邻居在（任意）walk 上**：若 `w` 与叶 `T.leaf x` 相邻，则任何
`T.leaf x → z` 的 walk（`z ≠ T.leaf x`）都把 `w` 放在 support 里。

（叶度 = 1 ⇒ `w` 是唯一邻居；非平凡 walk 的首步只能是 `⟦x,w⟧`。） -/
theorem mem_support_of_adj_leaf {x : X} {w z : T.V}
    (hadj : T.graph.Adj (T.leaf x) w) {p : T.graph.Walk (T.leaf x) z}
    (hz : z ≠ T.leaf x) : w ∈ p.support := by
  classical
  obtain ⟨u', hadj', q, hpq⟩ :=
    SimpleGraph.Walk.exists_eq_cons_of_ne (fun h => hz h.symm) p
  have hdeg : T.graph.degree (T.leaf x) = 1 :=
    (T.isLeaf_iff_degree_eq_one (T.leaf x)).mp ⟨x, rfl⟩
  obtain ⟨b, _hbadj, huniq⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hdeg
  have hu' : u' = w := (huniq u' hadj').trans (huniq w hadj).symm
  subst hu'
  rw [hpq, SimpleGraph.Walk.support_cons]
  exact List.mem_cons_of_mem _ (SimpleGraph.Walk.start_mem_support q)

/-- ★★ **樱桃中点处距离可加**：`w` 是叶 `T.leaf x` 的邻居 ⇒ `d(x, z) = d(x, w) + d(w, z)`
（`z ≠ T.leaf x`）。 -/
theorem dist_eq_add_of_adj_leaf_dist {x : X} {w z : T.V}
    (hadj : T.graph.Adj (T.leaf x) w) (hz : z ≠ T.leaf x) :
    T.dist (T.leaf x) z = T.dist (T.leaf x) w + T.dist w z := by
  have hp : ((T.existsUnique_path (T.leaf x) z).choose).IsPath :=
    (T.existsUnique_path (T.leaf x) z).choose_spec.1
  exact Phylo.TreeDist.dist_eq_add_of_mem_support T _ hp
    (T.mem_support_of_adj_leaf hadj hz)

/-- ★★ **树距离的三角不等式**（树度量的度量性）。

把 `x→y` 与 `y→z` 的唯一路径拼成一条 walk `W`（`walkDist W = d(x,y) + d(y,z)`），
而唯一路径 `W.toPath` 的边表是 `W` 边表的 **sublist**（`bypass` 只删边、不增边），
配上边权非负即得 `d(x,z) = walkDist W.toPath ≤ walkDist W`。 -/
theorem dist_triangle (x y z : T.V) : T.dist x z ≤ T.dist x y + T.dist y z := by
  classical
  have hp : ((T.existsUnique_path x y).choose).IsPath := (T.existsUnique_path x y).choose_spec.1
  have hq : ((T.existsUnique_path y z).choose).IsPath := (T.existsUnique_path y z).choose_spec.1
  let W : T.graph.Walk x z :=
    ((T.existsUnique_path x y).choose).append ((T.existsUnique_path y z).choose)
  have hW : T.walkDist W = T.dist x y + T.dist y z := by
    show T.walkDist (((T.existsUnique_path x y).choose).append
      ((T.existsUnique_path y z).choose)) = T.dist x y + T.dist y z
    rw [Phylo.TreeDist.walkDist_append,
      ← Phylo.TreeDist.dist_eq_walkDist_of_isPath T _ hp,
      ← Phylo.TreeDist.dist_eq_walkDist_of_isPath T _ hq]
  have hle : T.dist x z ≤ T.walkDist W := by
    rw [Phylo.TreeDist.dist_eq_walkDist_of_isPath T _ W.toPath.isPath]
    show ((W.toPath : T.graph.Walk x z).edges.map T.wExt).sum ≤ (W.edges.map T.wExt).sum
    refine List.Sublist.sum_le_sum ?_ ?_
    · have h1 : W.bypass.edges <+ W.edges := by
        rw [SimpleGraph.Walk.edges_eq_map_darts, SimpleGraph.Walk.edges_eq_map_darts]
        exact (SimpleGraph.Walk.darts_bypass_sublist_darts W).map SimpleGraph.Dart.edge
      exact h1.map T.wExt
    · intro a ha
      obtain ⟨e, -, rfl⟩ := List.mem_map.mp ha
      exact Phylo.TreeDist.wExt_nonneg T e
  rw [hW] at hle
  exact hle

end Phylogram

namespace Cladogram

/-- ★★★ **樱桃 ⟹ 四点和不等式**（树层，纯距离代数）。

取樱桃 `{a,b}` 的公共邻居 `w`：`a`、`b` 到任何点的唯一路径都过 `w`
（`Phylogram.dist_eq_add_of_adj_leaf_dist`），于是两条不等式都成为
「在 `w` 处的三角不等式」（`Phylogram.dist_triangle`）；
第二条正是第一条**交换 `i`、`j`**（`d(i,j) = d(j,i)`）。

⚠️ 假设 `hij : i ≠ j` 为**签名兼容**保留（T0.3 调用方要求「`i,j` 互异」）；
四点和不等式在 `i = j` 时同样成立（此时结论退化为 `w` 处三角不等式的特例）。 -/
theorem dist_add_le_of_isCherry {T : Phylogram.{u, v} X} {a b : X} (hc : T.IsCherry a b)
    {i j : X} (hi : i ≠ a) (hib : i ≠ b) (hj : j ≠ a) (hjb : j ≠ b) (hij : i ≠ j) :
    T.dist (T.leaf a) (T.leaf b) + T.dist (T.leaf i) (T.leaf j)
        ≤ T.dist (T.leaf a) (T.leaf i) + T.dist (T.leaf b) (T.leaf j)
    ∧ T.dist (T.leaf a) (T.leaf b) + T.dist (T.leaf i) (T.leaf j)
        ≤ T.dist (T.leaf a) (T.leaf j) + T.dist (T.leaf b) (T.leaf i) := by
  classical
  obtain ⟨hab, w, haw, hbw⟩ := hc
  -- 一条一般形式的四点不等式（对任意 `i,j ∉ {a,b}`）
  have key : ∀ {i j : X}, i ≠ a → i ≠ b → j ≠ a → j ≠ b → i ≠ j →
      T.dist (T.leaf a) (T.leaf b) + T.dist (T.leaf i) (T.leaf j)
        ≤ T.dist (T.leaf a) (T.leaf i) + T.dist (T.leaf b) (T.leaf j) := by
    intro i j hi hib hj hjb _hij
    have hia : T.leaf i ≠ T.leaf a := fun h => hi (T.leaf.injective h)
    have hib' : T.leaf i ≠ T.leaf b := fun h => hib (T.leaf.injective h)
    have hja : T.leaf j ≠ T.leaf a := fun h => hj (T.leaf.injective h)
    have hjb' : T.leaf j ≠ T.leaf b := fun h => hjb (T.leaf.injective h)
    have hab' : T.leaf a ≠ T.leaf b := fun h => hab (T.leaf.injective h)
    -- 距离在樱桃中点 `w` 处可加
    have hAB : T.dist (T.leaf a) (T.leaf b)
        = T.dist (T.leaf a) w + T.dist w (T.leaf b) :=
      T.dist_eq_add_of_adj_leaf_dist haw hab'.symm
    have hAI : T.dist (T.leaf a) (T.leaf i)
        = T.dist (T.leaf a) w + T.dist w (T.leaf i) :=
      T.dist_eq_add_of_adj_leaf_dist haw hia
    have hBJ : T.dist (T.leaf b) (T.leaf j)
        = T.dist (T.leaf b) w + T.dist w (T.leaf j) :=
      T.dist_eq_add_of_adj_leaf_dist hbw hjb'
    -- `w` 处的三角不等式
    have htri : T.dist (T.leaf i) (T.leaf j)
        ≤ T.dist w (T.leaf i) + T.dist w (T.leaf j) := by
      have h := T.dist_triangle (T.leaf i) w (T.leaf j)
      rwa [Phylo.TreeDist.dist_comm T (T.leaf i) w] at h
    have hcomm : T.dist w (T.leaf b) = T.dist (T.leaf b) w :=
      Phylo.TreeDist.dist_comm T w (T.leaf b)
    rw [hAB, hAI, hBJ]
    linarith
  refine ⟨key hi hib hj hjb hij, ?_⟩
  -- 第二条 = 第一条**交换 `i`、`j`**（`d(i,j) = d(j,i)`）
  have h := key (i := j) (j := i) hj hjb hi hib hij.symm
  rwa [Phylo.TreeDist.dist_comm T (T.leaf j) (T.leaf i)] at h

end Cladogram
