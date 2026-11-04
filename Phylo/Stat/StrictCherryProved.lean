/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.Stat.NJShrink

/-!
# `Phylo.Stat.StrictCherryProved` —— ★★★ **严格四点不等式**（原登记缺口**已证**）

协调侧 W46 复核第 ③ 条登记的缺口
★★ `Phylo.Stat.StrictCherry.strictCherry_of_isBinary_pos_gap`：
「二叉 ＋ 边权全正 ⇒ 樱桃 `{a,b}` 给出的四点不等式是**严格**的」。

本文件把它**证成**（台账【已收口】+1）。

## 证法（与文件头原先设想的路线不同，短得多）

原设想：`d(a,b)+d(p,q) ≤ d(a,p)+d(b,q)` 的**取等**只能发生在「`w` 落在 `p–q` 路径上」，
所以要证 `w` 不在那条路径上。**新观察**：不必做位置论证 —— 樱桃中点 `w` 的**第三邻居 `z`**
是 `w` 到**任何**非樱桃叶的**必经点**（`x ∉ {a,b}` ⇒ 路径 `w → leaf x` 第一步必到 `z`），于是

```text
d(w,p) + d(w,q) = [d(w,z) + d(z,p)] + [d(w,z) + d(z,q)]
                ≥ d(p,q) + 2·d(w,z)          -- 三角不等式 at z
                >  d(p,q)                    -- d(w,z) = w(w—z) > 0（正边权）
```

把这条**严格三角**与三条可加性（★ `dist_eq_add_of_adj_leaf_dist`）
`d(a,b) = d(a,w)+d(w,b)`、`d(a,p) = d(a,w)+d(w,p)`、`d(b,q) = d(b,w)+d(w,q)` 拼起来，
四点不等式的严格性立刻成立。

## 已证

* ★★★ `dist_w_eq_dist_w_z_add`：`x ∉ {a,b}` ⇒ `d(w, leaf x) = d(w,z) + d(z, leaf x)`；
* ★★★ `dist_lt_dist_add_dist_of_ne`：`p, q ∉ {a,b}` ⇒ `d(p,q) < d(w,p) + d(w,q)`；
* ★★★ `strict_cherry_fst`：四点不等式第一式**严格**；
* ★★★ `strictCherry_of_isBinary_pos_gap_holds`：缺口本身。
-/

noncomputable section

universe u v

namespace Phylo.Stat.StrictCherryProved

open Phylo
open Phylo.Stat.NJShrink

variable {X : Type u} [Fintype X] [DecidableEq X]

/-- ★★★ **`w` 到非樱桃叶的路径必经 `z`**：`x ∉ {a,b}` ⇒ `d(w, leaf x) = d(w,z) + d(z, leaf x)`。

证法与 A8-3f 里 `d(w,x) = d(w,z) + d(z,x)` 同一套：取 `w → leaf x` 的唯一路径 `P`，
`P = cons hv' P'`；`hv'` 的终点 `v'` 只能是 `z`（若为 `leaf a`／`leaf b`，
度 1 的顶点成了路径内点 —— 与 ★★★ `leaf_mem_support_eq_end` 矛盾）。 -/
theorem dist_w_eq_dist_w_z_add {T : Phylogram.{u, v} X} (hbin : T.toCladogram.IsBinary)
    {a b : X} (hab : a ≠ b) {w z : T.V} (haw : T.graph.Adj (T.leaf a) w)
    (hbw : T.graph.Adj (T.leaf b) w) (hwz : T.graph.Adj w z) (hza : z ≠ T.leaf a)
    (hzb : z ≠ T.leaf b) {x : X} (hxa : x ≠ a) (hxb : x ≠ b) :
    T.dist w (T.leaf x) = T.dist w z + T.dist z (T.leaf x) := by
  have hxw : T.leaf x ≠ w := leaf_ne_midpoint T hbin hab haw hbw x
  have hne : w ≠ T.leaf x := hxw.symm
  have hlaw : T.leaf a ≠ w := leaf_ne_midpoint T hbin hab haw hbw a
  have hlbw : T.leaf b ≠ w := leaf_ne_midpoint T hbin hab haw hbw b
  have hla : T.leaf a ≠ T.leaf x := fun h => hxa (T.leaf.injective h).symm
  have hlb : T.leaf b ≠ T.leaf x := fun h => hxb (T.leaf.injective h).symm
  obtain ⟨P, hPpath, -⟩ := T.existsUnique_path w (T.leaf x)
  obtain ⟨v', hv', P', hsplit⟩ := SimpleGraph.Walk.exists_eq_cons_of_ne hne P
  have hcases := adj_midpoint_cases T hbin hab haw hbw hwz hza hzb
  have hfirst : v' ∈ P.support := by
    rw [hsplit, SimpleGraph.Walk.support_cons]
    exact List.mem_cons_of_mem _ (SimpleGraph.Walk.start_mem_support P')
  have hda : T.graph.degree (T.leaf a) = 1 :=
    (T.isLeaf_iff_degree_eq_one (T.leaf a)).mp ⟨a, rfl⟩
  have hdb : T.graph.degree (T.leaf b) = 1 :=
    (T.isLeaf_iff_degree_eq_one (T.leaf b)).mp ⟨b, rfl⟩
  have hv'z : v' = z := by
    rcases hcases v' hv' with h | h | h
    · exfalso
      have hmem : T.leaf a ∈ P.support := by rwa [h] at hfirst
      rcases leaf_mem_support_eq_end T hda P hPpath.support_nodup hmem with h' | h'
      · exact hlaw h'
      · exact hla h'
    · exfalso
      have hmem : T.leaf b ∈ P.support := by rwa [h] at hfirst
      rcases leaf_mem_support_eq_end T hdb P hPpath.support_nodup hmem with h' | h'
      · exact hlbw h'
      · exact hlb h'
    · exact h
  subst v'
  have hP'path : P'.IsPath := by
    rw [hsplit] at hPpath
    exact SimpleGraph.Walk.IsPath.of_cons hPpath
  have hstep : T.dist w z = T.wExt s((w : T.V), (z : T.V)) :=
    Phylo.TreeDist.dist_eq_wExt_of_adj T hv'
  rw [Phylo.TreeDist.dist_eq_walkDist_of_isPath T P hPpath, hsplit,
    Phylogram.walkDist, SimpleGraph.Walk.edges_cons, List.map_cons, List.sum_cons, hstep,
    ← Phylogram.walkDist, ← Phylo.TreeDist.dist_eq_walkDist_of_isPath _ P' hP'path]

/-- ★★★ **严格三角**：`p, q ∉ {a,b}` ⇒ `d(p,q) < d(w,p) + d(w,q)`。

`d(w,p) + d(w,q) = d(z,p) + d(z,q) + 2·d(w,z) ≥ d(p,q) + 2·d(w,z) > d(p,q)`。 -/
theorem dist_lt_dist_add_dist_of_ne {T : Phylogram.{u, v} X} (hbin : T.toCladogram.IsBinary)
    {a b : X} (hab : a ≠ b) {w z : T.V} (haw : T.graph.Adj (T.leaf a) w)
    (hbw : T.graph.Adj (T.leaf b) w) (hwz : T.graph.Adj w z) (hza : z ≠ T.leaf a)
    (hzb : z ≠ T.leaf b) (hpos : ∀ e : Edge T.toCladogram, 0 < T.w e)
    {p q : X} (hpa : p ≠ a) (hpb : p ≠ b) (hqa : q ≠ a) (hqb : q ≠ b) :
    T.dist (T.leaf p) (T.leaf q) < T.dist w (T.leaf p) + T.dist w (T.leaf q) := by
  have h1 := dist_w_eq_dist_w_z_add (T := T) hbin hab haw hbw hwz hza hzb hpa hpb
  have h2 := dist_w_eq_dist_w_z_add (T := T) hbin hab haw hbw hwz hza hzb hqa hqb
  have h3 : T.dist (T.leaf p) (T.leaf q) ≤ T.dist (T.leaf p) z + T.dist z (T.leaf q) :=
    T.dist_triangle (T.leaf p) z (T.leaf q)
  have hwzpos : 0 < T.dist w z := by
    rw [Phylo.TreeDist.dist_eq_w_of_adj T hwz]
    exact hpos _
  have hzp : T.dist z (T.leaf p) = T.dist (T.leaf p) z :=
    (Phylo.TreeDist.dist_comm T (T.leaf p) z).symm
  have hzq : T.dist z (T.leaf q) = T.dist (T.leaf q) z :=
    (Phylo.TreeDist.dist_comm T (T.leaf q) z).symm
  linarith

/-- ★★★ **四点不等式第一式的严格版**（`ab|pq` 一侧）。 -/
theorem strict_cherry_fst {T : Phylogram.{u, v} X} (hbin : T.toCladogram.IsBinary)
    {a b : X} (hab : a ≠ b) {w z : T.V} (haw : T.graph.Adj (T.leaf a) w)
    (hbw : T.graph.Adj (T.leaf b) w) (hwz : T.graph.Adj w z) (hza : z ≠ T.leaf a)
    (hzb : z ≠ T.leaf b) (hpos : ∀ e : Edge T.toCladogram, 0 < T.w e)
    {p q : X} (hpa : p ≠ a) (hpb : p ≠ b) (hqa : q ≠ a) (hqb : q ≠ b) :
    T.dist (T.leaf a) (T.leaf b) + T.dist (T.leaf p) (T.leaf q)
      < T.dist (T.leaf a) (T.leaf p) + T.dist (T.leaf b) (T.leaf q) := by
  have hab' : T.leaf a ≠ T.leaf b := fun h => hab (T.leaf.injective h)
  have hAB : T.dist (T.leaf a) (T.leaf b) = T.dist (T.leaf a) w + T.dist w (T.leaf b) :=
    T.dist_eq_add_of_adj_leaf_dist haw hab'.symm
  have hAP : T.dist (T.leaf a) (T.leaf p) = T.dist (T.leaf a) w + T.dist w (T.leaf p) :=
    T.dist_eq_add_of_adj_leaf_dist haw (fun h => hpa (T.leaf.injective h))
  have hBQ : T.dist (T.leaf b) (T.leaf q) = T.dist (T.leaf b) w + T.dist w (T.leaf q) :=
    T.dist_eq_add_of_adj_leaf_dist hbw (fun h => hqb (T.leaf.injective h))
  have hstrict := dist_lt_dist_add_dist_of_ne (T := T) hbin hab haw hbw hwz hza hzb hpos hpa hpb hqa hqb
  have hwb : T.dist w (T.leaf b) = T.dist (T.leaf b) w :=
    Phylo.TreeDist.dist_comm T w (T.leaf b)
  linarith

/-- ★★★ **原登记缺口已证**：二叉 ＋ 边权全正 ⇒ 樱桃的四点不等式**严格**。

（第二式 = 第一式交换 `p`、`q`；`d(p,q) = d(q,p)`。） -/
theorem strictCherry_of_isBinary_pos_gap_holds :
    Phylo.Stat.StrictCherry.strictCherry_of_isBinary_pos_gap.{u, v} (X := X) := by
  intro T hpos hbin a b hc p q hpq hpa hpb hqa hqb
  obtain ⟨hab, w, haw, hbw⟩ := hc
  obtain ⟨z, hwz, hza, hzb, -⟩ := exists_third T hbin hab haw hbw
  have h1 := strict_cherry_fst (T := T) hbin hab haw hbw hwz hza hzb hpos hpa hpb hqa hqb
  have h2 := strict_cherry_fst (T := T) hbin hab haw hbw hwz hza hzb hpos hqa hqb hpa hpb
  refine ⟨h1, ?_⟩
  rwa [Phylo.TreeDist.dist_comm T (T.leaf q) (T.leaf p)] at h2

end Phylo.Stat.StrictCherryProved
