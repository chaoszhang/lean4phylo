/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.TreeDistance
import Phylo.Split
import Phylo.InternalEdge
import Mathlib.Tactic

/-!
# `Phylo.LeafStatus` —— Weller 2023 的「叶状态」（leaf status）

**文献**：`references/md/Weller2023_NeighborJoining_LeafStatus.md`
（Weller, *A leaf-status perspective on Neighbor Joining*, 2023）。行号均指该 md 文件。

**设定（照抄文献 `:121–136`）**：`T : Phylogram X`（`Phylo/Core.lean`）= 无度 2 顶点的树；
`T.dist` = 唯一路径的边权和；叶 = `T.leaf x`。文献 `:124` 假设边权 `ω : E(T) → ℕ⁺`
（`:397–402` 说明其实只需**内部边**正权）。本文件的定理把所需的**正权假设显式写成参数**。

⚠️ **命名空间**：声明放在**根命名空间 `Phylogram`**（与 `Phylo/Core.lean` 的
`Phylogram.dist`、`Phylo/BunemanGraft.lean` 的 `Phylogram.dist_comm` 一致），
这样点记号 `T.leafStatus` 可用。

## 已完成（本文件，逐条对照本轮四项任务）

1. ★★ **叶状态**（文献 `:136`）：`Phylogram.leafStatus`（定义）、`leafStatus_def`、
   ★ `leafStatus_nonneg`、`leafStatus_leaf`、`leafStatus_leaf_comm`。
2. ★★★ **Observation 1**（文献 `:128`）：★★★ `exists_median_eq_half` —— 存在
   `q ∈ V(u–v 路径)` 使 `d(x,q) = ½(d(x,u)+d(x,v)−d(u,v))`，**且** `q` 使 `d(x,·)`
   在该路径上取**最小**（= 文献 `:126` 定义的「`x` 到路径 `p` 的距离」）。
   辅助：★★ `eq_add_dist_of_min_support`（中位点的「远端」距离分解）、
   `pos_walkDist_of_ne` / `pos_dist_of_ne`（正边权 ⟹ 不同顶点的距离为正）。
   ⚠️ 文献 `:126` 的 `d_T(x,p)` 是 `min_{y∈V(p)} d(x,y)`；若误读成「路径上**任意**一点 `p`」，
   该等式为**假**（反例见第 5 节的 docstring）。本文件证的是**文献的正确含义**。
3. ★★★ **Lemma 1**（文献 `:148–152`）：★★★ `leafStatus_sub`
   （`ℓ(u) − ℓ(v) = ω(uv)·(|L^{uv}_v| − |L^{uv}_u|)`，假设 `0 < ω(uv)`）；
   核心件：★★★ `leafStatus_leaf_sub`（逐叶符号恒等式）与 ★★★ `adj_dichotomy`（相邻边的 `±ω` 二分）、
   ★★ `eq_add_dist_of_notMem_support`、`cons_walkDist`（`Walk.cons` 的加权长度）。
4. ★★★ **Corollary 1**（文献 `:207`）：★★★ `leafStatus_minimizer_not_isLeaf` ——
   `|X| ≥ 3` 且正边权时，`ℓ` 最小的结点不是叶。
   辅助：★★ `eq_add_dist_of_ne_of_unique_adj`（叶的唯一邻居给出的距离分解）。
5. ★★★ **Observation 2**（文献 `:138–143`，第 6 节）：★★★ `pathLeafStatus`（路径的叶状态
   `ℓ_T(p) := Σ_{x∈X} d_T(x,p)`，其中 `d_T(x,p)` 是 ★★ `distToPath` = 到路径的最小距离，
   用投影点 ★★ `projOnPath` 表达）、★★★ `pathLeafStatus_eq`
   （`ℓ_T(p) = ½(ℓ_T(u) + ℓ_T(v) − |L(T)|·d(u,v))`）；
   辅助：★★★ `distToPath_eq_half`（投影距离公式）、`distToPath_le`、`distToPath_left/right`。
6. ★★★ **Lemma 2**（文献 `:213–214`，第 7–9 节）：★★★ `leafStatus_strict_mono` ——
   沿以 `ℓ` 最小者 `v₀` 为起点、相继相邻且单射的序列 `(v₀,…,v_k)`：
   `ℓ(v₀) ≤ ℓ(v₁) < ℓ(v₂) < … < ℓ(v_k)`（第一段**弱**、严格性从 `i = 1` 起）。
   地基（同时供 Lemma 3 用）：
   * §7 ★★ `dist_le_dist_of_inSide` / `inSide_of_dist_lt` / `eq_add_dist_of_inSide`
     —— **边侧 ⟷ 距离比较**（文献 `:130–133` 的 `L^{uv}_u` 与删边分量版等价）；
   * §8 ★★ `sideLeaves_subset_of_adj`、★★★ `sideLeaves_card_lt_of_adj`
     —— 侧集**严格嵌套**（文献 `:232–249`，**「无度 2」正是这里起作用**）；
   * §9 ★★★ `leafStatus_sub_card_sideLeaves` / `leafStatus_le_iff_card_sideLeaves` /
     `leafStatus_lt_iff_card_sideLeaves` —— **等价式 (2)**（文献 `:251–275`）；
   * §9 ★★★ `leafStatus_lt_of_leafStatus_le_of_adj` —— 局部一步。
7. ★★★ **Lemma 3**（文献 `:328–329`，第 10–11 节）：**`z(u,v) ≤ ℓ(w)` 一半已完成**：
   * ★★★ `dist_add_pathLeafStatus_le_leafStatus` ——
     `d(leaf u, leaf v) + ℓ_T(p) ≤ ℓ_T(w)`（`w` 在 `u–v` 路径上即可）；
   * ★★★ `eq_dist_add_pathLeafStatus_iff` —— **等号的精确刻画**：等号 ⟺ 每个第三者叶 `x`
     到 `w` 的距离等于它到路径的距离（`w` 是 `x` 的投影）；
   * ★★★ `eq_of_adj_adj` —— 文献的**几何条件 ⟹ 等号**（`w` 同时邻接两片叶，即 `p = (u,w,v)`）；
   * ★★★ `eq_imp_adj_adj`（§12）—— **几何反向**：等号（且 `w` 非叶）⟹ `w` 同时邻接两片叶
     （引擎 ★★★ `exists_distToPath_lt_of_not_adj` + ★★★ `mem_support_of_inSide_of_inSide`
     + ★★ `exists_adj_crossing` + ★★ `distToPath_comm`）；**Lemma 3 至此两向皆完成**；
   * 辅助：★★ `sum_eq_add_add_sum_erase`、`leafStatus_sub_dist_add_pathLeafStatus`、
     `dist_eq_add_of_mem_path_support`、★★ `eq_of_adj_leaf`、`support_eq_of_adj_adj`、
     `eq_or_eq_or_eq_of_mem_support_of_adj_adj`、`distToPath_nonneg`。

**额外假设一览（文献 `:124` 的正边权被显式参数化；本库 `w_nonneg` 只给 `≥ 0`）**：

* `leafStatus_leaf_sub` / `leafStatus_sub`：只需**该边**正权 `0 < T.wExt s(u,v)`
  （⚠️ `ω < 0` 时 Lemma 1 的恒等式**为假**）；
* `leafStatus_minimizer_not_isLeaf` / `pos_walkDist_of_ne` / `pos_dist_of_ne` /
  `eq_add_dist_of_min_support` / `exists_median_eq_half` / `pathLeafStatus_eq` /
  `leafStatus_strict_mono` 及其 §7–§9 地基 / §12 的 `eq_imp_adj_adj`（其引擎用 `0 < d(p,w)`）：
  全局正边权 `∀ e : Edge T.toCladogram, 0 < T.w e`（文献 `:124` 的 `ω : E(T) → ℕ⁺`；
  `:397–402` 说其实内部边正权已够）；
* §7 的 ★★ `dist_le_dist_of_inSide` / `inSide_of_dist_lt` **不需要正权**（只用 `w_nonneg`）；
  §8 的侧集嵌套、§12 的 ★★ `exists_adj_crossing` / ★★★ `mem_support_of_inSide_of_inSide`
  也**不需要正权**。

## ⬜ 未完成（未虚报）

* **无**（本轮任务的三项与 §12 的几何反向均已落地）。
  文献 Observation 1 的「路径」字面形式在本文件第 5 节已按**文献原意**
  （`min_{y∈V(p)} d(x,y)`）处理，并记录了题面字面版为假的反例。
-/

universe u v

namespace Phylogram

open SimpleGraph

variable {X : Type u}

noncomputable section

/-! ## 1. 叶状态 `leafStatus`（文献 `:136`）

文献定义 `ℓ_T(u) := ∑_{x∈L(T)} d_T(u, x)`。本库把叶标签集写成 `X`（`T.leaf : X ↪ V`），
故定义就是 `∑ x : X, T.dist u (T.leaf x)`。

⚠️ 命名：**不**用 `S` / `ell`（避免与 `Dissimilarity.S` / `Dissimilarity.ell` 混淆）——
`leafStatus` 是全库新名。 -/

section LeafStatus

variable [Fintype X] [DecidableEq X]

/-- ★★ **叶状态（leaf status）** —— Weller 2023 `:136`：

    `ℓ_T(u) := ∑_{x ∈ L(T)} d_T(u, x)` —— `u` 到**所有叶**的距离之和。

（文献的 `s_T(u)` 是「所有顶点」的 status；本定义只求和叶，故名 leaf-status。） -/
noncomputable def leafStatus (T : Phylogram.{u, v} X) (u : T.V) : ℝ :=
  ∑ x : X, T.dist u (T.leaf x)

omit [DecidableEq X] in
/-- `leafStatus` 的展开式（定义相等，便于 `rw`）。 -/
theorem leafStatus_def (T : Phylogram.{u, v} X) (u : T.V) :
    T.leafStatus u = ∑ x : X, T.dist u (T.leaf x) := rfl

omit [DecidableEq X] in
/-- ★ **叶状态非负**（每项 `dist` 非负）。 -/
theorem leafStatus_nonneg (T : Phylogram.{u, v} X) (u : T.V) :
    0 ≤ T.leafStatus u := by
  rw [leafStatus_def]
  exact Finset.sum_nonneg fun x _ => Phylo.TreeDist.dist_nonneg T u (T.leaf x)

omit [DecidableEq X] in
/-- **叶上的叶状态**：`ℓ_T(leaf x)` 的展开形式。 -/
theorem leafStatus_leaf (T : Phylogram.{u, v} X) (x : X) :
    T.leafStatus (T.leaf x) = ∑ y : X, T.dist (T.leaf x) (T.leaf y) := rfl

omit [DecidableEq X] in
/-- **叶上的叶状态（对称形式）**：`ℓ_T(leaf x) = ∑_y d(leaf y, leaf x)`（`dist_comm`）。 -/
theorem leafStatus_leaf_comm (T : Phylogram.{u, v} X) (x : X) :
    T.leafStatus (T.leaf x) = ∑ y : X, T.dist (T.leaf y) (T.leaf x) := by
  rw [leafStatus_def]
  exact Finset.sum_congr rfl fun y _ => Phylo.TreeDist.dist_comm T (T.leaf x) (T.leaf y)

end LeafStatus

/-! ## 2. 相邻边上的 `±ω` 二分（Lemma 1 的逐叶核心）

文献 `:148–152` 的证明第一行把每个叶 `x` 归入 `L^{uv}_u` 或 `L^{uv}_v`。Lean 化是：

> 对相邻的 `u, v` 与任意顶点 `y`，`d(y,v) − d(y,u)` **恰好为 `±ω(uv)`**。

实现用 **`cons` 技巧**（不需要 Mathlib 没有的 `IsPath.append`）：取 `v→y` 的唯一路径 `P`。
若 `u ∉ P.support`，则把 `u` 接在 `P` 前面仍是路径（`Walk.cons_isPath_iff`）
⟹ `d(u,y) = ω + d(v,y)`；否则用 ★★ `dist_eq_add_of_mem_support` 在 `u` 处劈开 `P`
⟹ `d(v,y) = ω + d(u,y)`。 -/

section Adj

variable (T : Phylogram.{u, v} X)

/-- **`Walk.cons` 的加权长度**：`walkDist (cons h p) = wExt s(a,b) + walkDist p`。

（本文件只 `import Phylo.TreeDistance`；`Phylo/BunemanGraft.lean` 有同内容的
`Phylogram.walkDist_cons` —— 名字不同，两文件同时 import 不冲突。） -/
theorem cons_walkDist {a b c : T.V} (h : T.graph.Adj a b) (p : T.graph.Walk b c) :
    T.walkDist (SimpleGraph.Walk.cons h p) = T.wExt s(a, b) + T.walkDist p := by
  simp only [Phylogram.walkDist, SimpleGraph.Walk.edges_cons, List.map_cons, List.sum_cons]

/-- ★★ **`u` 不在 `v→y` 路径上时的距离分解**：`d(u,y) = ω(uv) + d(v,y)`。

`u ∉ support` 使 `cons` 拼出的走法仍是路径（`Walk.cons_isPath_iff`），
再由 ★★ `dist_eq_walkDist_of_isPath` 与 `cons_walkDist` 立得。 -/
theorem eq_add_dist_of_notMem_support {u v y : T.V} (h : T.graph.Adj u v)
    (hy : u ∉ (T.existsUnique_path v y).choose.support) :
    T.dist u y = T.wExt s(u, v) + T.dist v y := by
  have hP : (T.existsUnique_path v y).choose.IsPath :=
    (T.existsUnique_path v y).choose_spec.1
  have hp : (SimpleGraph.Walk.cons h (T.existsUnique_path v y).choose).IsPath :=
    (SimpleGraph.Walk.cons_isPath_iff h _).mpr ⟨hP, hy⟩
  have h1 : T.dist u y = T.walkDist (SimpleGraph.Walk.cons h (T.existsUnique_path v y).choose) :=
    Phylo.TreeDist.dist_eq_walkDist_of_isPath T _ hp
  have h2 : T.dist v y = T.walkDist (T.existsUnique_path v y).choose :=
    Phylo.TreeDist.dist_eq_walkDist_of_isPath T _ hP
  have h3 : T.walkDist (SimpleGraph.Walk.cons h (T.existsUnique_path v y).choose)
      = T.wExt s(u, v) + T.walkDist (T.existsUnique_path v y).choose :=
    cons_walkDist T h _
  linarith

/-- ★★★ **相邻边的 `±ω` 二分**（Lemma 1 的逐点核心）：

对相邻的 `u, v` 与**任意**顶点 `y`，`d(y,v)` 与 `d(y,u)` 之差恰为 `±ω(uv)`。 -/
theorem adj_dichotomy {u v y : T.V} (h : T.graph.Adj u v) :
    T.dist y v = T.dist y u + T.wExt s(u, v) ∨ T.dist y u = T.dist y v + T.wExt s(u, v) := by
  by_cases hy : u ∈ (T.existsUnique_path v y).choose.support
  · left
    have hP : (T.existsUnique_path v y).choose.IsPath :=
      (T.existsUnique_path v y).choose_spec.1
    have h1 : T.dist v y = T.dist v u + T.dist u y :=
      Phylo.TreeDist.dist_eq_add_of_mem_support T _ hP hy
    rw [Phylo.TreeDist.dist_comm T v y, Phylo.TreeDist.dist_comm T v u,
      Phylo.TreeDist.dist_comm T u y, Phylo.TreeDist.dist_eq_wExt_of_adj T h] at h1
    linarith
  · right
    have h1 : T.dist u y = T.wExt s(u, v) + T.dist v y := eq_add_dist_of_notMem_support T h hy
    rw [Phylo.TreeDist.dist_comm T u y, Phylo.TreeDist.dist_comm T v y] at h1
    linarith

end Adj

/-! ## 3. Lemma 1（文献 `:148–152`）

> **Lemma 1.** 设 `uv ∈ E(T)`，则 `ℓ(u) − ℓ(v) = ω(uv)·(|L^{uv}_v| − |L^{uv}_u|)`，
> 其中 `L^{uv}_u := {x ∈ L(T) : d_T(x,u) < d_T(x,v)}`。

⚠️ **所加假设（诚实记录）**：文献 `:124` 假设 `ω : E(T) → ℕ⁺`（正边权）。本库
`Phylogram.w_nonneg` 只给 `≥ 0`，而 `ω = 0` 时恒等式仍成立、`ω < 0` 时**不成立**
（见 `leafStatus_leaf_sub` 的 docstring），故本文件把 `0 < T.wExt s(u,v)` 写成显式参数。 -/

section Lemma1

variable [Fintype X] [DecidableEq X]
variable (T : Phylogram.{u, v} X)

omit [Fintype X] [DecidableEq X] in
/-- ★★★ **逐叶的符号恒等式**（Lemma 1 的证明核心）：对每个 taxon 标签 `x`，

    `d(leaf x, u) − d(leaf x, v) = ω·[d(leaf x, v) < d(leaf x, u)] − ω·[d(leaf x, u) < d(leaf x, v)]`。

由 ★★★ `adj_dichotomy`：`d(leaf x, v)` 与 `d(leaf x, u)` 之差恰为 `±ω`，
故 `ω > 0` 时「谁更近」正好决定符号。⚠️ `ω < 0` 时该恒等式为**假**。 -/
theorem leafStatus_leaf_sub {u v : T.V} (h : T.graph.Adj u v)
    (hω : 0 < T.wExt s(u, v)) (x : X) :
    T.dist (T.leaf x) u - T.dist (T.leaf x) v
      = T.wExt s(u, v) * (if T.dist (T.leaf x) v < T.dist (T.leaf x) u then (1 : ℝ) else 0)
        - T.wExt s(u, v) * (if T.dist (T.leaf x) u < T.dist (T.leaf x) v then (1 : ℝ) else 0) := by
  rcases adj_dichotomy T h (y := T.leaf x) with hd | hd
  · split_ifs with h1 h2 <;> linarith
  · split_ifs with h1 h2 <;> linarith

omit [DecidableEq X] in
/-- ★★★ **Lemma 1（Weller 2023 `:148–152`）**：对**相邻**的 `u, v` 与 `ω := ω(uv) > 0`，

    `ℓ(u) − ℓ(v) = ω · (|L^{uv}_v| − |L^{uv}_u|)`，

其中 `L^{uv}_u := {x ∈ X : d(leaf x, u) < d(leaf x, v)}`（文献写 `{x ∈ L(T) : d_T(x,u) < d_T(x,v)}`；
本库把叶标签集写成 `X`，故用 `Finset.univ.filter`）。

⚠️ **额外假设**：`0 < T.wExt s(u,v)`（文献 `:124` 的正边权；`:397–402` 说明内部边正权已足够）。 -/
theorem leafStatus_sub {u v : T.V} (h : T.graph.Adj u v) (hω : 0 < T.wExt s(u, v)) :
    T.leafStatus u - T.leafStatus v
      = T.wExt s(u, v)
        * (((Finset.univ.filter fun x : X => T.dist (T.leaf x) v < T.dist (T.leaf x) u).card : ℝ)
          - ((Finset.univ.filter fun x : X => T.dist (T.leaf x) u < T.dist (T.leaf x) v).card : ℝ)) := by
  have hsum : T.leafStatus u - T.leafStatus v
      = ∑ x : X, (T.dist (T.leaf x) u - T.dist (T.leaf x) v) := by
    rw [leafStatus_def, leafStatus_def, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun x _ => by
      rw [Phylo.TreeDist.dist_comm T u (T.leaf x), Phylo.TreeDist.dist_comm T v (T.leaf x)]
  rw [hsum, Finset.sum_congr rfl fun x _ => leafStatus_leaf_sub T h hω x,
    Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_boole,
    Finset.sum_boole]
  ring

end Lemma1

/-! ## 4. Corollary 1（文献 `:207`）

> **Corollary 1.** 设 `T` 是至少三片叶的树、`x` 使 `ℓ(x)` 最小，则 `x` **不是叶**。

证明是 Lemma 1 的直接推论：设 `u = leaf x` 是叶、`v` 是其唯一邻居。
对每个 taxon `y`，`leaf y ≠ u` 时 `u→leaf y` 的路径**必经 `v`**（`u` 只有 `v` 一个邻居），
故 `d(leaf y, u) = ω + d(leaf y, v)`；而 `y = x` 时该式为 `0 − ω = −ω`。于是

    `ℓ(u) − ℓ(v) = (|X| − 1)·ω − ω = (|X| − 2)·ω > 0`（`|X| ≥ 3` 且 `ω > 0`），

与 `ℓ(u)` 的最小性矛盾。

⚠️ **所加假设（诚实记录）**：文献 `:124` 的 `ω : E(T) → ℕ⁺`（**全局正边权**）——
本库 `Phylogram.w_nonneg` 只给 `≥ 0`，故把 `∀ e, 0 < T.w e` 写成显式参数。
（`:397–402` 指出其实只需**内部边**正权；本文件用全局正权，是文献 `:124` 的强假设，
证明中实际只用到「`u` 的挂边正权」。）`|X| ≥ 3` 即文献的「at least three leaves」。 -/

section Corollary1

variable [Fintype X] [DecidableEq X]
variable (T : Phylogram.{u, v} X)

omit [Fintype X] [DecidableEq X] in
/-- ★★ **叶的唯一邻居给出的距离分解**：设 `a` 是叶、`b` 是它**唯一**的邻居
（`huniq` 编码「唯一」），则对任意 `z ≠ a` 有 `d(a,z) = ω(ab) + d(b,z)`。

证明：`z ≠ a` 时 `a→z` 的唯一路径非空（`Walk.exists_eq_cons_of_ne`），
其首边从 `a` 出发，由 `huniq` 必为 `ab`，故路径 = `ab` + 剩余部分。 -/
theorem eq_add_dist_of_ne_of_unique_adj {a b z : T.V}
    (huniq : ∀ w : T.V, T.graph.Adj a w → w = b) (hz : z ≠ a) :
    T.dist a z = T.wExt s(a, b) + T.dist b z := by
  obtain ⟨w, haw, P', hP'⟩ :=
    SimpleGraph.Walk.exists_eq_cons_of_ne (Ne.symm hz) (T.existsUnique_path a z).choose
  have hP : (T.existsUnique_path a z).choose.IsPath :=
    (T.existsUnique_path a z).choose_spec.1
  have hP'path : P'.IsPath := by
    rw [hP'] at hP
    exact SimpleGraph.Walk.IsPath.of_cons hP
  have h1 : T.dist a z = T.walkDist (SimpleGraph.Walk.cons haw P') := by
    rw [Phylo.TreeDist.dist_eq_walkDist_of_isPath T (T.existsUnique_path a z).choose hP, hP']
  have h2 : T.walkDist (SimpleGraph.Walk.cons haw P') = T.wExt s(a, w) + T.walkDist P' :=
    cons_walkDist T haw P'
  have h3 : T.walkDist P' = T.dist w z :=
    (Phylo.TreeDist.dist_eq_walkDist_of_isPath T P' hP'path).symm
  have h4 : T.wExt s(a, w) = T.wExt s(a, b) := by rw [huniq w haw]
  have h5 : T.dist w z = T.dist b z := by rw [huniq w haw]
  linarith

/-- ★★★ **Corollary 1（Weller 2023 `:207`）**：`ℓ` 最小的结点**不是叶**。

对 `T : Phylogram X`：若 `X` 至少含 3 个 taxon、每条边的权为正，且
`∀ w, ℓ(u) ≤ ℓ(w)`，则 `u` 不是任何叶 `T.leaf x`。 -/
theorem leafStatus_minimizer_not_isLeaf (hcard : 3 ≤ Fintype.card X)
    (hpos : ∀ e : Edge T.toCladogram, 0 < T.w e)
    {u : T.V} (hmin : ∀ w : T.V, T.leafStatus u ≤ T.leafStatus w) :
    ¬ ∃ x : X, T.leaf x = u := by
  rintro ⟨x, rfl⟩
  have hdeg : T.graph.degree (T.leaf x) = 1 :=
    (T.leaf_iff_degree_one (T.leaf x)).mp ⟨x, rfl⟩
  obtain ⟨v, huv, huniq⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hdeg
  have hωpos : 0 < T.wExt s(T.leaf x, v) := by
    rw [Phylo.TreeDist.wExt_eq_w T ((SimpleGraph.mem_edgeSet T.graph).mpr huv)]
    exact hpos ⟨s(T.leaf x, v), (SimpleGraph.mem_edgeSet T.graph).mpr huv⟩
  have hterm : ∀ y : X, T.dist (T.leaf x) (T.leaf y) - T.dist v (T.leaf y)
      = if y = x then -T.wExt s(T.leaf x, v) else T.wExt s(T.leaf x, v) := by
    intro y
    by_cases hy : y = x
    · have h1 : T.dist (T.leaf x) (T.leaf y) = 0 := by rw [hy, Phylogram.dist_self]
      have h2 : T.dist v (T.leaf y) = T.wExt s(T.leaf x, v) := by
        rw [hy, Phylo.TreeDist.dist_comm T v (T.leaf x),
          Phylo.TreeDist.dist_eq_wExt_of_adj T huv]
      have h3 : (if y = x then -T.wExt s(T.leaf x, v) else T.wExt s(T.leaf x, v))
          = -T.wExt s(T.leaf x, v) :=
        ite_eq_left hy
      rw [h1, h2, h3]
      ring
    · rw [ite_eq_right hy]
      have hne : T.leaf y ≠ T.leaf x := fun h => hy (T.leaf.injective h)
      have h1 : T.dist (T.leaf x) (T.leaf y) = T.wExt s(T.leaf x, v) + T.dist v (T.leaf y) :=
        eq_add_dist_of_ne_of_unique_adj T huniq hne
      linarith
  have hsum : T.leafStatus (T.leaf x) - T.leafStatus v
      = ∑ y : X, (if y = x then -T.wExt s(T.leaf x, v) else T.wExt s(T.leaf x, v)) := by
    rw [leafStatus_def, leafStatus_def, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun y _ => hterm y
  have hcalc : ∑ y : X, (if y = x then -T.wExt s(T.leaf x, v) else T.wExt s(T.leaf x, v))
      = ((Fintype.card X : ℝ) - 2) * T.wExt s(T.leaf x, v) := by
    have h1 : 1 ≤ Fintype.card X := Fintype.card_pos_iff.mpr ⟨x⟩
    rw [← Finset.sum_erase_add (Finset.univ : Finset X)
      (fun y : X => if y = x then -T.wExt s(T.leaf x, v) else T.wExt s(T.leaf x, v))
      (Finset.mem_univ x), ite_eq_left rfl]
    have hrest : ∑ y ∈ (Finset.univ.erase x),
        (if y = x then -T.wExt s(T.leaf x, v) else T.wExt s(T.leaf x, v))
        = ∑ _y ∈ (Finset.univ.erase x), T.wExt s(T.leaf x, v) := by
      refine Finset.sum_congr rfl fun y hy => ?_
      rw [ite_eq_right (Finset.mem_erase.mp hy).1]
    rw [hrest, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ x),
      Finset.card_univ, nsmul_eq_mul, Nat.cast_sub h1, Nat.cast_one]
    ring
  have hlt : T.leafStatus v < T.leafStatus (T.leaf x) := by
    have h2 : (0 : ℝ) < (Fintype.card X : ℝ) - 2 := by
      have h3 : (3 : ℝ) ≤ (Fintype.card X : ℝ) := by exact_mod_cast hcard
      linarith
    nlinarith [hsum.trans hcalc, hωpos, h2]
  exact absurd (hmin v) (not_le.mpr hlt)

end Corollary1

/-! ## 5. Observation 1（文献 `:128`）——「`x` 到 `u–v` 路径的距离」

文献 `:126` 把 `d_T(x,p)` 定义为 **`x` 到路径 `p` 上各点距离的最小值**：

> `d_T(x,p) := min_{u ∈ V(p)} d(u,x)`，

Observation 1（`:128`）断言该最小值 `= ½(d(x,u) + d(x,v) − d(u,v))`，即取到最小值的那个点
（`x` 在路径上的**投影**／中位点）满足等式。

⚠️ **与题面字面表述的差异（诚实记录）**：若把 `p` 读成路径上的**任意一点**，则该等式为**假**。
反例：四点树 `({x,u} | {v,w})`（内部边 `c₁—c₂`，权全为 `1`），`u–v` 路径是 `u—c₁—c₂—v`，
则 `½(d(x,u)+d(x,v)−d(u,v)) = ½(2+3−3) = 1 = d(x,c₁)`，但路径上的点 `p := c₂` 给出 `d(x,c₂) = 2`。
故本文件证明的是**文献的正确含义**（下一条定理：存在性 + 最小性 + 等式），
而不是「任意 `p ∈ V(p)` 都满足等式」。 -/

section Observation1

variable (T : Phylogram.{u, v} X)

/-- **正边权 ⟹ 非平凡 walk 的加权长度为正**（文献 `:124` 的 `ω : E(T) → ℕ⁺`）。 -/
theorem pos_walkDist_of_ne (hpos : ∀ e : Edge T.toCladogram, 0 < T.w e) {z q : T.V}
    (p : T.graph.Walk z q) (h : z ≠ q) : 0 < T.walkDist p := by
  obtain ⟨w, hzw, p', rfl⟩ := SimpleGraph.Walk.exists_eq_cons_of_ne h p
  rw [cons_walkDist T hzw p']
  have hw : 0 < T.wExt s(z, w) := by
    rw [Phylo.TreeDist.wExt_eq_w T ((SimpleGraph.mem_edgeSet T.graph).mpr hzw)]
    exact hpos ⟨s(z, w), (SimpleGraph.mem_edgeSet T.graph).mpr hzw⟩
  have h0 : 0 ≤ T.walkDist p' := Phylo.TreeDist.walkDist_nonneg T p'
  linarith

/-- **正边权 ⟹ 不同顶点的距离为正**（`pos_walkDist_of_ne` + 唯一路径）。 -/
theorem pos_dist_of_ne (hpos : ∀ e : Edge T.toCladogram, 0 < T.w e) {z q : T.V}
    (h : z ≠ q) : 0 < T.dist z q := by
  rw [Phylo.TreeDist.dist_eq_walkDist_of_isPath T (T.existsUnique_path z q).choose
    (T.existsUnique_path z q).choose_spec.1]
  exact pos_walkDist_of_ne T hpos (T.existsUnique_path z q).choose h

/-- ★★ **中位点的「远端」距离分解**：设 `Q : a → b` 是路径、`q ∈ Q.support` 且 `q` 使
`d(x,·)` 在 `Q.support` 上取最小，则 `d(x,b) = d(x,q) + d(q,b)`。

证明：把 `Q` 在 `q` 处劈成 `Q₁.append Q₂`（★★ `IsPath.mem_support_iff_exists_append`），
考虑走法 `Z := (x→q 的唯一路径).append Q₂`。若 `Z` 是路径，`dist_eq_add_of_isPath_append` 直接给出结论；
否则由 `support_append` + `List.nodup_append` 得 `Z.support` 有重复，即存在
`z ∈ (x→q 路径).support ∩ Q₂.support.tail`。由最小性 `d(x,q) ≤ d(x,z)`，
由 ★★ `dist_eq_add_of_mem_support` 有 `d(x,q) = d(x,z) + d(z,q)`，故 `d(z,q) = 0`；
正权下 `pos_dist_of_ne` 逼出 `z = q`，与 `z ∈ Q₂.support.tail`（`Q₂` 是路径，不含 `q`）矛盾。 -/
theorem eq_add_dist_of_min_support (hpos : ∀ e : Edge T.toCladogram, 0 < T.w e) {a b x : T.V}
    (Q : T.graph.Walk a b) (hQ : Q.IsPath) {q : T.V} (hq : q ∈ Q.support)
    (hmin : ∀ y ∈ Q.support, T.dist x q ≤ T.dist x y) :
    T.dist x b = T.dist x q + T.dist q b := by
  obtain ⟨Q₁, Q₂, _hQ₁, hQ₂, hQeq⟩ :=
    (SimpleGraph.Walk.IsPath.mem_support_iff_exists_append hQ).mp hq
  have hR : (T.existsUnique_path x q).choose.IsPath :=
    (T.existsUnique_path x q).choose_spec.1
  by_cases hZ : ((T.existsUnique_path x q).choose.append Q₂).IsPath
  · exact Phylo.TreeDist.dist_eq_add_of_isPath_append T _ Q₂ hZ
  · exfalso
    have hsupp : ((T.existsUnique_path x q).choose.append Q₂).support
        = (T.existsUnique_path x q).choose.support ++ Q₂.support.tail :=
      SimpleGraph.Walk.support_append _ Q₂
    have hnnd : ¬ ((T.existsUnique_path x q).choose.support ++ Q₂.support.tail).Nodup := by
      intro hnd
      exact hZ (SimpleGraph.Walk.IsPath.mk' (hsupp.symm ▸ hnd))
    rw [List.nodup_append] at hnnd
    have hC : ¬ (∀ u ∈ (T.existsUnique_path x q).choose.support,
        ∀ v ∈ Q₂.support.tail, u ≠ v) := by
      intro hC
      exact hnnd ⟨hR.support_nodup, hQ₂.support_nodup.tail, hC⟩
    push Not at hC
    obtain ⟨z, hzR, z', hz'tail, hzz'⟩ := hC
    rw [← hzz'] at hz'tail
    have hzQ : z ∈ Q.support := by
      rw [hQeq, SimpleGraph.Walk.support_append]
      exact List.mem_append_right _ hz'tail
    have hle : T.dist x q ≤ T.dist x z := hmin z hzQ
    have hadd : T.dist x q = T.dist x z + T.dist z q :=
      Phylo.TreeDist.dist_eq_add_of_mem_support T _ hR hzR
    have hzero : T.dist z q = 0 := by
      have h0 : 0 ≤ T.dist z q := Phylo.TreeDist.dist_nonneg T z q
      linarith
    have hzq : z = q := by
      by_contra hne
      have hp := pos_dist_of_ne T hpos hne
      linarith
    have hqnot : q ∉ Q₂.support.tail := by
      intro hmem
      have hnd := hQ₂.support_nodup
      rw [← SimpleGraph.Walk.cons_tail_support Q₂] at hnd
      exact (List.nodup_cons.mp hnd).1 hmem
    exact hqnot (hzq ▸ hz'tail)

/-- ★★★ **Observation 1（Weller 2023 `:128`，正确读法）**：

设 `p` 是 `u–v` 的唯一路径。则存在 `q ∈ V(p)`（`x` 在 `p` 上的投影／中位点）使

    `d(x,q) = ½·(d(x,u) + d(x,v) − d(u,v))`

**且** `q` 是 `d(x,·)` 在 `V(p)` 上的**最小值点** —— 即此值正是文献 `:126` 定义的
「`x` 到路径 `p` 的距离」`d_T(x,p) = min_{y∈V(p)} d(x,y)`。

⚠️ **所加假设**：`∀ e, 0 < T.w e`（文献 `:124` 的正边权）—— 证明中只用到
「`d(z,q) = 0 ⟹ z = q`」（`pos_dist_of_ne`）。 -/
theorem exists_median_eq_half (hpos : ∀ e : Edge T.toCladogram, 0 < T.w e) (x u v : T.V) :
    ∃ q ∈ (T.existsUnique_path u v).choose.support,
      T.dist x q = (T.dist x u + T.dist x v - T.dist u v) / 2 ∧
      ∀ y ∈ (T.existsUnique_path u v).choose.support, T.dist x q ≤ T.dist x y := by
  set P := (T.existsUnique_path u v).choose with hPdef
  have hP : P.IsPath := (T.existsUnique_path u v).choose_spec.1
  have hne : P.support.toFinset.Nonempty :=
    ⟨u, List.mem_toFinset.mpr (SimpleGraph.Walk.start_mem_support P)⟩
  obtain ⟨q, hqS, hqmin⟩ :=
    Finset.exists_min_image P.support.toFinset (fun y => T.dist x y) hne
  have hq : q ∈ P.support := List.mem_toFinset.mp hqS
  have hmin : ∀ y ∈ P.support, T.dist x q ≤ T.dist x y :=
    fun y hy => hqmin y (List.mem_toFinset.mpr hy)
  refine ⟨q, hq, ?_, hmin⟩
  have hav : T.dist x v = T.dist x q + T.dist q v :=
    eq_add_dist_of_min_support T hpos P hP hq hmin
  have hq' : q ∈ P.reverse.support := by
    rw [SimpleGraph.Walk.support_reverse]
    exact List.mem_reverse.mpr hq
  have hmin' : ∀ y ∈ P.reverse.support, T.dist x q ≤ T.dist x y := by
    intro y hy
    rw [SimpleGraph.Walk.support_reverse] at hy
    exact hmin y (List.mem_reverse.mp hy)
  have hb : T.dist x u = T.dist x q + T.dist q u :=
    eq_add_dist_of_min_support T hpos P.reverse hP.reverse hq' hmin'
  have hc : T.dist u v = T.dist u q + T.dist q v :=
    Phylo.TreeDist.dist_eq_add_of_mem_support T P hP hq
  have hqu : T.dist q u = T.dist u q := Phylo.TreeDist.dist_comm T q u
  linarith

end Observation1

/-! ## 6. 路径的叶状态与 ★★★ Observation 2（文献 `:138–143`）

文献 `:126` 定义 **`x` 到路径 `p` 的距离**为路径上各点距离的**最小值**
`d_T(x,p) := min_{y∈V(p)} d_T(x,y)`；文献 `:138` 定义**路径的叶状态**

    `ℓ_T(p) := Σ_{x∈L(T)} d_T(x,p)`，

Observation 2（`:143`）断言 `ℓ_T(p) = ½(ℓ_T(u) + ℓ_T(v) − |L(T)|·d(u,v))`。

本库的实现：**不**把 `min` 做成 `def`，而是用 ★★★ `exists_median_eq_half` 给出的**投影点**
`projOnPath u v x`（`x` 在 `u–v` 路径上取到该最小值的点）来表达：
`distToPath u v x := d(x, projOnPath u v x)`。`|L(T)|` 就是 `Fintype.card X`。 -/

section PathLeafStatus

variable (T : Phylogram.{u, v} X)

/-- `u–v` 路径的顶点集（`support` 的 `Finset` 形式）非空（含 `u`）。 -/
theorem support_toFinset_nonempty (u v : T.V) :
    ((T.existsUnique_path u v).choose.support.toFinset).Nonempty :=
  ⟨u, List.mem_toFinset.mpr (SimpleGraph.Walk.start_mem_support _)⟩

/-- **投影点的存在性**：`u–v` 路径上存在一点，使得到 `x` 的距离在路径上取最小。 -/
theorem exists_projOnPath (u v x : T.V) :
    ∃ y ∈ (T.existsUnique_path u v).choose.support,
      ∀ z ∈ (T.existsUnique_path u v).choose.support, T.dist x y ≤ T.dist x z := by
  classical
  obtain ⟨y, hy, hmin⟩ :=
    Finset.exists_min_image _ (fun y => T.dist x y) (support_toFinset_nonempty T u v)
  exact ⟨y, List.mem_toFinset.mp hy, fun z hz => hmin z (List.mem_toFinset.mpr hz)⟩

/-- ★★ **`x` 在 `u–v` 路径上的投影点**（取到 `d_T(x,p)` 的点）。 -/
noncomputable def projOnPath (u v x : T.V) : T.V := (exists_projOnPath T u v x).choose

/-- ★ 投影点落在路径上。 -/
theorem projOnPath_mem (u v x : T.V) :
    T.projOnPath u v x ∈ (T.existsUnique_path u v).choose.support :=
  (exists_projOnPath T u v x).choose_spec.1

/-- ★ 投影点使 `d(x,·)` 在路径上取最小。 -/
theorem projOnPath_min (u v x : T.V) {z : T.V}
    (hz : z ∈ (T.existsUnique_path u v).choose.support) :
    T.dist x (T.projOnPath u v x) ≤ T.dist x z :=
  (exists_projOnPath T u v x).choose_spec.2 z hz

/-- ★★ **点到路径的距离** `d_T(x,p) = min_{y∈V(p)} d_T(x,y)`（文献 `:126`），
用投影点表达。 -/
noncomputable def distToPath (u v x : T.V) : ℝ := T.dist x (T.projOnPath u v x)

/-- ★ `d_T(x,p)` 不超过路径上任一点到 `x` 的距离。 -/
theorem distToPath_le {u v x z : T.V} (hz : z ∈ (T.existsUnique_path u v).choose.support) :
    T.distToPath u v x ≤ T.dist x z :=
  projOnPath_min T u v x hz

/-- ★ `d_T(x,p)` 由路径上的投影点取到。 -/
theorem exists_distToPath_eq (u v x : T.V) :
    ∃ z ∈ (T.existsUnique_path u v).choose.support, T.distToPath u v x = T.dist x z :=
  ⟨T.projOnPath u v x, projOnPath_mem T u v x, rfl⟩

/-- ★★★ **投影点的距离公式**（= Observation 1 的内容，用于 Observation 2）：

    `d_T(x,p) = ½(d(x,u) + d(x,v) − d(u,v))`。 -/
theorem distToPath_eq_half (hpos : ∀ e : Edge T.toCladogram, 0 < T.w e) (u v x : T.V) :
    T.distToPath u v x = (T.dist x u + T.dist x v - T.dist u v) / 2 := by
  obtain ⟨q, hq, hformula, hmin⟩ := exists_median_eq_half T hpos x u v
  refine le_antisymm ?_ ?_
  · exact (distToPath_le T hq).trans_eq hformula
  · rw [← hformula]
    exact hmin _ (projOnPath_mem T u v x)

end PathLeafStatus

section Observation2

variable [Fintype X] [DecidableEq X]
variable (T : Phylogram.{u, v} X)

/-- ★★★ **路径的叶状态**（文献 `:138`）：`ℓ_T(p) := Σ_{x∈X} d_T(x, p)`，
其中 `p` 是 `u–v` 的唯一路径、`d_T(x,p)` 是 ★★ `distToPath`。 -/
noncomputable def pathLeafStatus (u v : T.V) : ℝ := ∑ x : X, T.distToPath u v (T.leaf x)

omit [DecidableEq X] in
/-- ★★★ **Observation 2（Weller 2023 `:143`）**：

    `ℓ_T(p) = ½·(ℓ_T(u) + ℓ_T(v) − |L(T)|·d(u,v))`，

其中 `p` 是 `u–v` 路径、`|L(T)| = Fintype.card X`（本库的叶恰是 `X` 的像）。

⚠️ **所加假设**：文献 `:124` 的正边权 `∀ e, 0 < T.w e`（经 ★★★ `distToPath_eq_half`，
即 Observation 1，用到「`d(z,q) = 0 ⟹ z = q`」）。 -/
theorem pathLeafStatus_eq (hpos : ∀ e : Edge T.toCladogram, 0 < T.w e) (u v : T.V) :
    T.pathLeafStatus u v
      = (T.leafStatus u + T.leafStatus v - (Fintype.card X : ℝ) * T.dist u v) / 2 := by
  have hpt : ∀ x : X, T.distToPath u v (T.leaf x)
      = (T.dist (T.leaf x) u + T.dist (T.leaf x) v - T.dist u v) / 2 :=
    fun x => distToPath_eq_half T hpos u v (T.leaf x)
  have h1 : (∑ x : X, T.dist (T.leaf x) u) = T.leafStatus u := by
    rw [leafStatus_def]
    exact Finset.sum_congr rfl fun x _ => (Phylo.TreeDist.dist_comm T u (T.leaf x)).symm
  have h2 : (∑ x : X, T.dist (T.leaf x) v) = T.leafStatus v := by
    rw [leafStatus_def]
    exact Finset.sum_congr rfl fun x _ => (Phylo.TreeDist.dist_comm T v (T.leaf x)).symm
  have h3 : (∑ _x : X, T.dist u v) = (Fintype.card X : ℝ) * T.dist u v := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  simp only [pathLeafStatus]
  rw [Finset.sum_congr rfl fun x _ => hpt x, ← Finset.sum_div, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, h1, h2, h3]

end Observation2

/-! ## 7. 边侧 ⟷ 距离比较（Lemma 2 / Lemma 3 的地基）

设 `u, v` **相邻**、`e := s(u,v)`。文献 `:130–133` 把 `L^{uv}_u` 定义为**距离**较近的叶集，
而 `Phylo/Split.lean` 的 `T.inSide e u y` / `T.sideLeaves e u` 用**删边分量**表述。
本节的桥：

* ★★ `dist_le_dist_of_inSide`：在 `u` 侧 ⟹ `d(y,u) ≤ d(y,v)`；
* ★★ `inSide_of_dist_lt`：`d(y,v) < d(y,u)` ⟹ 在 `v` 侧。

两者合起来：**哪一侧 ⟺ 离谁更近**（这正是 Lemma 2 的 (2) 式里
`L←_i` / `L→_i` 与删边叶侧集可以互换的依据）。

证明都只用到一件事：若 `y → v` 的唯一路径 `W` 用了边 `e`，则由 ★★
`dist_eq_add_of_mem_support`（取 `u ∈ W.support`）得 `d(y,v) = d(y,u) + ω ≥ d(y,u)`；
反之 `e ∉ W.edges` 时 `W.toDeleteEdges` 给出 `T - e` 中 `y → v` 的可达性。 -/

section SideDist

variable [Fintype X] [DecidableEq X]
variable (T : Phylogram.{u, v} X)

omit [Fintype X] [DecidableEq X] in
/-- ★★ **走向「远端」的路径不能用 `s(u,v)`**：`u,v` 相邻且 `d(y,v) < d(y,u)` 时，
`y → v` 的唯一路径不含边 `s(u,v)`。

（否则 `u ∈ W.support`，`d(y,v) = d(y,u) + d(u,v) ≥ d(y,u)`，与 `d(y,v) < d(y,u)` 矛盾。） -/
theorem not_mem_edges_of_dist_lt {u v y : T.V}
    (h : T.dist y v < T.dist y u) :
    s(u, v) ∉ (T.existsUnique_path y v).choose.edges := by
  intro hmem
  have hW : ((T.existsUnique_path y v).choose).IsPath := (T.existsUnique_path y v).choose_spec.1
  have hu : u ∈ (T.existsUnique_path y v).choose.support :=
    SimpleGraph.Walk.fst_mem_support_of_mem_edges _ hmem
  have hadd : T.dist y v = T.dist y u + T.dist u v :=
    Phylo.TreeDist.dist_eq_add_of_mem_support T _ hW hu
  have h0 : 0 ≤ T.dist u v := Phylo.TreeDist.dist_nonneg T u v
  linarith

omit [Fintype X] [DecidableEq X] in
/-- ★★ **较近 ⟹ 在该侧**：若 `d(y,v) < d(y,u)`（`u,v` 相邻），则 `y` 在 `s(u,v)` 的 `v` 侧
（即 `T - s(u,v)` 中 `y` 与 `v` 可达）。 -/
theorem inSide_of_dist_lt {u v y : T.V} (h : T.dist y v < T.dist y u) :
    T.inSide s(u, v) v y := by
  have hne := not_mem_edges_of_dist_lt T h
  have hreach : (T.graph.deleteEdges {s(u, v)}).Reachable y v :=
    (SimpleGraph.Walk.toDeleteEdges {s(u, v)} _ (by
      intro e' he' hmem
      exact hne (Set.mem_singleton_iff.mp hmem ▸ he'))).reachable
  exact reachable_comm.mp hreach

/-- ★★ **在该侧 ⟹ 距离不大**：若 `y` 在 `s(u,v)` 的 `u` 侧（`u,v` 相邻），则 `d(y,u) ≤ d(y,v)`。

（否则 `d(y,v) < d(y,u)`；由上一条 `y` 与 `v` 在 `T - s(u,v)` 中可达，与 `y` 与 `u` 可达
合起来给出 `u` 与 `v` 在该图中可达 —— 与「边是桥」矛盾。） -/
theorem dist_le_dist_of_inSide {u v y : T.V} (huv : T.graph.Adj u v)
    (hy : T.inSide s(u, v) u y) : T.dist y u ≤ T.dist y v := by
  by_contra hcon
  rw [not_le] at hcon
  have hne := not_mem_edges_of_dist_lt T hcon
  have hreach : (T.graph.deleteEdges {s(u, v)}).Reachable y v :=
    (SimpleGraph.Walk.toDeleteEdges {s(u, v)} _ (by
      intro e' he' hmem
      exact hne (Set.mem_singleton_iff.mp hmem ▸ he'))).reachable
  have hyu : (T.graph.deleteEdges {s(u, v)}).Reachable y u := reachable_comm.mp hy
  exact T.not_reachable_deleteEdges_of_adj huv (hyu.symm.trans hreach)

/-- ★★ **在 `u` 侧 ⟹ 严格更近**（正边权）：`y` 在 `s(u,v)` 的 `u` 侧时
`d(y,u) < d(y,v)`（由 `adj_dichotomy`：两侧之差恰为 `ω(s(u,v)) > 0`）。 -/
theorem dist_lt_of_inSide {u v y : T.V} (huv : T.graph.Adj u v)
    (hω : 0 < T.wExt s(u, v)) (hy : T.inSide s(u, v) u y) : T.dist y u < T.dist y v := by
  have hle := dist_le_dist_of_inSide T huv hy
  rcases adj_dichotomy T huv (y := y) with hd | hd
  · linarith
  · linarith

/-- ★★ **在 `u` 侧的距离分解**（正边权）：`d(y,v) = d(y,u) + ω(s(u,v))`。 -/
theorem eq_add_dist_of_inSide {u v y : T.V} (huv : T.graph.Adj u v)
    (hω : 0 < T.wExt s(u, v)) (hy : T.inSide s(u, v) u y) :
    T.dist y v = T.dist y u + T.wExt s(u, v) := by
  have hle := dist_le_dist_of_inSide T huv hy
  rcases adj_dichotomy T huv (y := y) with hd | hd
  · exact hd
  · exfalso; linarith

end SideDist

/-! ## 8. 侧集的包含与严格嵌套（Lemma 2 的「无度 2」入口）

路径上相继三点 `a — x — b`（`a ≠ b`）：

* ★★ `sideLeaves_subset_of_adj`：`a` 侧（关于边 `s(a,x)`）⊆ `x` 侧（关于边 `s(x,b)`）；
* ★★★ `sideLeaves_card_lt_of_adj`：再加上「`x` 无度 2」时包含是**严格**的
  （第三条边 `x—c` 的分支里必有叶，它落在 `x` 侧而不在 `a` 侧）。

这正是文献 `:232–249` 里 `L→_i ⊂ L←_{i−1}` 那一步 —— **真包含**正是「无度 2 顶点」起作用之处。 -/

section SideNesting

variable [Fintype X] [DecidableEq X]
variable (T : Phylogram.{u, v} X)

/-- ★★ **侧包含**：`a — x — b` 为路径上相继三点（`a ≠ b`）时，
关于边 `s(a,x)` 的 `a` 侧 ⊆ 关于边 `s(x,b)` 的 `x` 侧。

证明：取 `z` 在 `a` 侧。因 `b` 与 `x` 相邻且边 `s(x,b) ≠ s(a,x)`，`b` 与 `x` 关于 `s(a,x)` 同侧，
故 `b ∉ z 侧`；于是 `z 侧` 不含 `x`、`b`，由 ★★ `inSide_deleteEdges_of_inSide`（删边不破坏同侧）
得 `z` 与 `a` 关于 `s(x,b)` 同侧；再把基准从 `a` 换到 `x`（`s(a,x) ≠ s(x,b)` + `inSide_congr_of_adj`）。 -/
theorem sideLeaves_subset_of_adj {a x b : T.V} (hax : T.graph.Adj a x)
    (hxb : T.graph.Adj x b) (hab : a ≠ b) :
    T.sideLeaves s(a, x) a ⊆ T.sideLeaves s(x, b) x := by
  have hne : s(x, b) ≠ s(a, x) := by
    intro h
    have hb : b ∈ s(a, x) := h ▸ (Sym2.mem_iff.mpr (Or.inr rfl) : b ∈ s(x, b))
    rcases Sym2.mem_iff.mp hb with h1 | h1
    · exact hab h1.symm
    · exact hxb.ne h1.symm
  intro z hz
  rw [T.mem_sideLeaves_iff_inSide] at hz ⊢
  have hx_not : ¬ T.inSide s(a, x) (T.leaf z) x := by
    have hboth := T.not_inSide_both hax (y := T.leaf z)
    exact fun h => hboth ⟨hz, (T.inSide_comm _ _ _).mp h⟩
  have hb_not : ¬ T.inSide s(a, x) (T.leaf z) b := by
    intro hb
    exact hx_not (((T.inSide_congr_of_adj (e₁ := s(a, x)) (u₁ := T.leaf z) hxb hne).mpr hb))
  have h1 : T.inSide s(x, b) (T.leaf z) a :=
    T.inSide_deleteEdges_of_inSide (e₁ := s(a, x)) (e₂ := s(x, b)) (c := x) (d := b)
      (p := T.leaf z) (q := a) rfl ((T.inSide_comm _ _ _).mp hz) hx_not hb_not
  have h2 : T.inSide s(x, b) (T.leaf z) x :=
    (T.inSide_congr_of_adj (e₁ := s(x, b)) (u₁ := T.leaf z) hax hne.symm).mp h1
  exact (T.inSide_comm _ _ _).mp h2

omit [Fintype X] [DecidableEq X] in
/-- ★★ **`x` 有两条以上不同的相邻边 ⟹ 度 ≥ 2**。 -/
theorem two_le_degree_of_adj_adj {a x b : T.V} (hax : T.graph.Adj a x)
    (hxb : T.graph.Adj x b) (hab : a ≠ b) : 2 ≤ T.graph.degree x := by
  have hsub : ({a, b} : Finset T.V) ⊆ T.graph.neighborFinset x := by
    intro y hy
    rw [Finset.mem_insert, Finset.mem_singleton] at hy
    rw [SimpleGraph.mem_neighborFinset]
    rcases hy with rfl | rfl
    · exact hax.symm
    · exact hxb
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_pair hab, SimpleGraph.card_neighborFinset_eq_degree] at hcard
  exact hcard

/-- ★★★ **侧集的严格嵌套**（Lemma 2 的严格性来源，文献 `:232–249`）：

`a — x — b` 相继（`a ≠ b`）且 `x` **无度 2** 时

    `|a 侧(s(a,x))| < |x 侧(s(x,b))|`。

证明：包含由 ★★ `sideLeaves_subset_of_adj` 给出；严格性由**第三条边** `x—c`（`c ∉ {a,b}`，
存在性来自 `deg x ≥ 3`）的分支取叶 `z`（`sideLeaves_nonempty_of_adj`）：`z` 落在 `x` 侧
（对边 `s(x,b)`）而不落在 `a` 侧（对边 `s(a,x)`）—— 两次都用 ★★ `sideLeaves_subset_of_adj` 加「补侧」。 -/
theorem sideLeaves_card_lt_of_adj {a x b : T.V} (hax : T.graph.Adj a x)
    (hxb : T.graph.Adj x b) (hab : a ≠ b) (hdeg : T.graph.degree x ≠ 2) :
    (T.sideLeaves s(a, x) a).card < (T.sideLeaves s(x, b) x).card := by
  have htwo := two_le_degree_of_adj_adj T hax hxb hab
  have hthree : 3 ≤ T.graph.degree x := by omega
  -- 第三条边 x—c
  obtain ⟨c, hc, hca, hcb⟩ : ∃ c ∈ T.graph.neighborFinset x, c ≠ a ∧ c ≠ b := by
    by_contra hcon
    rw [not_exists] at hcon
    have hsub : T.graph.neighborFinset x ⊆ ({a, b} : Finset T.V) := by
      intro y hy
      have hy' := hcon y
      rw [Finset.mem_insert, Finset.mem_singleton]
      by_contra hnb
      rw [not_or] at hnb
      exact hy' ⟨hy, hnb.1, hnb.2⟩
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_pair hab, SimpleGraph.card_neighborFinset_eq_degree] at hcard
    omega
  have hxc : T.graph.Adj x c := (SimpleGraph.mem_neighborFinset T.graph x c).mp hc
  -- c 分支里的叶 z
  obtain ⟨z, hz⟩ := T.sideLeaves_nonempty_of_adj hxc.symm
  have hzR : z ∈ T.sideLeaves s(x, b) x :=
    sideLeaves_subset_of_adj T hxc.symm hxb hcb hz
  have hznotL : z ∉ T.sideLeaves s(a, x) a := by
    have hz' : z ∈ T.sideLeaves s(x, a) x :=
      sideLeaves_subset_of_adj T hxc.symm hax.symm hca hz
    rw [Sym2.eq_swap, T.sideLeaves_compl_adj hax] at hz'
    exact Finset.mem_compl.mp hz'
  refine Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
    ⟨sideLeaves_subset_of_adj T hax hxb hab, ?_⟩)
  intro heq
  exact hznotL (heq.symm ▸ hzR)

end SideNesting

/-! ## 9. Lemma 2（文献 `:213–214`）：沿以 `ℓ` 最小者为起点的路径，`ℓ` 弱增后严格增

正文（含 (2) 式的 Lean 形式）：

* ★★ `pos_wExt_of_adj` —— 相邻边的权为正（全局正边权假设）；
* ★★★ `leafStatus_le_iff_card_sideLeaves` / ★★★ `leafStatus_lt_iff_card_sideLeaves`
  —— **等价式 (2)**：`ℓ(u) ≤ ℓ(v) ⟺ |L(T)| ≤ 2|u 侧叶|`（`<` 同理）；
* ★★★ `leafStatus_lt_of_leafStatus_le_of_adj` —— **局部一步**（用 ★★★ `sideLeaves_card_lt_of_adj`
  的严格嵌套 + 等价式 (2) 的算术）；
* ★★★ `leafStatus_strict_mono_of_walk` —— **Lemma 2 本体**
  （路径用 `v : ℕ → T.V` 在 `{0,…,k}` 上「相继相邻 + 单射」表述）。 -/

section Lemma2

variable [Fintype X] [DecidableEq X]
variable (T : Phylogram.{u, v} X)

omit [Fintype X] [DecidableEq X] in
/-- ★★ **相邻边的权为正**（文献 `:124` 的 `ω : E(T) → ℕ⁺`）。 -/
theorem pos_wExt_of_adj (hpos : ∀ e : Edge T.toCladogram, 0 < T.w e) {u v : T.V}
    (h : T.graph.Adj u v) : 0 < T.wExt s(u, v) := by
  rw [Phylo.TreeDist.wExt_eq_w T ((SimpleGraph.mem_edgeSet T.graph).mpr h)]
  exact hpos ⟨s(u, v), (SimpleGraph.mem_edgeSet T.graph).mpr h⟩

/-- ★★★ **Lemma 1 的「侧集」形式**（等价式 (2) 的来源）：`u, v` 相邻、`ω(s(u,v)) > 0` 时

    `ℓ(u) − ℓ(v) = ω(s(u,v)) · (|L(T)| − 2·|u 侧叶|)`。

证明：由 ★★★ `leafStatus_sub`，`ℓ(u) − ℓ(v) = ω(|L^{uv}_v| − |L^{uv}_u|)`；两个「更近」集互补
（★ `adj_dichotomy` + `ω > 0`），故 `|L^{uv}_v| − |L^{uv}_u| = |L(T)| − 2|L^{uv}_u|`；
再由 §7 的桥把 `L^{uv}_u = {x : d(x,u) < d(x,v)}` 换成删边叶侧集 `T.sideLeaves s(u,v) u`。 -/
theorem leafStatus_sub_card_sideLeaves {u v : T.V} (huv : T.graph.Adj u v)
    (hω : 0 < T.wExt s(u, v)) :
    T.leafStatus u - T.leafStatus v
      = T.wExt s(u, v) * ((Fintype.card X : ℝ) - 2 * ((T.sideLeaves s(u, v) u).card : ℝ)) := by
  have hcompl : ∀ x : X, ¬ (T.dist (T.leaf x) v < T.dist (T.leaf x) u) ↔
      T.dist (T.leaf x) u < T.dist (T.leaf x) v := by
    intro x
    constructor
    · intro h
      rcases adj_dichotomy T huv (y := T.leaf x) with hd | hd
      · linarith
      · exfalso; linarith
    · intro h h'; linarith
  have hcard_part :
      ((Finset.univ.filter
          (fun x : X => T.dist (T.leaf x) v < T.dist (T.leaf x) u)).card : ℝ)
        + ((Finset.univ.filter
          (fun x : X => T.dist (T.leaf x) u < T.dist (T.leaf x) v)).card : ℝ)
        = (Fintype.card X : ℝ) := by
    have hnat := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset X))
      (p := fun x : X => T.dist (T.leaf x) v < T.dist (T.leaf x) u)
    have hf : (Finset.univ.filter
          (fun x : X => ¬ (T.dist (T.leaf x) v < T.dist (T.leaf x) u)))
        = Finset.univ.filter (fun x : X => T.dist (T.leaf x) u < T.dist (T.leaf x) v) :=
      Finset.filter_congr fun x _ => hcompl x
    rw [hf, Finset.card_univ] at hnat
    exact_mod_cast hnat
  have hset : (Finset.univ.filter (fun x : X => T.dist (T.leaf x) u < T.dist (T.leaf x) v))
      = T.sideLeaves s(u, v) u := by
    ext x
    rw [Finset.mem_filter, T.mem_sideLeaves_iff_inSide]
    constructor
    · rintro ⟨_, hx⟩
      have h := inSide_of_dist_lt T (u := v) (v := u) (y := T.leaf x) hx
      rwa [Sym2.eq_swap] at h
    · intro hx
      refine ⟨Finset.mem_univ _, ?_⟩
      have hle := dist_le_dist_of_inSide T huv hx
      rcases adj_dichotomy T huv (y := T.leaf x) with hd | hd
      · linarith
      · linarith
  rw [leafStatus_sub T huv hω]
  have hB : ((Finset.univ.filter
        (fun x : X => T.dist (T.leaf x) u < T.dist (T.leaf x) v)).card : ℝ)
      = ((T.sideLeaves s(u, v) u).card : ℝ) := by rw [hset]
  have hmain : ((Finset.univ.filter
          (fun x : X => T.dist (T.leaf x) v < T.dist (T.leaf x) u)).card : ℝ)
        - ((Finset.univ.filter
          (fun x : X => T.dist (T.leaf x) u < T.dist (T.leaf x) v)).card : ℝ)
      = (Fintype.card X : ℝ) - 2 * ((T.sideLeaves s(u, v) u).card : ℝ) := by
    linarith [hcard_part, hB]
  rw [hmain]

/-- ★★★ **等价式 (2)**（文献 `:251–275`）：`u, v` 相邻、`ω(s(u,v)) > 0` 时

    `ℓ(u) ≤ ℓ(v) ⟺ |L(T)| ≤ 2·|u 侧叶|`。 -/
theorem leafStatus_le_iff_card_sideLeaves {u v : T.V} (huv : T.graph.Adj u v)
    (hω : 0 < T.wExt s(u, v)) :
    T.leafStatus u ≤ T.leafStatus v ↔
      (Fintype.card X : ℝ) ≤ 2 * ((T.sideLeaves s(u, v) u).card : ℝ) := by
  have hiff : T.leafStatus u ≤ T.leafStatus v ↔ T.leafStatus u - T.leafStatus v ≤ 0 := by
    constructor <;> intro h <;> linarith
  rw [hiff, leafStatus_sub_card_sideLeaves T huv hω]
  constructor <;> intro h <;> nlinarith [hω, h]

/-- ★★★ **等价式 (2) 的严格版**：`ℓ(u) < ℓ(v) ⟺ |L(T)| < 2·|u 侧叶|`。 -/
theorem leafStatus_lt_iff_card_sideLeaves {u v : T.V} (huv : T.graph.Adj u v)
    (hω : 0 < T.wExt s(u, v)) :
    T.leafStatus u < T.leafStatus v ↔
      (Fintype.card X : ℝ) < 2 * ((T.sideLeaves s(u, v) u).card : ℝ) := by
  have hiff : T.leafStatus u < T.leafStatus v ↔ T.leafStatus u - T.leafStatus v < 0 := by
    constructor <;> intro h <;> linarith
  rw [hiff, leafStatus_sub_card_sideLeaves T huv hω]
  constructor <;> intro h <;> nlinarith [hω, h]

/-- ★★★ **局部一步**：`a — x — b` 相继（`a ≠ b`）、`x` 无度 2，且 `ℓ(a) ≤ ℓ(x)`，则
`ℓ(x) < ℓ(b)`。

证明：由等价式 (2) 得 `|L(T)| ≤ 2|a 侧|`；由 ★★★ `sideLeaves_card_lt_of_adj` 得
`|a 侧| < |x 侧|`（**真包含**，即「无度 2」之处），故 `|L(T)| < 2|x 侧|`，
再由等价式 (2) 的严格版得 `ℓ(x) < ℓ(b)`。 -/
theorem leafStatus_lt_of_leafStatus_le_of_adj (hpos : ∀ e : Edge T.toCladogram, 0 < T.w e)
    {a x b : T.V} (hax : T.graph.Adj a x) (hxb : T.graph.Adj x b) (hab : a ≠ b)
    (hle : T.leafStatus a ≤ T.leafStatus x) : T.leafStatus x < T.leafStatus b := by
  have h1 := (leafStatus_le_iff_card_sideLeaves T hax (pos_wExt_of_adj T hpos hax)).mp hle
  have h2 := sideLeaves_card_lt_of_adj T hax hxb hab (T.no_degree_two x)
  have h3 : 2 * ((T.sideLeaves s(a, x) a).card : ℝ) + 2
      ≤ 2 * ((T.sideLeaves s(x, b) x).card : ℝ) := by
    have h2' : (T.sideLeaves s(a, x) a).card + 1 ≤ (T.sideLeaves s(x, b) x).card :=
      Nat.succ_le_of_lt h2
    have h2'' : ((T.sideLeaves s(a, x) a).card : ℝ) + 1
        ≤ ((T.sideLeaves s(x, b) x).card : ℝ) := by exact_mod_cast h2'
    linarith
  have h4 : (Fintype.card X : ℝ) < 2 * ((T.sideLeaves s(x, b) x).card : ℝ) := by linarith
  exact (leafStatus_lt_iff_card_sideLeaves T hxb (pos_wExt_of_adj T hpos hxb)).mpr h4

/-- ★★★ **Lemma 2（Weller 2023 `:213–214`）**：设 `T` 是正边权、无度 2 顶点的树，
`(v₀, v₁, …, v_k)` 是 `T` 中的一条**路径**（相继相邻 + 在 `{0,…,k}` 上单射），
且 `v₀` 的叶状态在 `T` 中最小。则

    `ℓ(v₀) ≤ ℓ(v₁) < ℓ(v₂) < … < ℓ(v_k)`。

⚠️ 第一段是**弱**不等式（只来自 `v₀` 的最小性）；严格性从 `i = 1` 起
（局部一步 ★★★ `leafStatus_lt_of_leafStatus_le_of_adj` 对 `i ≥ 1` 归纳）。 -/
theorem leafStatus_strict_mono (hpos : ∀ e : Edge T.toCladogram, 0 < T.w e)
    {k : ℕ} (v : ℕ → T.V) (hadj : ∀ i, i < k → T.graph.Adj (v i) (v (i + 1)))
    (hinj : ∀ i j, i ≤ k → j ≤ k → v i = v j → i = j)
    (hmin : ∀ w : T.V, T.leafStatus (v 0) ≤ T.leafStatus w) :
    T.leafStatus (v 0) ≤ T.leafStatus (v 1) ∧
      ∀ i, 1 ≤ i → i < k → T.leafStatus (v i) < T.leafStatus (v (i + 1)) := by
  refine ⟨hmin (v 1), ?_⟩
  intro i
  induction i with
  | zero => intro hi _; exact absurd hi (by omega)
  | succ j ih =>
    intro hi hk
    rcases Nat.eq_or_lt_of_le hi with h1 | h2
    · have hj : j = 0 := by omega
      subst hj
      exact leafStatus_lt_of_leafStatus_le_of_adj T hpos (hadj 0 (by omega)) (hadj 1 (by omega))
        (fun h => by have hc := hinj 0 2 (by omega) (by omega) h; omega) (hmin (v 1))
    · have hj : 1 ≤ j := by omega
      exact leafStatus_lt_of_leafStatus_le_of_adj T hpos (hadj j (by omega))
        (hadj (j + 1) (by omega))
        (fun h => by have hc := hinj j (j + 2) (by omega) (by omega) h; omega)
        (le_of_lt (ih hj (by omega)))

end Lemma2

/-! ## 10. Lemma 3（文献 `:328–329`）

> **Lemma 3.** `T` 正边权、无度 2 顶点，`u, v ∈ L(T)`，`w` 是 `u–v` 路径 `p` 的**内部**结点。
> 则 `z(u,v) ≤ ℓ(w)`，且等号成立 ⟺ `p = (u,w,v)`（路径只有 `u, w, v` 三点）。

树层版本：`z(u,v) = d(leaf u, leaf v) + ℓ_T(p)`，其中 `ℓ_T(p)` 是 ★★★ `pathLeafStatus`。
本文件证出：

* ★★★ `dist_add_pathLeafStatus_le_leafStatus` —— **`z(u,v) ≤ ℓ(w)`**（`w` 在路径上即可，不需
  「内部」假设：不等式的证明只用 `d(x,p) ≤ d(x,w)` 与 `d(u,v) = d(u,w)+d(w,v)`）；
* ★★★ `eq_dist_add_pathLeafStatus_iff` —— **等号的精确刻画**：等号 ⟺ 每个「第三者」叶 `x`
  到 `w` 的距离 = 它到路径的距离（即 `w` 是 `x` 在 `p` 上的投影）。

⬜ **尚未形式化**：把上一条的投影式条件换成文献的几何条件 `p = (u,w,v)`
（即 `w` 同时邻接两片叶）⟺ 的**几何方向**（等号 ⟹ `p` 只有三点）——
需要「路径上某内部顶点的第三条分支必含一片投影落在该顶点的叶」这一步
（用 `no_degree_two` + ★★★ `sideLeaves_card_lt_of_adj` 那套侧集工具可行，本轮未做）。 -/

section Lemma3

variable [Fintype X] [DecidableEq X]
variable (T : Phylogram.{u, v} X)

/-- 求和拆成「`u`、`v` 两项 + 其余」（`u ≠ v`）。 -/
theorem sum_eq_add_add_sum_erase {M : Type*} [AddCommMonoid M] {u v : X} (huv : u ≠ v)
    (f : X → M) :
    ∑ x : X, f x = f u + f v + ∑ x ∈ (Finset.univ.erase u).erase v, f x := by
  rw [← Finset.sum_erase_add (Finset.univ : Finset X) f (Finset.mem_univ u)]
  rw [← Finset.sum_erase_add ((Finset.univ : Finset X).erase u) f
    (Finset.mem_erase.mpr ⟨huv.symm, Finset.mem_univ v⟩)]
  abel

omit [Fintype X] [DecidableEq X] in
/-- ★ `d_T(x,p) ≥ 0`。 -/
theorem distToPath_nonneg (u v x : T.V) : 0 ≤ T.distToPath u v x :=
  Phylo.TreeDist.dist_nonneg T x (T.projOnPath u v x)

omit [Fintype X] [DecidableEq X] in
/-- ★ 路径左端点到路径的距离为 `0`（它就是投影点）。 -/
theorem distToPath_left (u v : T.V) : T.distToPath u v u = 0 := by
  have h1 : T.distToPath u v u ≤ T.dist u u :=
    distToPath_le T (SimpleGraph.Walk.start_mem_support (T.existsUnique_path u v).choose)
  rw [Phylogram.dist_self] at h1
  have h2 := distToPath_nonneg T u v u
  linarith

omit [Fintype X] [DecidableEq X] in
/-- ★ 路径右端点到路径的距离为 `0`。 -/
theorem distToPath_right (u v : T.V) : T.distToPath u v v = 0 := by
  have h1 : T.distToPath u v v ≤ T.dist v v :=
    distToPath_le T (SimpleGraph.Walk.end_mem_support (T.existsUnique_path u v).choose)
  rw [Phylogram.dist_self] at h1
  have h2 := distToPath_nonneg T u v v
  linarith

omit [Fintype X] [DecidableEq X] in
/-- `w` 在 `u–v` 路径上时 `d(leaf u, leaf v) = d(leaf u, w) + d(leaf v, w)`。 -/
theorem dist_eq_add_of_mem_path_support {u v : X} {w : T.V}
    (hw : w ∈ (T.existsUnique_path (T.leaf u) (T.leaf v)).choose.support) :
    T.dist (T.leaf u) (T.leaf v) = T.dist (T.leaf u) w + T.dist (T.leaf v) w := by
  have hP : ((T.existsUnique_path (T.leaf u) (T.leaf v)).choose).IsPath :=
    (T.existsUnique_path (T.leaf u) (T.leaf v)).choose_spec.1
  have h := Phylo.TreeDist.dist_eq_add_of_mem_support T _ hP hw
  rw [h, Phylo.TreeDist.dist_comm T w (T.leaf v)]

/-- **差的求和恒等式**（Lemma 3 的核心计算）：`w` 在 `u–v` 路径 `p` 上时

    `ℓ(w) − (d(u,v) + ℓ(p)) = Σ_{x ∉ {u,v}} [d(leaf x, w) − d(leaf x, p)]`。 -/
theorem leafStatus_sub_dist_add_pathLeafStatus {u v : X} (huv : u ≠ v) {w : T.V}
    (hw : w ∈ (T.existsUnique_path (T.leaf u) (T.leaf v)).choose.support) :
    T.leafStatus w
        - (T.dist (T.leaf u) (T.leaf v) + T.pathLeafStatus (T.leaf u) (T.leaf v))
      = ∑ x ∈ (Finset.univ.erase u).erase v,
          (T.dist (T.leaf x) w - T.distToPath (T.leaf u) (T.leaf v) (T.leaf x)) := by
  have hp : T.pathLeafStatus (T.leaf u) (T.leaf v)
      = T.distToPath (T.leaf u) (T.leaf v) (T.leaf u)
        + T.distToPath (T.leaf u) (T.leaf v) (T.leaf v)
        + ∑ x ∈ (Finset.univ.erase u).erase v,
            T.distToPath (T.leaf u) (T.leaf v) (T.leaf x) := by
    rw [pathLeafStatus]
    exact sum_eq_add_add_sum_erase (X := X) huv _
  rw [distToPath_left, distToPath_right, add_zero, zero_add] at hp
  have hw' : T.leafStatus w
      = T.dist (T.leaf u) w + T.dist (T.leaf v) w
        + ∑ x ∈ (Finset.univ.erase u).erase v, T.dist (T.leaf x) w := by
    rw [leafStatus_def]
    rw [sum_eq_add_add_sum_erase (X := X) huv (fun x : X => T.dist w (T.leaf x))]
    rw [Phylo.TreeDist.dist_comm T w (T.leaf u), Phylo.TreeDist.dist_comm T w (T.leaf v),
      show (∑ x ∈ (Finset.univ.erase u).erase v, T.dist w (T.leaf x))
        = ∑ x ∈ (Finset.univ.erase u).erase v, T.dist (T.leaf x) w from
        Finset.sum_congr rfl fun x _ => Phylo.TreeDist.dist_comm T w (T.leaf x)]
  rw [hp, hw', dist_eq_add_of_mem_path_support T hw, Finset.sum_sub_distrib]
  ring

/-- ★★★ **Lemma 3 的不等式一半（树层形式）**（文献 `:328–329`）：

`u ≠ v` 是两片叶、`w` 是 `u–v` 路径 `p` 上的点，则

    `z(u,v) = d(leaf u, leaf v) + ℓ_T(p) ≤ ℓ_T(w)`。 -/
theorem dist_add_pathLeafStatus_le_leafStatus {u v : X} (huv : u ≠ v) {w : T.V}
    (hw : w ∈ (T.existsUnique_path (T.leaf u) (T.leaf v)).choose.support) :
    T.dist (T.leaf u) (T.leaf v) + T.pathLeafStatus (T.leaf u) (T.leaf v) ≤ T.leafStatus w := by
  have hdiff := leafStatus_sub_dist_add_pathLeafStatus T huv hw
  have hnn : 0 ≤ ∑ x ∈ (Finset.univ.erase u).erase v,
      (T.dist (T.leaf x) w - T.distToPath (T.leaf u) (T.leaf v) (T.leaf x)) :=
    Finset.sum_nonneg fun x _ => by
      have := distToPath_le T (u := T.leaf u) (v := T.leaf v) (x := T.leaf x) hw
      linarith
  linarith

/-- ★★★ **Lemma 3 的等号刻画（树层形式）**：在上一条的假设下，

    `z(u,v) = ℓ(w) ⟺ 每个「第三者」叶 `x` 都是 `w` 更近`（`d(leaf x, w) = d(leaf x, p)`）。

文献把右端进一步写成几何条件 `p = (u,w,v)`；两者的等价见文件头 `⬜`。 -/
theorem eq_dist_add_pathLeafStatus_iff {u v : X} (huv : u ≠ v) {w : T.V}
    (hw : w ∈ (T.existsUnique_path (T.leaf u) (T.leaf v)).choose.support) :
    T.dist (T.leaf u) (T.leaf v) + T.pathLeafStatus (T.leaf u) (T.leaf v) = T.leafStatus w ↔
      ∀ x : X, T.leaf x ≠ T.leaf u → T.leaf x ≠ T.leaf v →
        T.distToPath (T.leaf u) (T.leaf v) (T.leaf x) = T.dist (T.leaf x) w := by
  have hdiff := leafStatus_sub_dist_add_pathLeafStatus T huv hw
  have hnn : ∀ x ∈ (Finset.univ.erase u).erase v,
      0 ≤ T.dist (T.leaf x) w - T.distToPath (T.leaf u) (T.leaf v) (T.leaf x) := fun x _ => by
    have := distToPath_le T (u := T.leaf u) (v := T.leaf v) (x := T.leaf x) hw
    linarith
  have hsum0 : T.leafStatus w
        - (T.dist (T.leaf u) (T.leaf v) + T.pathLeafStatus (T.leaf u) (T.leaf v)) = 0 ↔
      ∀ x ∈ (Finset.univ.erase u).erase v,
        T.dist (T.leaf x) w - T.distToPath (T.leaf u) (T.leaf v) (T.leaf x) = 0 := by
    rw [hdiff]
    exact Finset.sum_eq_zero_iff_of_nonneg hnn
  constructor
  · intro h x hx hxv
    have hmem : x ∈ (Finset.univ.erase u).erase v := by
      rw [Finset.mem_erase, Finset.mem_erase]
      exact ⟨fun hh => hxv (congrArg T.leaf hh), fun hh => hx (congrArg T.leaf hh),
        Finset.mem_univ x⟩
    have hz := hsum0.mp (by linarith)
    have := hz x hmem
    linarith
  · intro h
    have hz : ∀ x ∈ (Finset.univ.erase u).erase v,
        T.dist (T.leaf x) w - T.distToPath (T.leaf u) (T.leaf v) (T.leaf x) = 0 := by
      intro x hx
      rw [Finset.mem_erase, Finset.mem_erase] at hx
      have hxu : T.leaf x ≠ T.leaf u := fun hh => hx.2.1 (T.leaf.injective hh)
      have hxv : T.leaf x ≠ T.leaf v := fun hh => hx.1 (T.leaf.injective hh)
      have := h x hxu hxv
      linarith
    linarith [hsum0.mpr hz]

end Lemma3

/-! ## 11. Lemma 3 的等号条件：几何方向 `p = (u,w,v) ⟹ 等号`

文献 `:328–329` 把等号条件写成 `p = (u,w,v)`（`w` **同时邻接**两片叶 `u, v`）。
本节证出该几何条件 ⟹ 等号（另一半「等号 ⟹ `p = (u,w,v)`」见文件头 `⬜`）：

* ★★ `eq_of_adj_leaf` —— 叶的唯一邻居；
* ★★ `support_eq_of_adj_adj` —— `w` 同时邻接 `u, v` 时 `u–v` 路径的支持集恰为 `[leaf u, w, leaf v]`；
* ★★★ `eq_of_adj_adj` —— 于是对每个第三者叶 `x` 都有 `d(x,w) = d(x,p)`（两片叶的唯一邻居
  分别是 `w`，故 `d(x, leaf u) = ω(uw) + d(x,w) ≥ d(x,w)`，对 `v` 同理），
  由 ★★★ `eq_dist_add_pathLeafStatus_iff` 得等号。 -/

section Lemma3Adj

variable [Fintype X] [DecidableEq X]
variable (T : Phylogram.{u, v} X)

omit [Fintype X] [DecidableEq X] in
/-- ★★ **叶的唯一邻居**：`T.leaf u` 的邻居只能是 `w`。 -/
theorem eq_of_adj_leaf (u : X) {w y : T.V} (huw : T.graph.Adj (T.leaf u) w)
    (hy : T.graph.Adj (T.leaf u) y) : y = w := by
  have hdeg : T.graph.degree (T.leaf u) = 1 := (T.leaf_iff_degree_one (T.leaf u)).mp ⟨u, rfl⟩
  obtain ⟨w', _, huniq⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hdeg
  rw [huniq y hy, huniq w huw]

omit [Fintype X] [DecidableEq X] in
/-- ★★ **`w` 同时邻接两片叶时，`u–v` 路径的支持集恰为 `[leaf u, w, leaf v]`**
（即 `p = (u,w,v)`）。 -/
theorem support_eq_of_adj_adj {u v : X} (huv : u ≠ v) {w : T.V}
    (huw : T.graph.Adj (T.leaf u) w) (hwv : T.graph.Adj w (T.leaf v)) :
    (T.existsUnique_path (T.leaf u) (T.leaf v)).choose.support = [T.leaf u, w, T.leaf v] := by
  have hQ : (SimpleGraph.Walk.cons huw (SimpleGraph.Walk.cons hwv SimpleGraph.Walk.nil)).IsPath := by
    rw [SimpleGraph.Walk.cons_isPath_iff]
    refine ⟨?_, ?_⟩
    · rw [SimpleGraph.Walk.cons_isPath_iff]
      exact ⟨SimpleGraph.Walk.IsPath.nil, by simp [hwv.ne]⟩
    · intro h
      rcases List.mem_cons.mp h with h | h
      · exact huw.ne h
      · exact huv (T.leaf.injective (List.mem_singleton.mp h))
  have huniq := (T.existsUnique_path (T.leaf u) (T.leaf v)).choose_spec.2 _ hQ
  rw [← huniq]
  rfl

omit [Fintype X] [DecidableEq X] in
/-- ★★ 若 `w` 同时邻接两片叶 `u, v`，则 `u–v` 路径上的点只有 `leaf u`、`w`、`leaf v`。 -/
theorem eq_or_eq_or_eq_of_mem_support_of_adj_adj {u v : X} (huv : u ≠ v) {w y : T.V}
    (huw : T.graph.Adj (T.leaf u) w) (hwv : T.graph.Adj w (T.leaf v))
    (hy : y ∈ (T.existsUnique_path (T.leaf u) (T.leaf v)).choose.support) :
    y = T.leaf u ∨ y = w ∨ y = T.leaf v := by
  rw [support_eq_of_adj_adj T huv huw hwv] at hy
  simpa using hy

/-- ★★★ **Lemma 3 等号条件的几何方向（⟸）**（文献 `:328–329`）：若 `w` **同时邻接**两片叶
`u, v`（即 `p = (u,w,v)`，路径只有三点），则 `z(u,v) = ℓ(w)`。 -/
theorem eq_of_adj_adj {u v : X} (huv : u ≠ v) {w : T.V}
    (huw : T.graph.Adj (T.leaf u) w) (hwv : T.graph.Adj w (T.leaf v)) :
    T.dist (T.leaf u) (T.leaf v) + T.pathLeafStatus (T.leaf u) (T.leaf v) = T.leafStatus w := by
  have hw : w ∈ (T.existsUnique_path (T.leaf u) (T.leaf v)).choose.support := by
    rw [support_eq_of_adj_adj T huv huw hwv]
    simp
  refine (eq_dist_add_pathLeafStatus_iff T huv hw).mpr ?_
  intro x hxu hxv
  have huniqU : ∀ y : T.V, T.graph.Adj (T.leaf u) y → y = w := fun y hy => eq_of_adj_leaf T u huw hy
  have huniqV : ∀ y : T.V, T.graph.Adj (T.leaf v) y → y = w :=
    fun y hy => eq_of_adj_leaf T v hwv.symm hy
  show T.dist (T.leaf x) (T.projOnPath (T.leaf u) (T.leaf v) (T.leaf x)) = T.dist (T.leaf x) w
  refine le_antisymm (distToPath_le T hw) ?_
  have hmem := projOnPath_mem T (T.leaf u) (T.leaf v) (T.leaf x)
  rcases eq_or_eq_or_eq_of_mem_support_of_adj_adj T huv huw hwv hmem with h | h | h
  · rw [h]
    have h1 := eq_add_dist_of_ne_of_unique_adj T huniqU hxu
    rw [Phylo.TreeDist.dist_comm T (T.leaf u) (T.leaf x),
      Phylo.TreeDist.dist_comm T w (T.leaf x)] at h1
    have h0 : 0 ≤ T.wExt s(T.leaf u, w) := Phylo.TreeDist.wExt_nonneg T _
    linarith
  · rw [h]
  · rw [h]
    have h1 := eq_add_dist_of_ne_of_unique_adj T huniqV hxv
    rw [Phylo.TreeDist.dist_comm T (T.leaf v) (T.leaf x),
      Phylo.TreeDist.dist_comm T w (T.leaf x)] at h1
    have h0 : 0 ≤ T.wExt s(T.leaf v, w) := Phylo.TreeDist.wExt_nonneg T _
    linarith

end Lemma3Adj

/-! ## 12. Lemma 3 等号条件的几何反向：等号 ⟹ `p = (u,w,v)`

路线（主 agent 的配方 + 本库已有件）：

* ★★ `exists_adj_crossing` —— 从集合 `U` 内走到 `U` 外的 walk 必含**跨界边**（walk 归纳）；
* ★★★ `mem_support_of_inSide_of_inSide` —— `x` 在边 `s(c,p)` 的 `c` 侧、`y` 在 `p` 侧时，
  `x–y` 的唯一路径**必经 `p`**（用 ★★ `exists_adj_crossing` + 库的
  `eq_of_adj_of_not_inSide`：跨界边只能是 `s(c,p)`，故 `p` 落在路径的支持集里）；
* ★★★ `exists_distToPath_lt_of_not_adj` —— **引擎**：`T.leaf u` 是叶、它与 `w ∈ u–v 路径`
  不相邻、`w` 非叶时，存在第三者叶 `x` 使
  `T.distToPath (T.leaf u) (T.leaf v) (T.leaf x) < T.dist (T.leaf x) w`
  （取邻居 `p`、`p` 在路径上的后继 `q`、第三条边 `p—c`（`deg p ≥ 3` 来自 `no_degree_two`）
  与 `c` 分支里的叶 `x`；`x` 的投影是 `p` 而 `w` 在 `p` 的另一侧，正权给出
  `d(x,w) = d(x,p) + d(p,w) > d(x,p)`）；
* ★★ `distToPath_comm` —— `distToPath` 对两端点对称（经 ★★★ `distToPath_eq_half`）；
* ★★★ `eq_imp_adj_adj` —— **目标**：由 ★★★ `eq_dist_add_pathLeafStatus_iff` 把等号化为
  「所有第三者叶的投影都是 `w`」，再用引擎（两个方向各一次）反证。 -/

section Lemma3Conv

variable [Fintype X] [DecidableEq X]
variable (T : Phylogram.{u, v} X)

omit [Fintype X] [DecidableEq X] in
/-- ★★ **跨界 walk 必有跨界边**：若 `a ∈ U`、`b ∉ U`，则 `a–b` 的 walk 必含一条
一端在 `U` 内、一端在 `U` 外的边（两端点都在 walk 的支持集中）。 -/
theorem exists_adj_crossing {U : Set T.V} {a b : T.V} (p : T.graph.Walk a b)
    (ha : a ∈ U) (hb : b ∉ U) :
    ∃ x ∈ p.support, ∃ y ∈ p.support, T.graph.Adj x y ∧ x ∈ U ∧ y ∉ U := by
  refine SimpleGraph.Walk.recOn (motive := fun u v q => u ∈ U → v ∉ U →
      ∃ x ∈ q.support, ∃ y ∈ q.support, T.graph.Adj x y ∧ x ∈ U ∧ y ∉ U)
    p ?_ ?_ ha hb
  · intro u hu hnu
    exact absurd hu hnu
  · intro u v ww hadj q ih hu hnw
    by_cases hc : v ∈ U
    · obtain ⟨x, hx, y, hy, hadj', hxU, hyU⟩ := ih hc hnw
      exact ⟨x, List.mem_cons_of_mem _ hx, y, List.mem_cons_of_mem _ hy, hadj', hxU, hyU⟩
    · refine ⟨u, SimpleGraph.Walk.start_mem_support _, v, ?_, hadj, hu, hc⟩
      rw [SimpleGraph.Walk.support_cons]
      exact List.mem_cons_of_mem _ (SimpleGraph.Walk.start_mem_support q)

/-- ★★★ **跨界路径必经端点**：`x` 在边 `s(c,p)` 的 `c` 侧、`y` 在 `p` 侧时，
`x–y` 的唯一路径**含 `p`**。 -/
theorem mem_support_of_inSide_of_inSide {c p x y : T.V} (hcp : T.graph.Adj c p)
    (hx : T.inSide s(c, p) c x) (hy : T.inSide s(c, p) p y) :
    p ∈ (T.existsUnique_path x y).choose.support := by
  by_contra hnot
  have hyc : ¬ T.inSide s(c, p) c y := fun hcy => T.not_inSide_both hcp ⟨hcy, hy⟩
  obtain ⟨z₁, hz₁, z₂, hz₂, hadj, hz₁U, hz₂U⟩ :=
    exists_adj_crossing T (U := {z : T.V | T.inSide s(c, p) c z})
      ((T.existsUnique_path x y).choose) hx hyc
  have hedge : s(z₁, z₂) = s(c, p) := T.eq_of_adj_of_not_inSide hadj hz₁U hz₂U
  rcases Sym2.eq_iff.mp hedge with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact hnot (h2 ▸ hz₂)
  · exact hnot (h1 ▸ hz₁)

omit [Fintype X] [DecidableEq X] in
/-- ★★ **`distToPath` 对两端点对称**（经 ★★★ `distToPath_eq_half`）。 -/
theorem distToPath_comm (hpos : ∀ e : Edge T.toCladogram, 0 < T.w e) (a b x : T.V) :
    T.distToPath a b x = T.distToPath b a x := by
  rw [distToPath_eq_half T hpos, distToPath_eq_half T hpos, Phylo.TreeDist.dist_comm T b a]
  ring

/-- ★★★ **引擎**：`T.leaf u` 是叶、它与 `w ∈ u–v 路径` 不相邻、`w` 非叶时，
存在**第三者**叶 `x`（`x ≠ u`、`x ≠ v`）使它的投影离它比 `w` 更近：
`T.distToPath (T.leaf u) (T.leaf v) (T.leaf x) < T.dist (T.leaf x) w`。 -/
theorem exists_distToPath_lt_of_not_adj (hpos : ∀ e : Edge T.toCladogram, 0 < T.w e)
    {u v : X} (huv : u ≠ v) {w : T.V}
    (hw : w ∈ (T.existsUnique_path (T.leaf u) (T.leaf v)).choose.support)
    (hwint : ¬ T.IsLeaf w) (hwna : ¬ T.graph.Adj (T.leaf u) w) :
    ∃ x : X, T.leaf x ≠ T.leaf u ∧ T.leaf x ≠ T.leaf v ∧
      T.distToPath (T.leaf u) (T.leaf v) (T.leaf x) < T.dist (T.leaf x) w := by
  -- `p`：路径首边的中间点（= `T.leaf u` 的唯一邻居）
  have hdeg : T.graph.degree (T.leaf u) = 1 := (T.leaf_iff_degree_one (T.leaf u)).mp ⟨u, rfl⟩
  obtain ⟨p, hap, P₂, hPsplit⟩ := SimpleGraph.Walk.exists_eq_cons_of_ne
    (fun h => huv (T.leaf.injective h)) (T.existsUnique_path (T.leaf u) (T.leaf v)).choose
  obtain ⟨p₀, _, huniq₀⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hdeg
  have huniq : ∀ y : T.V, T.graph.Adj (T.leaf u) y → y = p :=
    fun y hy => (huniq₀ y hy).trans (huniq₀ p hap).symm
  have hpw : p ≠ w := fun h => hwna (h ▸ hap)
  have hP : ((T.existsUnique_path (T.leaf u) (T.leaf v)).choose).IsPath :=
    (T.existsUnique_path (T.leaf u) (T.leaf v)).choose_spec.1
  have hP₂ : P₂.IsPath := by
    rw [hPsplit] at hP
    exact SimpleGraph.Walk.IsPath.of_cons hP
  have hPsupp : (T.existsUnique_path (T.leaf u) (T.leaf v)).choose.support
      = T.leaf u :: P₂.support := by rw [hPsplit]; rfl
  have hnu : T.leaf u ∉ P₂.support :=
    (List.nodup_cons.mp (by rw [← hPsupp]; exact hP.support_nodup)).1
  have hpP : p ∈ (T.existsUnique_path (T.leaf u) (T.leaf v)).choose.support := by
    rw [hPsupp]
    exact List.mem_cons_of_mem _ (SimpleGraph.Walk.start_mem_support P₂)
  by_cases hpv : p = T.leaf v
  · exfalso
    -- 此时路径只有一条边，而 `w ∈ support` 且不是叶
    have hnil : P₂.Nil := (SimpleGraph.Walk.IsPath.nil_iff_eq hP₂).mpr hpv
    have hsupp₂ : P₂.support = [p] := SimpleGraph.Walk.nil_iff_support_eq.mp hnil
    have hw' : w ∈ T.leaf u :: P₂.support := by rw [← hPsupp]; exact hw
    rw [hsupp₂] at hw'
    rcases List.mem_cons.mp hw' with h | h
    · exact hwint (h ▸ (show T.IsLeaf (T.leaf u) from ⟨u, rfl⟩))
    · exact hpw (List.mem_singleton.mp h).symm
  · -- `q`：`P₂` 的首个后继
    obtain ⟨q, hpq, Q, hP₂cons⟩ := SimpleGraph.Walk.exists_eq_cons_of_ne hpv P₂
    have hqP₂ : q ∈ P₂.support := by
      rw [hP₂cons]
      exact List.mem_cons_of_mem _ (SimpleGraph.Walk.start_mem_support Q)
    have hqu : q ≠ T.leaf u := fun h => hnu (h ▸ hqP₂)
    -- `deg p ≥ 3`
    have h2deg : 2 ≤ T.graph.degree p := two_le_degree_of_adj_adj T hap hpq hqu.symm
    have hne1 : T.graph.degree p ≠ 1 := fun h =>
      (fun hnl : ¬ T.IsLeaf p => hnl ((T.isLeaf_iff_degree_eq_one p).mpr h))
        (fun hleaf => by rw [(T.isLeaf_iff_degree_eq_one p).mp hleaf] at h2deg; omega)
    have h3deg : 3 ≤ T.graph.degree p := by
      have hne2 := T.no_degree_two p
      omega
    -- 第三条边 `p—c`
    obtain ⟨c, hc, hca, hcq⟩ : ∃ c ∈ T.graph.neighborFinset p, c ≠ T.leaf u ∧ c ≠ q := by
      by_contra hcon
      rw [not_exists] at hcon
      have hsub : T.graph.neighborFinset p ⊆ ({T.leaf u, q} : Finset T.V) := by
        intro z hz
        have hz' := hcon z
        rw [Finset.mem_insert, Finset.mem_singleton]
        by_contra hz''
        rw [not_or] at hz''
        exact hz' ⟨hz, hz''.1, hz''.2⟩
      have hcard := Finset.card_le_card hsub
      rw [Finset.card_pair hqu.symm, SimpleGraph.card_neighborFinset_eq_degree] at hcard
      omega
    have hpc : T.graph.Adj p c := (SimpleGraph.mem_neighborFinset T.graph p c).mp hc
    have hcp : T.graph.Adj c p := hpc.symm
    -- `s(p,c) ∉ P₂.edges`（`P₂` 是路径，`p` 只出现一次）
    have he_not : s(p, c) ∉ P₂.edges := by
      rw [hP₂cons, SimpleGraph.Walk.edges_cons]
      intro hmem
      rcases List.mem_cons.mp hmem with h | h
      · rcases Sym2.eq_iff.mp h with ⟨-, h2⟩ | ⟨h1, -⟩
        · exact hcq h2
        · exact hpq.ne h1
      · have hpQ : p ∈ Q.support := SimpleGraph.Walk.fst_mem_support_of_mem_edges Q h
        have hQnot : p ∉ Q.support := by
          have hnd := hP₂.support_nodup
          rw [hP₂cons] at hnd
          exact (List.nodup_cons.mp hnd).1
        exact hQnot hpQ
    -- `c` 分支里的叶 `x`
    obtain ⟨x, hx⟩ := T.sideLeaves_nonempty_of_adj hpc.symm
    have hxC : T.inSide s(c, p) c (T.leaf x) := (T.mem_sideLeaves_iff_inSide).mp hx
    -- `p` 侧的三片已知叶：`u`、`v`，以及 `w`
    have hsideU : T.inSide s(c, p) p (T.leaf u) :=
      (SimpleGraph.deleteEdges_adj.mpr ⟨hap.symm, by
        intro hmem
        rcases Sym2.eq_iff.mp (Set.mem_singleton_iff.mp hmem) with ⟨-, h2⟩ | ⟨-, h2⟩
        · exact hap.ne h2
        · exact hca h2.symm⟩).reachable
    have hsideV : T.inSide s(c, p) p (T.leaf v) :=
      (SimpleGraph.Walk.toDeleteEdges {s(c, p)} P₂ (by
        intro e' he' hmem
        have h' : s(c, p) ∈ P₂.edges := Set.mem_singleton_iff.mp hmem ▸ he'
        rw [Sym2.eq_swap] at h'
        exact he_not h')).reachable
    have hsideW : T.inSide s(c, p) p w := by
      have hwP₂ : w ∈ P₂.support := by
        have h1 : w ∈ T.leaf u :: P₂.support := by rw [← hPsupp]; exact hw
        rcases List.mem_cons.mp h1 with h | h
        · exact absurd (h ▸ (show T.IsLeaf (T.leaf u) from ⟨u, rfl⟩)) hwint
        · exact h
      obtain ⟨M₁, M₂, hM⟩ := SimpleGraph.Walk.mem_support_iff_exists_append.mp hwP₂
      exact (SimpleGraph.Walk.toDeleteEdges {s(c, p)} M₁ (by
        intro e' he' hmem
        have h' : e' = s(c, p) := Set.mem_singleton_iff.mp hmem
        have h2 : s(p, c) ∈ P₂.edges := by
          rw [hM, SimpleGraph.Walk.edges_append]
          rw [h', Sym2.eq_swap] at he'
          exact List.mem_append_left _ he'
        exact he_not h2)).reachable
    -- `x` 不在 `p` 侧（否则与 `u`/`v` 同侧矛盾）
    have hxnot : x ∉ T.sideLeaves s(c, p) p := by
      rw [T.sideLeaves_compl_adj hcp]
      exact fun hcon => (Finset.mem_compl.mp hcon) hx
    have hxu : T.leaf x ≠ T.leaf u := fun h => hxnot (by
      rw [T.leaf.injective h]
      exact (T.mem_sideLeaves_iff_inSide).mpr hsideU)
    have hxv : T.leaf x ≠ T.leaf v := fun h => hxnot (by
      rw [T.leaf.injective h]
      exact (T.mem_sideLeaves_iff_inSide).mpr hsideV)
    -- `p` 在 `x–w` 路径上 ⟹ `d(x,w) = d(x,p) + d(p,w) > d(x,p)`
    have hp_mem : p ∈ (T.existsUnique_path (T.leaf x) w).choose.support :=
      mem_support_of_inSide_of_inSide T hcp hxC hsideW
    have hxw : T.dist (T.leaf x) w = T.dist (T.leaf x) p + T.dist p w :=
      Phylo.TreeDist.dist_eq_add_of_mem_support T _
        (T.existsUnique_path (T.leaf x) w).choose_spec.1 hp_mem
    have hwpos : 0 < T.dist p w := pos_dist_of_ne T hpos hpw
    exact ⟨x, hxu, hxv, by
      have hle : T.distToPath (T.leaf u) (T.leaf v) (T.leaf x) ≤ T.dist (T.leaf x) p :=
        distToPath_le T hpP
      linarith⟩

/-- ★★★ **Lemma 3 等号条件的几何反向**（文献 `:328–329`）：`u ≠ v` 是两片叶、`w` 是
`u–v` 路径上的**内部**结点（`¬ T.IsLeaf w`），且 `z(u,v) = ℓ(w)` 取得等号 —— 则
`w` **同时邻接**两片叶（即 `p = (u,w,v)`，路径只有三点）。

证明：由 ★★★ `eq_dist_add_pathLeafStatus_iff`，等号给出「所有第三者叶的投影都是 `w`」；
若 `T.leaf u` 与 `w` 不相邻，则由 ★★★ `exists_distToPath_lt_of_not_adj` 得到一片
投影不是 `w` 的第三者叶，矛盾；对 `T.leaf v` 用 ★★ `distToPath_comm` 与路径反向同理。 -/
theorem eq_imp_adj_adj (hpos : ∀ e : Edge T.toCladogram, 0 < T.w e) {u v : X} (huv : u ≠ v)
    {w : T.V} (hw : w ∈ (T.existsUnique_path (T.leaf u) (T.leaf v)).choose.support)
    (hwint : ¬ T.IsLeaf w)
    (heq : T.dist (T.leaf u) (T.leaf v) + T.pathLeafStatus (T.leaf u) (T.leaf v)
      = T.leafStatus w) :
    T.graph.Adj (T.leaf u) w ∧ T.graph.Adj w (T.leaf v) := by
  have hforall := (eq_dist_add_pathLeafStatus_iff T huv hw).mp heq
  by_contra hcon
  rw [not_and_or] at hcon
  rcases hcon with hna | hnb
  · obtain ⟨x, hxu, hxv, hlt⟩ := exists_distToPath_lt_of_not_adj T hpos huv hw hwint hna
    exact absurd (hforall x hxu hxv) (ne_of_lt hlt)
  · have hrev : (T.existsUnique_path (T.leaf v) (T.leaf u)).choose
        = ((T.existsUnique_path (T.leaf u) (T.leaf v)).choose).reverse :=
      ((T.existsUnique_path (T.leaf v) (T.leaf u)).choose_spec.2 _
        (SimpleGraph.Walk.IsPath.reverse
          (T.existsUnique_path (T.leaf u) (T.leaf v)).choose_spec.1)).symm
    have hw' : w ∈ (T.existsUnique_path (T.leaf v) (T.leaf u)).choose.support := by
      rw [hrev, SimpleGraph.Walk.support_reverse]
      exact List.mem_reverse.mpr hw
    obtain ⟨x, hxv, hxu, hlt⟩ :=
      exists_distToPath_lt_of_not_adj T hpos huv.symm hw' hwint (fun h => hnb h.symm)
    rw [distToPath_comm T hpos] at hlt
    exact absurd (hforall x hxu hxv) (ne_of_lt hlt)

end Lemma3Conv

end

end Phylogram
