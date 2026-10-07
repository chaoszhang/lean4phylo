/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.TreeDistance
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

**额外假设一览（文献 `:124` 的正边权被显式参数化；本库 `w_nonneg` 只给 `≥ 0`）**：

* `leafStatus_leaf_sub` / `leafStatus_sub`：只需**该边**正权 `0 < T.wExt s(u,v)`
  （⚠️ `ω < 0` 时 Lemma 1 的恒等式**为假**）；
* `leafStatus_minimizer_not_isLeaf` / `pos_walkDist_of_ne` / `pos_dist_of_ne` /
  `eq_add_dist_of_min_support` / `exists_median_eq_half`：全局正边权
  `∀ e : Edge T.toCladogram, 0 < T.w e`（文献 `:124` 的 `ω : E(T) → ℕ⁺`；
  `:397–402` 说其实内部边正权已够）。

## ⬜ 未完成（本轮范围之外，未虚报）

* **Lemma 2**（文献 `:213–214`，沿路径 `ℓ` 单调）—— 未做。
* **Lemma 3**（文献 `:328–329`，`z(u,v) ≤ ℓ(w)`、等号 iff `p = (u,w,v)`）—— 未做。
* **Observation 2**（文献 `:143`，`ℓ(p) = ½(ℓ(u)+ℓ(v)−|L(T)|·d(u,v))`）—— 未做
  （可由本文件的 ★★★ `exists_median_eq_half` 加求和线性性组合，但不属本轮四项）。
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

end

end Phylogram
