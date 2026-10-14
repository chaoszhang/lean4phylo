/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.BMELeastSquares

/-!
# `Phylo.SideDoubling` —— 子树倍增恒等式的**反例侧**（W19 任务 C1.5 的 ★B 件）

## 背景（文献与库内现状）
* Pauplin 公式的本体在库内已被归约为「**每条边两侧的子树倍增和 `D_e(u) = 1`**」
  （`Phylo/BMELeastSquares.lean:587-598` ✓），其中
  `sideDoublingSum T e u := Σ_{x ∈ sideLeaves e u} (1/2)^{d_u(x)}`（同文件 `:618` ✓，
  真名 `NJ.Dissimilarity.sideDoublingSum` ✓）。
* 库内已证：`sideDoublingSum_nonneg`（`:623` ✓）· **挂边的叶侧** `sideDoublingSum_leaf_edge`（`:656` ✓）。
* ★ 派单 W19 明写：`D = 1`「**二叉成立、非二叉不成立**」✓。

## 本文件做什么（★B：结构型先造反例）
给出非二叉导致 `D ≠ 1` 的**显式算术实例**：

> 若某边 `e` 在 `u` 侧的叶集**恰为三片** `{a, b, c}`，且三者到 `u` 的路径**各只有一条边**（`d_u = 1` ✓），
> 则 `D_e(u) = 3 · (1/2) = 3/2 ≠ 1` ✓。

**显式几何实例（星形 4 叶树 ✓）**：顶点 `{c, x₁, x₂, x₃, x₄}`、边仅 `c—xᵢ`（即 `K_{1,4}` ✓，
中心度 **4** ⇒ `IsBinary` 假 ✗）。取 `e = s(c, x₁)`、`u = c`：删除 `e` 后与 `c` 同侧者恰为 `{x₂, x₃, x₄}` ✓，
三者到 `c` 距离都是 **1** ✓ ⇒ **命中本定理** ⇒ `D_e(c) = 3/2 ≠ 1` ✓。
（★ **3 叶**星形两侧都仍为 `1` ✓ —— 故**临界在 4 叶** ✓；这正说明 `IsBinary` 在恒等式中**不可省** ✓。）

## 诚实边界
* 本文件只做**反例侧**（★B ✓）；上面那个**具体**星形 `Cladogram`（`Fin 5` 上的 `K_{1,4}` ✓，
  需证 `IsTree`/`leaf_iff_degree_one`/`no_degree_two` 三字段 ✓）**本轮未落地** ⬜ ——
  故反例以**左右两侧都写明的算术实例**给出（前提在星形树上显然可满足 ✓）；
* 恒等式正面（`T.IsBinary → D_e(u) = 1` ✓）仍需**递归恒等式 ＋ 良基归纳** ⬜；
* 本文件**不改**任何既有声明 ✗。
-/

noncomputable section

namespace Phylo.SideDoubling

open NJ.Dissimilarity

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- ★★ **反例算术（★B 的核心）**：若某侧恰为三片 `{a,b,c}` 且三者深度都是 `1`，
则倍增和 `= 3/2` ⇒ **`≠ 1`** ⇒ 该边不满足 `D = 1` ✓。

（星形 4 叶树取中心那一侧即命中：`e = s(c,x₁)`、`u = c`、该侧 `= {x₂,x₃,x₄}` ✓。） -/
theorem sideDoublingSum_eq_three_halves_of_side_eq_three_leaves (T : Cladogram X) (e : Sym2 T.V)
    (u : T.V) {a b c : X}
    (hside : T.sideLeaves e u = ({a, b, c} : Finset X))
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hda : (T.pathOf u (T.leaf a)).edges.length = 1)
    (hdb : (T.pathOf u (T.leaf b)).edges.length = 1)
    (hdc : (T.pathOf u (T.leaf c)).edges.length = 1) :
    sideDoublingSum T e u = 3 / 2 := by
  rw [sideDoublingSum, hside, Finset.sum_insert (by simp [hab, hac]),
    Finset.sum_insert (by simp [hbc]), Finset.sum_singleton, hda, hdb, hdc]
  norm_num

/-- ★★ **推论（反例陈述）**：同上条件下 `D_e(u) ≠ 1` ✓ ——
即「非二叉」（星形树 ✓）会**破坏**逐边归一化 `D = 1` ✓。 -/
theorem sideDoublingSum_ne_one_of_side_eq_three_leaves (T : Cladogram X) (e : Sym2 T.V)
    (u : T.V) {a b c : X}
    (hside : T.sideLeaves e u = ({a, b, c} : Finset X))
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hda : (T.pathOf u (T.leaf a)).edges.length = 1)
    (hdb : (T.pathOf u (T.leaf b)).edges.length = 1)
    (hdc : (T.pathOf u (T.leaf c)).edges.length = 1) :
    sideDoublingSum T e u ≠ 1 := by
  rw [sideDoublingSum_eq_three_halves_of_side_eq_three_leaves T e u hside hab hac hbc hda hdb hdc]
  norm_num

/-! ## ② 递归恒等式（**代数内核**，条件化形态）

恒等式 `D = 1` 的证明走「对 `sideLeaves.card` 的良基归纳」：**底**＝挂边叶侧（库内 `:656` ✓ **已证** ✓）；
**步**＝内部点 `u`（二叉时度 3 ⇒ 除朝 `e` 的那一支外**恰有两支** `v, w`）：

* **分支分划**（几何，待补 ⬜）：`sideLeaves e u = sideLeaves s(u,v) v ∪ sideLeaves s(u,w) w`（**不交** ✓）；
* **深度关系**（几何，待补 ⬜）：该两支上的叶满足 `d_u(x) = d_v(x) + 1`；
* ★ **代数内核**（本文件 **已证** ✓）：上述两条 ⇒ `D_e(u) = (1/2)·(D_{s(u,v)}(v) + D_{s(u,w)}(w))` ✓。

⇒ 归纳步：两支各自的 `D` 由归纳假设为 `1` ⇒ `D_e(u) = (1/2)·(1 + 1) = 1` ✓。

**诚实边界** ⬜：上面两条「几何前提」（分划与深度关系）本轮**未落地** ✗ ——
它们需要 `sideLeaves`/`pathOf` 在 `u` 的邻接分支上的 `Finset` 记账（库内有 `sideVertices`/`SideSubtree`
分层 ✓，但记账未完成 ✗）；本文件先把**代数内核**钉死 ✓，几何两条按教训 359 如实登记为缺口 ✓。 -/

/-- ★★★ **递归恒等式（②的代数内核，条件形态）**：若某侧恰是「朝 `u` 的两支」的**不交并**，
且两支上的叶深度各比 `u` 深 `1`，则倍增和满足**两支递归**

　`D_e(u) = (1/2)·(D_{s(u,v)}(v) + D_{s(u,w)}(w))` ✓。

（二叉内部点 `u` 度 3 ⇒ 除朝 `e` 一支外**恰有两支** ✓，正是归纳步所需的形状 ✓。） -/
theorem sideDoublingSum_eq_half_mul_add_of_union (T : Cladogram X) (e : Sym2 T.V)
    (u v w : T.V)
    (hpart : T.sideLeaves e u = T.sideLeaves s(u, v) v ∪ T.sideLeaves s(u, w) w)
    (hdisj : Disjoint (T.sideLeaves s(u, v) v) (T.sideLeaves s(u, w) w))
    (hdv : ∀ x ∈ T.sideLeaves s(u, v) v,
      (T.pathOf u (T.leaf x)).edges.length = (T.pathOf v (T.leaf x)).edges.length + 1)
    (hdw : ∀ x ∈ T.sideLeaves s(u, w) w,
      (T.pathOf u (T.leaf x)).edges.length = (T.pathOf w (T.leaf x)).edges.length + 1) :
    sideDoublingSum T e u
      = (1 / 2) * (sideDoublingSum T s(u, v) v + sideDoublingSum T s(u, w) w) := by
  have hA : (∑ x ∈ T.sideLeaves s(u, v) v,
        (1 / 2) ^ ((T.pathOf u (T.leaf x)).edges.length))
      = (1 / 2) * sideDoublingSum T s(u, v) v := by
    rw [sideDoublingSum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [hdv x hx, pow_succ]
    ring
  have hB : (∑ x ∈ T.sideLeaves s(u, w) w,
        (1 / 2) ^ ((T.pathOf u (T.leaf x)).edges.length))
      = (1 / 2) * sideDoublingSum T s(u, w) w := by
    rw [sideDoublingSum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [hdw x hx, pow_succ]
    ring
  rw [sideDoublingSum, hpart, Finset.sum_union hdisj, hA, hB]
  ring

/-! ## ③ 几何前提 (b)：深度关系（沿邻接分支 +1）

归纳步还需要：**若 `x` 落在 `u` 朝 `v` 的那一支上（`x ∈ sideLeaves s(u,v) v` ✓），
则 `d_u(x) = d_v(x) + 1`** ✓（路径 `u — v — ⋯ — x` ✓）。

库内可用器材（探路实测 ✓）：`Cladogram.pathOf`（`AttesonRadius.lean:1336` ✓）· `pathOf_isPath`（`:1341` ✓）·
`existsUnique_path`（`Phylo/Core.lean:83` ✓）· `inSide_*` 族（`LeafStatus.lean` ✓）。
做法：把「`u — v` 接着 `pathOf v (leaf x)`」这条 walk 证成 **`IsPath`**（用 `x` 在 `v` 侧 ⇒ 该 walk 不回访 `u` ✓），
再用路径**唯一性**与 `pathOf` 的定义相等，最后取边数（`Walk.edges_cons` ✓）。

**诚实边界** ⬜：本节的引理若本轮未过门，即如实登记为"未落地"，并在下一轮以 359/361 的策略继续
（**不**改任何既有声明 ✗）。 -/

/-- ★★★ **几何前提 (b) 的第一半**：`x` 落在 `u` 朝 `v` 那一支上（`x ∈ sideLeaves s(u,v) v` ✓）时，
从 **`u`** 到 `leaf x` 的路径**必经**边 `s(u,v)` ✓
（因 `u` 与 `leaf x` 分居该边两侧 ✓ —— 用「跨越侧界的 walk 必用该边」的引擎 ✓）。

库内器材（探路实测 ✓）：`mem_pathOf_edges_iff_not_inSide`（`AttesonRadius.lean:1394` ✓）·
`mem_sideLeaves_iff_inSide`（`Split.lean:648` ✓）· `not_reachable_deleteEdges_of_adj`（`Split.lean:540` ✓，边是桥 ✓）·
`reachable_comm` ✓。 -/
theorem mem_edge_pathOf_u_of_mem_sideLeaves (T : Cladogram X) {u v : T.V}
    (huv : T.graph.Adj u v) {x : X} (hx : x ∈ T.sideLeaves s(u, v) v) :
    s(u, v) ∈ (T.pathOf u (T.leaf x)).edges := by
  rw [T.mem_pathOf_edges_iff_not_inSide]
  intro hc
  have hside : T.inSide s(u, v) v (T.leaf x) := (T.mem_sideLeaves_iff_inSide).mp hx
  exact (T.not_reachable_deleteEdges_of_adj huv) (hc.trans hside.symm)

end Phylo.SideDoubling
