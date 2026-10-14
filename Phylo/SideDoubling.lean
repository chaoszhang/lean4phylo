/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.BMELeastSquares
import Phylo.SplitsMaximal

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

/-- ★★★ **几何前提 (b)：深度关系** ✓ —— `x` 在 `u` 朝 `v` 那一支上时，
从 `u` 到 `leaf x` 的路径**恰比**从 `v` 到 `leaf x` 的路径**多一条边** ✓：

　`(T.pathOf u (T.leaf x)).edges.length = (T.pathOf v (T.leaf x)).edges.length + 1` ✓。

证明（"边集只差一条"路线 ✓）：
* `s(u,v) ∈ (pathOf u (leaf x)).edges` ✓（本文件 `mem_edge_pathOf_u_of_mem_sideLeaves` ✓）；
* `s(u,v) ∉ (pathOf v (leaf x)).edges` ✓（由 `mem_pathOf_edges_iff_not_inSide` ＋ `inSide` ✓）；
* 其余边 `e ≠ s(u,v)`：两条路径的成员关系**一致** ✓ —— 由 `inSide_congr_of_adj`
  （`a — b` 为边且 `e ≠ s(a,b)` 时两**端点同侧** ✓，见 `LeafStatus.lean:787` 的用法 ✓）得
  `inSide e (leaf x) u ↔ inSide e (leaf x) v` ✓；
* 故 `edges.toFinset` 只差一条 ⇒ 取**基数**（`pathOf_edges_nodup` ✓ `AttesonRadius.lean:1539` ✓）即得 `+1` ✓。 -/
theorem length_pathOf_eq_succ_of_adj_of_mem_sideLeaves (T : Cladogram X) {u v : T.V}
    (huv : T.graph.Adj u v) {x : X} (hx : x ∈ T.sideLeaves s(u, v) v) :
    (T.pathOf u (T.leaf x)).edges.length = (T.pathOf v (T.leaf x)).edges.length + 1 := by
  have hside : T.inSide s(u, v) v (T.leaf x) := (T.mem_sideLeaves_iff_inSide).mp hx
  have hin : s(u, v) ∈ (T.pathOf u (T.leaf x)).edges :=
    mem_edge_pathOf_u_of_mem_sideLeaves T huv hx
  have hnotin : s(u, v) ∉ (T.pathOf v (T.leaf x)).edges := fun hmem =>
    (T.mem_pathOf_edges_iff_not_inSide (e := s(u, v)) (u := v) (v := T.leaf x)).mp hmem hside
  have hset : (T.pathOf u (T.leaf x)).edges.toFinset
      = insert s(u, v) (T.pathOf v (T.leaf x)).edges.toFinset := by
    ext e
    rw [Finset.mem_insert]
    by_cases he : e = s(u, v)
    · subst he
      simp [hin, hnotin]
    · have he' : s(u, v) ≠ e := fun h => he h.symm
      have hcongr : T.inSide e (T.leaf x) u ↔ T.inSide e (T.leaf x) v :=
        T.inSide_congr_of_adj (e₁ := e) (u₁ := T.leaf x) huv he'
      have hiff : e ∈ (T.pathOf u (T.leaf x)).edges ↔ e ∈ (T.pathOf v (T.leaf x)).edges := by
        rw [T.mem_pathOf_edges_iff_not_inSide, T.mem_pathOf_edges_iff_not_inSide]
        exact not_congr ((T.inSide_comm e u (T.leaf x)).trans
          (hcongr.trans (T.inSide_comm e v (T.leaf x)).symm))
      simp only [List.mem_toFinset]
      rw [hiff]
      exact ⟨fun h => Or.inr h, fun h => h.elim (fun h1 => absurd h1.symm he') id⟩
  have hnu : (T.pathOf u (T.leaf x)).edges.Nodup := T.pathOf_edges_nodup u (T.leaf x)
  have hnv : (T.pathOf v (T.leaf x)).edges.Nodup := T.pathOf_edges_nodup v (T.leaf x)
  have h1 : (T.pathOf u (T.leaf x)).edges.toFinset.card
      = (T.pathOf u (T.leaf x)).edges.length := List.toFinset_card_of_nodup hnu
  have h2 : (T.pathOf v (T.leaf x)).edges.toFinset.card
      = (T.pathOf v (T.leaf x)).edges.length := List.toFinset_card_of_nodup hnv
  rw [← h1, ← h2, hset, Finset.card_insert_of_notMem (fun h => hnotin (List.mem_toFinset.mp h))]

/-! ## ④ 几何前提 (a) 的关键一步：`v` 侧路径**不经过 `u`**

`x` 在 `u` 朝 `v` 那一支上时，从 `v` 到 `leaf x` 的唯一路径**不经过 `u`** ✓ ——
否则该路径的前缀 `takeUntil u` 是一条**避开 `s(u,v)`** 的 `v → u` 走法（边表是子集 ✓
`SimpleGraph.Walk.edges_takeUntil_subset_edges`，`Mathlib/…/Walk/Decomp.lean:235` ✓），
与「边是桥」矛盾 ✓。这一步是 (a) 分支分划的直接前提 ✓。 -/

/-- ★★★ **`v` 侧路径不经过 `u`**：`x ∈ sideLeaves s(u,v) v` ⇒ `u ∉ (T.pathOf v (T.leaf x)).support` ✓。 -/
theorem not_mem_support_pathOf_of_mem_sideLeaves (T : Cladogram X) {u v : T.V}
    (huv : T.graph.Adj u v) {x : X} (hx : x ∈ T.sideLeaves s(u, v) v) :
    u ∉ (T.pathOf v (T.leaf x)).support := by
  intro hmem
  have hside : T.inSide s(u, v) v (T.leaf x) := (T.mem_sideLeaves_iff_inSide).mp hx
  have hedge : s(u, v) ∉ (T.pathOf v (T.leaf x)).edges := fun h =>
    ((T.mem_pathOf_edges_iff_not_inSide (e := s(u, v)) (u := v) (v := T.leaf x)).mp h) hside
  have hsub := SimpleGraph.Walk.edges_takeUntil_subset_edges (T.pathOf v (T.leaf x)) hmem
  have hreach : (T.graph.deleteEdges {s(u, v)}).Reachable v u :=
    SimpleGraph.reachable_deleteEdges_of_notMem_edges _ fun h => hedge (hsub h)
  exact (T.not_reachable_deleteEdges_of_adj huv) hreach.symm

/-! ## ⑤ 几何前提 (a) 的一半：`v` 支 ⊆ `u` 侧

`e = s(u,y)` 是 `u` 的**另一条**邻边（`s(u,v) ≠ e` ✓）时，`v` 支上的叶都在 `u` 侧 ✓：

　`sideLeaves s(u,v) v ⊆ sideLeaves e u` ✓。

证明（现在有砖了 ✓）：取 `p := T.pathOf v (T.leaf x)` ✓。由 ④ 知 `u ∉ p.support` ✓，
故 `SimpleGraph.reachable_deleteEdges_of_notMem_support`（`SplitsMaximal.lean:232` ✓，
"支撑集不含 `w` 的 walk 不使用任何以 `w` 为端点的边" ✓）给出 `(T - e).Reachable v (T.leaf x)` ✓；
又 `u — v` 这条边在 `T - e` 中仍在（`s(u,v) ≠ e` ✓，`deleteEdges_adj` ✓），
故 `(T - e).Reachable u (T.leaf x)` ✓，即 `x ∈ sideLeaves e u` ✓。 -/

/-- ★★★ **(a) 的一半**：`e = s(u,y)`（`u` 的另一条邻边，`s(u,v) ≠ e` ✓）时
`x ∈ sideLeaves s(u,v) v ⇒ x ∈ sideLeaves e u` ✓。 -/
theorem mem_sideLeaves_of_mem_sideLeaves_adj (T : Cladogram X) {u v y : T.V} {e : Sym2 T.V}
    (huv : T.graph.Adj u v) (he : e = s(u, y)) (hne : s(u, v) ≠ e) {x : X}
    (hx : x ∈ T.sideLeaves s(u, v) v) : x ∈ T.sideLeaves e u := by
  rw [T.mem_sideLeaves]
  have hnotmem : u ∉ (T.pathOf v (T.leaf x)).support :=
    not_mem_support_pathOf_of_mem_sideLeaves T huv hx
  have hreach_v : (T.graph.deleteEdges {e}).Reachable v (T.leaf x) := by
    rw [he]
    exact SimpleGraph.reachable_deleteEdges_of_notMem_support
      (z := y) (T.pathOf v (T.leaf x)) hnotmem
  have hreach_uv : (T.graph.deleteEdges {e}).Reachable u v :=
    (SimpleGraph.deleteEdges_adj.mpr ⟨huv, hne⟩).reachable
  exact (hreach_uv.trans hreach_v).symm

/-! ## ⑥ 砖块：从 `u` 出发的路径至多用到 `u` 的一条邻边

这一块同时给出 **(a) 的反向包含** 与 **两支不交** 所需的全部信息 ✓：

　`u ≠ z` 时，若 `s(u,y₁)` 与 `s(u,y₂)` 都出现在 `(T.pathOf u z).edges` 里，则 `s(u,y₁) = s(u,y₂)` ✓。

证明：把 `pathOf u z` 按 `Walk.cons` 分解 ✓ —— 两条边**都必须是首边** ✗ 否则其另一端点在尾走法的支撑集里 ✓
（`SimpleGraph.Walk.mem_support_of_mem_edges` ✓），而 `pathOf` 是**路径** ⇒ 支撑集无重复 ⇒ `u` 不可能再出现 ✓。 -/

omit [Fintype X] [DecidableEq X] in
/-- ★★★ **`u` 处至多一条邻边在路径边表里** ✓（见 §⑥ 说明 ✓）。 -/
theorem eq_of_mem_edges_pathOf_of_adj (T : Cladogram X) {u z : T.V} (huz : u ≠ z)
    {y₁ y₂ : T.V}
    (h₁ : s(u, y₁) ∈ (T.pathOf u z).edges) (h₂ : s(u, y₂) ∈ (T.pathOf u z).edges) :
    s(u, y₁) = s(u, y₂) := by
  cases hp : T.pathOf u z with
  | nil => rw [hp] at h₁; simp at h₁
  | cons hadj p =>
    rw [hp] at h₁ h₂
    simp only [SimpleGraph.Walk.edges_cons, List.mem_cons] at h₁ h₂
    have hno : u ∉ p.support := by
      have hpath : (SimpleGraph.Walk.cons hadj p).IsPath := by
        rw [← hp]; exact T.pathOf_isPath u z
      rw [SimpleGraph.Walk.isPath_def, SimpleGraph.Walk.support_cons,
        List.nodup_cons] at hpath
      exact hpath.1
    rcases h₁ with h₁ | h₁
    · rcases h₂ with h₂ | h₂
      · rw [h₁, h₂]
      · exact absurd (SimpleGraph.Walk.mem_support_of_mem_edges h₂ (by simp)) hno
    · exact absurd (SimpleGraph.Walk.mem_support_of_mem_edges h₁ (by simp)) hno

/-! ## ⑦ 用 ⑥ 的砖收 **两支不交**（(a) 的 `hdisj` ✓）

`u` 的两条**不同**邻边 `s(u,v)`、`s(u,w)` 给出的两支**不交** ✓：
若某叶 `x` 同时在两支上，则由 ⑤ 的前向引理，两条边都在 `(pathOf u (leaf x)).edges` 里 ✓，
由 ⑥ 得二者**相等** ⇒ `v = w` ✗（或 `v = u` ✗，与 `Adj` 的无自环矛盾 ✓）—— 皆与假设冲突 ✓。 -/

/-- ★★★ **两支不交** ✓（(a) 的 `hdisj` 前提 ✓；下一条拼装直接用它 ✓）。 -/
theorem disjoint_sideLeaves_of_adj_adj (T : Cladogram X) {u v w : T.V}
    (huv : T.graph.Adj u v) (huw : T.graph.Adj u w) (hvw : v ≠ w) :
    Disjoint (T.sideLeaves s(u, v) v) (T.sideLeaves s(u, w) w) := by
  rw [Finset.disjoint_left]
  intro x hx1 hx2
  -- `u ≠ T.leaf x`：若相等，则在 `T - s(u,v)` 中 `u` 与 `v` 可达 —— 与「边是桥」矛盾
  have hux : u ≠ T.leaf x := by
    intro h
    have hside : T.inSide s(u, v) v (T.leaf x) := (T.mem_sideLeaves_iff_inSide).mp hx1
    exact (T.not_reachable_deleteEdges_of_adj huv) (h ▸ hside.symm)
  have e1 : s(u, v) ∈ (T.pathOf u (T.leaf x)).edges :=
    mem_edge_pathOf_u_of_mem_sideLeaves T huv hx1
  have e2 : s(u, w) ∈ (T.pathOf u (T.leaf x)).edges :=
    mem_edge_pathOf_u_of_mem_sideLeaves T huw hx2
  have heq := eq_of_mem_edges_pathOf_of_adj T hux e1 e2
  rcases Sym2.eq_iff.mp heq with ⟨-, h⟩ | ⟨_, h2⟩
  · exact hvw h
  · exact huv.ne h2.symm

/-! ## ⑧ (a) 的第三块：反向包含 —— **本轮只落「取首边」，路线已写清** ⬜

**已证** ✓：`exists_adj_of_edges_pathOf` —— `u ≠ z` 时 `pathOf u z` 的**首边**是 `u` 的某条邻边 `s(u,y)` ✓。

**★★ 反向包含的清晰路线（下一轮按此写，避免缠团 ✗）**：
设 `x ∈ sideLeaves e u` ✓，`e = s(u,y₀)` ✓，覆盖假设 `∀ z, Adj u z → z = y₀ ∨ z = v ∨ z = w` ✓：
1. 由 `mem_sideLeaves_iff_inSide` ＋ `mem_pathOf_edges_iff_not_inSide`
   ⇒ **路径 `pathOf u (leaf x)` 避开 `e`** ✓；
2. 取首边（本文件 ✓）得 `s(u,y) ∈ (pathOf u (leaf x)).edges` ✓ ⇒ 由 1. 有 `s(u,y) ≠ e` ⇒ `y ≠ y₀` ✓
   ⇒ 由覆盖假设 `y = v ∨ y = w` ✓；
3. ★★ **关键简化** ✓：**不必**做"support 不回头"的分析 ✗ ——
   直接用 `pathOf_edges_nodup`（`AttesonRadius.lean:1539` ✓）：**每条边在路径边表里至多一次** ✓
   ⇒ 若 `y = v`，则**尾走法**里**不再有** `s(u,v)` ✓ ⇒ 尾走法是一条**避开 `s(u,v)`** 的 `v → leaf x` 走法 ✓
   ⇒ 由 `reachable_deleteEdges_of_notMem_edges` 得 `(T - s(u,v)).Reachable v (leaf x)` ✓
   ⇒ `x ∈ sideLeaves s(u,v) v` ✓；`y = w` 同理 ✓。
⇒ ★ 教训 **376**：**"边表 `Nodup`" 可以替代整段"支撑集不回头"的推理** ✓
  （本轮我先把证明写缠了 ✗，正是因为忘了 `pathOf_edges_nodup` ✓）。

**诚实边界** ⬜：反向包含**本轮未完成**（缠团的草稿已按铁律 5 撤下 ✓）；
本定理族仍把 `u ≠ T.leaf x` 作为**显式前提**（二叉场合可另证 ✓，不引入 `Phylogram` 度数器材 ✓ 教训 375 ✓）。 -/

omit [Fintype X] [DecidableEq X] in
/-- ★★ **取首边**：`u ≠ z` ⇒ 路径 `pathOf u z` 的首边是 `u` 的某条邻边 ✓。 -/
theorem exists_adj_of_edges_pathOf (T : Cladogram X) {u z : T.V} (huz : u ≠ z) :
    ∃ y : T.V, T.graph.Adj u y ∧ s(u, y) ∈ (T.pathOf u z).edges := by
  cases hp : T.pathOf u z with
  | nil => exact (huz rfl).elim
  | cons hadj p =>
    exact ⟨_, hadj, by rw [SimpleGraph.Walk.edges_cons]; exact List.mem_cons_self⟩

omit [Fintype X] [DecidableEq X] in
/-- ★★ **取首边（打包邻接版）**：`u ≠ z` ⇒ 存在**邻接** `h : Adj u t` 与尾走法 `p : Walk t z`，
使 `pathOf u z = cons h p` ✓（这样无需给 `cons` 的隐含顶点命名 ✓）。 -/
theorem exists_cons_pathOf (T : Cladogram X) {u z : T.V} (huz : u ≠ z) :
    ∃ (t : T.V) (h : T.graph.Adj u t) (p : T.graph.Walk t z),
      T.pathOf u z = SimpleGraph.Walk.cons h p := by
  cases hp : T.pathOf u z with
  | nil => exact (huz rfl).elim
  | cons hadj p => exact ⟨_, hadj, p, rfl⟩

/-- ★★★ **(a) 的反向包含（第三块）** ✓：覆盖假设（`u` 的邻点只有 `y₀, v, w` ✓）下，
`x ∈ sideLeaves e u`（`e = s(u,y₀)` ✓）⇒ `x` 落在 `v` 支或 `w` 支上 ✓。 -/
theorem mem_union_sideLeaves_of_mem_sideLeaves (T : Cladogram X) {u v w y₀ : T.V} {e : Sym2 T.V}
    (he : e = s(u, y₀))
    (hcover : ∀ z : T.V, T.graph.Adj u z → z = y₀ ∨ z = v ∨ z = w)
    {x : X} (hux : u ≠ T.leaf x) (hx : x ∈ T.sideLeaves e u) :
    x ∈ T.sideLeaves s(u, v) v ∪ T.sideLeaves s(u, w) w := by
  have hside : T.inSide e u (T.leaf x) := (T.mem_sideLeaves_iff_inSide).mp hx
  have hnotmem : e ∉ (T.pathOf u (T.leaf x)).edges := fun h =>
    ((T.mem_pathOf_edges_iff_not_inSide (e := e) (u := u) (v := T.leaf x)).mp h) hside
  obtain ⟨t, hut, p, hp⟩ := exists_cons_pathOf T hux
  have hhead : s(u, t) ≠ e := by
    intro hc
    exact hnotmem (by rw [hp, SimpleGraph.Walk.edges_cons]; exact hc ▸ List.mem_cons_self)
  have hty : t ≠ y₀ := fun h => hhead (by rw [h, ← he])
  have htail : s(u, t) ∉ p.edges := by
    have h2 : (SimpleGraph.Walk.cons hut p).edges.Nodup := by
      rw [← hp]; exact T.pathOf_edges_nodup u (T.leaf x)
    rw [SimpleGraph.Walk.edges_cons] at h2
    exact (List.nodup_cons.mp h2).1
  have htail_reach : (T.graph.deleteEdges {s(u, t)}).Reachable t (T.leaf x) :=
    SimpleGraph.reachable_deleteEdges_of_notMem_edges p htail
  rcases hcover t hut with h | h | h
  · exact absurd h hty
  · exact Finset.mem_union_left _ (by
      rw [h] at htail_reach
      exact (T.mem_sideLeaves).mpr htail_reach.symm)
  · exact Finset.mem_union_right _ (by
      rw [h] at htail_reach
      exact (T.mem_sideLeaves).mpr htail_reach.symm)

/-! ## ⑨ ③ 良基归纳：**底情形（`u` 是叶）** ✓

`u` 是叶且 `e ∋ u`（`e` 为**真边** ✓）时，`e` 必是 `u` 的**挂边** ✓（度为 1 ⇒ 唯一邻居，
用 `degree_eq_one_iff_existsUnique_adj` ✓，库内 `Split.lean:564` 已在用 ✓），
故由库内 `sideDoublingSum_leaf_edge`（`BMELeastSquares.lean:656` ✓）得 **`D_e(u) = 1`** ✓。

**注** ✓：`e ∈ T.graph.edgeSet` 这一假设**不可省** ✗ —— 若 `e` 不是真边，则删去它不改变连通性，
`u` 侧的叶是**全部**叶，`D_e(u) ≠ 1` ✗。 -/

/-- ★★★ **归纳底情形** ✓：`u` 是叶、`e ∋ u` 且 `e` 是真边 ⇒ `D_e(u) = 1` ✓。 -/
theorem sideDoublingSum_eq_one_of_isLeaf (T : Cladogram X) {u : T.V} (hu : T.IsLeaf u)
    {e : Sym2 T.V} (he : u ∈ e) (hedge : e ∈ T.graph.edgeSet) :
    sideDoublingSum T e u = 1 := by
  obtain ⟨x, rfl⟩ := hu
  have hdeg : T.graph.degree (T.leaf x) = 1 :=
    (T.isLeaf_iff_degree_eq_one (T.leaf x)).mp ⟨x, rfl⟩
  obtain ⟨b, hb, huniq⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hdeg
  induction e using Sym2.ind with
  | h a c =>
    rw [Sym2.mem_iff] at he
    rcases he with h | h
    · subst h
      rw [SimpleGraph.mem_edgeSet] at hedge
      rw [huniq c hedge]
      exact sideDoublingSum_leaf_edge T hb
    · subst h
      rw [SimpleGraph.mem_edgeSet] at hedge
      have hab : a = b := huniq a hedge.symm
      subst hab
      rw [Sym2.eq_swap]
      exact sideDoublingSum_leaf_edge T hb

/-! ## ⑩ ③ 步情形的第一块：从「度 3」取出 `u` 的另两条邻边

内部顶点 `u`（二叉 ⇒ 度为 `3` ✓）与一条邻边 `s(u,y₀)` 给出**覆盖假设** ✓：

　`∃ v w, v ≠ w ∧ ∀ z, Adj u z → z = y₀ ∨ z = v ∨ z = w` ✓。

手段（与库内 `PhylogramContract.lean:427-434` 的"度 2 取两条邻边"**完全同款** ✓）：
`SimpleGraph.card_neighborFinset_eq_degree`（`Finite.lean:244` ✓）把度换成 `neighborFinset` 的基数 ✓；
`y₀` 在集里 ✓；按 `Finset.card_erase_of_mem` 删去后基数为 `2` ✓；
再用 **`Finset.card_eq_two`**（`Card.lean:800` ✓）取出 `v, w` ✓；
最后由 `Finset.insert_erase` 还原覆盖假设 ✓。 -/

omit [Fintype X] [DecidableEq X] in
/-- ★★ **度 3 ⇒ 取出另两条邻边**（覆盖假设 ✓）。 -/
theorem exists_two_adj_of_card_three (T : Cladogram X) {u : T.V}
    (h3 : (T.graph.neighborFinset u).card = 3) {y₀ : T.V} (hy₀ : T.graph.Adj u y₀) :
    ∃ v w : T.V, T.graph.Adj u v ∧ T.graph.Adj u w ∧ v ≠ w ∧ v ≠ y₀ ∧ w ≠ y₀ ∧
      ∀ z : T.V, T.graph.Adj u z → z = y₀ ∨ z = v ∨ z = w := by
  have hy₀mem : y₀ ∈ T.graph.neighborFinset u :=
    (SimpleGraph.mem_neighborFinset T.graph u y₀).mpr hy₀
  have h2 : ((T.graph.neighborFinset u).erase y₀).card = 2 := by
    rw [Finset.card_erase_of_mem hy₀mem, h3]
  obtain ⟨v, w, hvw, hpair⟩ := Finset.card_eq_two.mp h2
  have hvmem : v ∈ (T.graph.neighborFinset u).erase y₀ := by rw [hpair]; simp
  have hwmem : w ∈ (T.graph.neighborFinset u).erase y₀ := by rw [hpair]; simp
  have hvne : v ≠ y₀ := (Finset.mem_erase.mp hvmem).1
  have hwne : w ≠ y₀ := (Finset.mem_erase.mp hwmem).1
  have huv : T.graph.Adj u v :=
    (SimpleGraph.mem_neighborFinset T.graph u v).mp (Finset.mem_erase.mp hvmem).2
  have huw : T.graph.Adj u w :=
    (SimpleGraph.mem_neighborFinset T.graph u w).mp (Finset.mem_erase.mp hwmem).2
  refine ⟨v, w, huv, huw, hvw, hvne, hwne, fun z hz => ?_⟩
  have hzmem : z ∈ T.graph.neighborFinset u :=
    (SimpleGraph.mem_neighborFinset T.graph u z).mpr hz
  rw [← Finset.insert_erase hy₀mem, hpair] at hzmem
  simpa only [Finset.mem_insert, Finset.mem_singleton] using hzmem

omit [Fintype X] [DecidableEq X] in
/-- ★★ **二叉内部点 ⇒ 覆盖假设**（把 ⑩ 的第一块与 `IsBinary.degree_eq_three` 接起来 ✓）。 -/
theorem exists_two_adj_of_isBinary (T : Cladogram X) (hbin : T.IsBinary) {u : T.V}
    (hu : ¬ T.IsLeaf u) {y₀ : T.V} (hy₀ : T.graph.Adj u y₀) :
    ∃ v w : T.V, T.graph.Adj u v ∧ T.graph.Adj u w ∧ v ≠ w ∧ v ≠ y₀ ∧ w ≠ y₀ ∧
      ∀ z : T.V, T.graph.Adj u z → z = y₀ ∨ z = v ∨ z = w :=
  exists_two_adj_of_card_three T (by
    rw [SimpleGraph.card_neighborFinset_eq_degree]
    exact hbin.degree_eq_three hu) hy₀

/-- ★★★ **打包：二叉内部点处 `e` 的两侧分划 ＋ 不交** ✓
（正是 ② 代数内核所需的 `hpart` 与 `hdisj` ✓）。 -/
theorem sideLeaves_eq_union_of_isBinary (T : Cladogram X) (hbin : T.IsBinary) {u : T.V}
    (hu : ¬ T.IsLeaf u) {y₀ : T.V} (hy₀ : T.graph.Adj u y₀) {e : Sym2 T.V} (he : e = s(u, y₀)) :
    ∃ v w : T.V, T.graph.Adj u v ∧ T.graph.Adj u w ∧ v ≠ w ∧
      T.sideLeaves e u = T.sideLeaves s(u, v) v ∪ T.sideLeaves s(u, w) w ∧
      Disjoint (T.sideLeaves s(u, v) v) (T.sideLeaves s(u, w) w) := by
  obtain ⟨v, w, huv, huw, hvw, hvy, hwy, hcover⟩ := exists_two_adj_of_isBinary T hbin hu hy₀
  -- `e ≠ s(u,v)`（否则 v = y₀）
  have hnev : s(u, v) ≠ e := by
    intro hc
    have h1 : s(u, v) = s(u, y₀) := hc.trans he
    rcases Sym2.eq_iff.mp h1 with ⟨-, h⟩ | ⟨_, h⟩
    · exact hvy h
    · exact absurd h.symm huv.ne
  have hnew : s(u, w) ≠ e := by
    intro hc
    have h1 : s(u, w) = s(u, y₀) := hc.trans he
    rcases Sym2.eq_iff.mp h1 with ⟨-, h⟩ | ⟨_, h⟩
    · exact hwy h
    · exact absurd h.symm huw.ne
  refine ⟨v, w, huv, huw, hvw, ?_, disjoint_sideLeaves_of_adj_adj T huv huw hvw⟩
  ext x
  constructor
  · intro hx
    exact mem_union_sideLeaves_of_mem_sideLeaves T he hcover
      (fun h => hu (h ▸ (⟨x, rfl⟩ : T.IsLeaf (T.leaf x)))) hx
  · intro hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact mem_sideLeaves_of_mem_sideLeaves_adj T huv he hnev hx
    · exact mem_sideLeaves_of_mem_sideLeaves_adj T huw he hnew hx

omit [Fintype X] [DecidableEq X] in
/-- ★★ **取锚点**：`e ∋ u` 且 `e` 是真边 ⇒ `∃ y₀, Adj u y₀ ∧ e = s(u, y₀)` ✓。 -/
theorem exists_adj_of_mem_of_mem_edgeSet (T : Cladogram X) {u : T.V} {e : Sym2 T.V}
    (he : u ∈ e) (hedge : e ∈ T.graph.edgeSet) :
    ∃ y₀ : T.V, T.graph.Adj u y₀ ∧ e = s(u, y₀) := by
  induction e using Sym2.ind with
  | h a b =>
    rw [Sym2.mem_iff] at he
    rcases he with h | h
    · subst h
      exact ⟨b, by rwa [SimpleGraph.mem_edgeSet] at hedge, rfl⟩
    · subst h
      rw [SimpleGraph.mem_edgeSet] at hedge
      exact ⟨a, hedge.symm, Sym2.eq_swap⟩

/-- ★★★ **一支的 card 严格小于并集**（归纳假设的前提 ✓）：
若 `sideLeaves E u = A ∪ B` 且 `A ⊥ B`，`B` 非空（由 `Adj u w` 得一叶 ✓），则 `A.card < (sideLeaves E u).card` ✓。 -/
theorem card_sideLeaves_lt_of_union (T : Cladogram X) {u v w : T.V} {E : Sym2 T.V}
    (huw : T.graph.Adj u w)
    (hpart : T.sideLeaves E u = T.sideLeaves s(u, v) v ∪ T.sideLeaves s(u, w) w)
    (hdisj : Disjoint (T.sideLeaves s(u, v) v) (T.sideLeaves s(u, w) w)) :
    (T.sideLeaves s(u, v) v).card < (T.sideLeaves E u).card := by
  rw [hpart]
  refine Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
    ⟨Finset.subset_union_left, ?_⟩)
  intro hEq
  have hBsub : T.sideLeaves s(u, w) w ⊆ T.sideLeaves s(u, v) v := by
    rw [hEq]; exact Finset.subset_union_right
  obtain ⟨x, hx⟩ := T.sideLeaves_nonempty_of_adj' huw
  exact (Finset.disjoint_left.mp hdisj (hBsub hx)) hx

/-! ## ⑬ ★★★ **最终定理**：二叉树上 `D_e(u) = 1`

把 ② 的代数内核、⑤ 的前向引理、⑦ 的不交、⑧ 的反向包含、⑩ 的取邻边、⑫ 的取锚点与 card 不等式
与 (b) 的深度关系接起来，对 `(T.sideLeaves e u).card` 做**强归纳**：

* **底**（`u` 是叶）：`sideDoublingSum_eq_one_of_isLeaf` ✓；
* **步**（`u` 内部，二叉 ⇒ 度 `3`）：取锚点 `e = s(u,y₀)` ⇒ 取另两条邻边 `v, w`
  ⇒ 代入 ② 得 `D_e(u) = (1/2)·(D_{s(u,v)}(v) + D_{s(u,w)}(w))`
  ⇒ 两支的 `card` 严格更小（⑫ ✓）⇒ 归纳假设给两支各为 `1` ⇒ `(1/2)(1+1) = 1` ✓。

⚠️ `e` 必须是**真边**（`e ∈ T.graph.edgeSet` ✓）：否则取锚点不成立，命题为假 ✗。 -/

/-- ★★★ **最终定理**：二叉树上，真边 `e` 与 `u ∈ e` ⇒ `D_e(u) = 1` ✓
（`sideDoublingSum` 的**子树倍增归一化** ✓ —— Pauplin 公式的核心恒等式 ✓）。 -/
theorem sideDoublingSum_eq_one_of_isBinary (T : Cladogram X) (hbin : T.IsBinary) :
    ∀ (n : ℕ) (u : T.V) (e : Sym2 T.V), u ∈ e → e ∈ T.graph.edgeSet →
      (T.sideLeaves e u).card = n → sideDoublingSum T e u = 1 := by
  intro n
  refine Nat.strong_induction_on n ?_
  intro m ih u e he hedge hcard
  by_cases hu : T.IsLeaf u
  · exact sideDoublingSum_eq_one_of_isLeaf T hu he hedge
  · obtain ⟨y₀, hy₀, hee⟩ := exists_adj_of_mem_of_mem_edgeSet T he hedge
    obtain ⟨v, w, huv, huw, hvw, hpart, hdisj⟩ :=
      sideLeaves_eq_union_of_isBinary T hbin hu hy₀ hee
    have hdv : ∀ x ∈ T.sideLeaves s(u, v) v,
        (T.pathOf u (T.leaf x)).edges.length = (T.pathOf v (T.leaf x)).edges.length + 1 :=
      fun x hx => length_pathOf_eq_succ_of_adj_of_mem_sideLeaves T huv hx
    have hdw : ∀ x ∈ T.sideLeaves s(u, w) w,
        (T.pathOf u (T.leaf x)).edges.length = (T.pathOf w (T.leaf x)).edges.length + 1 :=
      fun x hx => length_pathOf_eq_succ_of_adj_of_mem_sideLeaves T huw hx
    have hrec := sideDoublingSum_eq_half_mul_add_of_union T e u v w hpart hdisj hdv hdw
    have hcv : (T.sideLeaves s(u, v) v).card < (T.sideLeaves e u).card :=
      card_sideLeaves_lt_of_union T huw hpart hdisj
    have hcw : (T.sideLeaves s(u, w) w).card < (T.sideLeaves e u).card := by
      rw [hpart]
      refine Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
        ⟨Finset.subset_union_right, ?_⟩)
      intro hEq
      have hAsub : T.sideLeaves s(u, v) v ⊆ T.sideLeaves s(u, w) w := by
        rw [hEq]; exact Finset.subset_union_left
      obtain ⟨x, hx⟩ := T.sideLeaves_nonempty_of_adj' huv
      exact (Finset.disjoint_left.mp hdisj hx) (hAsub hx)
    have hDv : sideDoublingSum T s(u, v) v = 1 :=
      ih _ (by rw [← hcard]; exact hcv) v s(u, v) (by simp)
        ((SimpleGraph.mem_edgeSet (G := T.graph) (v := u) (w := v)).mpr huv) rfl
    have hDw : sideDoublingSum T s(u, w) w = 1 :=
      ih _ (by rw [← hcard]; exact hcw) w s(u, w) (by simp)
        ((SimpleGraph.mem_edgeSet (G := T.graph) (v := u) (w := w)).mpr huw) rfl
    rw [hDv, hDw] at hrec
    linarith

end Phylo.SideDoubling
