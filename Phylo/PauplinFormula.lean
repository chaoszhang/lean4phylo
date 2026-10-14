/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.TreeDistance
import Phylo.BMELeastSquares
import Phylo.SplitsMaximal

/-!
# `Phylo.PauplinFormula` —— Pauplin（BME）树长公式（W11g · D2）

## 0. 文献与逐行依据

* **Pauplin, Y. (2000)**, *Direct calculation of a tree length using a distance matrix*,
  J. Mol. Evol. **51**(1):41–47 —— 公式的**原始出处**。
  ⚠️ **未入库**（W11g 派单原文已注：「Pauplin 2000 / Gascuel–Steel 2006 **未下载**」）
  ⇒ 本文件**不引用**其行号。
* **Desper, R. & Gascuel, O. (2004)**, *Theoretical Foundation of the Balanced Minimum
  Evolution Method of Phylogenetic Inference and Its Relationship to Weighted Least-Squares
  Tree Fitting*, Mol. Biol. Evol. **21**(3):587–598
  （`references/md/DesperGascuel2004_BalancedMinimumEvolution.md`，**在手**，行号即该 md 行号）。
  其中
  * **式 (4)**（`:394–404`）★：`l̂(T) = Σ_{i<j} 2^{1−p_ij} d_ij`，`p_ij` = `T` 上路径的**边数**；
  * **式 (9)**（`:2027`）：`SᵗF = 1`，即逐边的 **Pauplin 归一化**；
  * **Appendix 2**（`:2021–2032`）：式 (9) 是线性估计量**无偏**（= 对**任意**边权给出真树长）
    的**充要**条件。
* **Mihaescu, Levy & Pachter (2006)**（`MihaescuLevyPachter2006_WhyNeighborJoiningWorks.md`，
  在手）：第 **154 行**转述同一公式 —— 这是派单允许的**转述依据**。

## 1. 本文件在库内的位置（★A 扫描结论）

`Phylo/BMELeastSquares.lean`（W11g · D3）已经给出**抽象层**：

| 已有零件 | 位置 |
|---|---|
| `bmeCoeff p = 2^{1−p}` | `BMELeastSquares.lean:81` |
| `Dissimilarity.plane` / `sum_sum_eq_plane` | `:171, :176` |
| `Dissimilarity.bmeLength c δ = ½ Σ_{i,j} c_ij δ_ij` | `:188` |
| ★★★ `wls_consistent_of_incidence_one`（式 (9) ⟹ 一致） | `:242` |
| ★★★ `bme_length_eq_true_length`（式 (9) 的具体形式 ⟹ `l̂ = l`） | `:262` |
| ★C `ex4_pauplin_internal` / `ex4_pauplin_pendant` / `ex4_bmeLength` | `:314, :321, :326` |
| ⬜ `bme_pauplin_identity_gap` —— 「**没有**「顶点对 ↔ 边」的关联判定 `e ∈ P_ij`，也没有沿路径计数的接口」 | `:372` |

**本文件补的正是那个接口**：

* ★★ `pathWalk` / `topoDist`（`n_ij` = **真路径的边数**）/ `incidence`（`e ∈ P_ij` 的指示函数）
  —— 全部**从 `Phylogram` 造出来**（不再是抽象假设）；
* ★★★ `dist_eq_sum_incidence`：`T.dist (leaf i) (leaf j) = Σ_e incidence i j e · wExt e`
  ⇒ **`bme_pauplin_identity_gap` 的 (1)（可加性）在树层被构造性给出**；
* ★★★ `sum_incidence_eq_topoDist`：`Σ_e incidence i j e = n_ij`
  ⇒ **该缺口的 (2)（关联计数 = 路径边数）被给出**；
* ★★★ `pauplinLength_eq_trueLength_of_edgeCoeff`：**只剩**「逐边 Pauplin 归一化 = 2」
  （式 (9)）这一个条件，公式即成立 —— 于是缺口**精确地**收缩为 `pauplinEdgeCoeff_gap`；
* `pauplinLength`（式 (4) 的**树层字面转写**，`d_ij` = 库内 `Phylogram.dist`）＋ `trueLength`。

## 2. ★B 反例检查（重要）

**式 (4) 只对二叉（fully resolved）树成立。** 取 4 叶**星形树**（唯一内点度 = 4，非二叉）：
挂边 `e_x` 出现在 `x` 到另外 **3** 个叶的路径上，且这些路径的边数都是 `2` ⇒ 系数

　　`Σ 2^{1−n} = 3 · 2^{−1} = 3/2 ≠ 1`  ⟹  `l̂(T) ≠ l(T)`。

对二叉内点（度 3）正相反：另外只有 **2** 个邻居 ⇒ 系数 `= 2 · 2^{−1} = 1` ✓。
本文件把这两条写成 `starCoeff_two` / `starCoeff_three_ne_one`。
⇒ **所有一般性陈述都必须带 `T.IsBinary`**（本文件的缺口定义都带）。

## 3. ★C 最小具体例子（精确、无 Monte Carlo）

* 3 叶星形（二叉、唯一拓扑）：`n_ij ≡ 2`，`d = (3,5,6)`，真树长 `1+2+4 = 7`，
  Pauplin 和 `= ½·(½)(3+5+6)·2 = 7` ✓（`ex3_pauplin_arith` / `ex3_total`）；
* 4 叶（二叉）：`ex4_*`（`BMELeastSquares.lean`，Pauplin 归一化逐边验证 + `l̂ = 15 = l`）。
* 更一般的穷举见 `scripts/msc/w11g_n3_d2_t4_check.py`（`n = 4…7` 全部二叉拓扑、精确有理数）。
-/

open Phylo

namespace NJ

namespace Pauplin

open Dissimilarity

variable {X : Type*} [Fintype X] [DecidableEq X]

/-! ## 1. 从 `Phylogram` 造出「路径」「路径边数」「关联」 -/

/-- `x` 到 `y` 的**唯一路径**（`Phylogram.dist` 的见证）。 -/
noncomputable def pathWalk (T : Phylogram X) (x y : X) :
    T.graph.Walk (T.leaf x) (T.leaf y) :=
  (T.existsUnique_path (T.leaf x) (T.leaf y)).choose

omit [Fintype X] [DecidableEq X] in
/-- 该路径是 `IsPath`（故其边表 `Nodup` —— 关联计数要用）。 -/
theorem pathWalk_isPath (T : Phylogram X) (x y : X) : (pathWalk T x y).IsPath :=
  (T.existsUnique_path (T.leaf x) (T.leaf y)).choose_spec.1

/-- ★★ **`n_xy`：路径上的边数**（式 (4) 的 `p_ij`，即**拓扑距离**）。 -/
noncomputable def topoDist (T : Phylogram X) (x y : X) : ℕ := (pathWalk T x y).length

/-- ★★ **路径关联**：边 `e` 是否在 `x`-`y` 路径上（式 (9) 的 `S_ij(e)`）。 -/
noncomputable def incidence (T : Phylogram X) (x y : X) (e : Sym2 T.V) : ℝ :=
  if e ∈ (pathWalk T x y).edges then 1 else 0

/-! ### ★★★ W19 补：把 `pathWalk` 与 `Cladogram.pathOf` 接上（桥的第一块）

`pathWalk` 是 `existsUnique_path` 的 `choose` ✓，而**树中路径唯一** ✓ ⇒ 它与
`T.pathOf (T.leaf x) (T.leaf y)` 是**同一条** ✓。接上之后，库内已有的**顶点级**引理
`Cladogram.mem_pathOf_edges_iff_not_inSide`（`AttesonRadius.lean:1394` ✓）就能用在
`pathWalk`/`incidence` 上 —— 这正是把 `sideDoublingSum` 与 `bmeCoeff·incidence`
两套形式化接起来所缺的第一块砖 ✓。 -/

omit [Fintype X] [DecidableEq X] in
/-- ★★ **`pathWalk` 就是 `pathOf`**（树中两点间路径唯一 ✓）。 -/
theorem pathWalk_eq_pathOf (T : Phylogram X) (x y : X) :
    pathWalk T x y = T.pathOf (T.leaf x) (T.leaf y) :=
  (T.existsUnique_path (T.leaf x) (T.leaf y)).unique (pathWalk_isPath T x y)
    (T.pathOf_isPath (T.leaf x) (T.leaf y))

/-- ★★★ **同侧对不含 `e`** ✓：`x`、`y` 都落在 `e` 的 `u` 侧 ⇒ `e` 不在 `x`-`y` 路径上
⇒ `S_xy(e) = 0` ✓（桥的"同侧贡献为零"那一半 ✓）。

证明：两端点都从 `u` 在 `T - e` 中可达 ⇒ 它们在 `T - e` 中互通 ✓ ⇒
由 `mem_pathOf_edges_iff_not_inSide` 的**逆否**，`e ∉ (pathOf (leaf x) (leaf y)).edges` ✓
⇒ 经上一条换成 `pathWalk` ✓。 -/
theorem incidence_eq_zero_of_same_side (T : Phylogram X) {e : Sym2 T.V} {u : T.V} {x y : X}
    (hx : x ∈ T.sideLeaves e u) (hy : y ∈ T.sideLeaves e u) : incidence T x y e = 0 := by
  rw [incidence]
  have hx' : T.inSide e u (T.leaf x) := (T.mem_sideLeaves_iff_inSide).mp hx
  have hy' : T.inSide e u (T.leaf y) := (T.mem_sideLeaves_iff_inSide).mp hy
  have hside : T.inSide e (T.leaf x) (T.leaf y) := hx'.symm.trans hy'
  have hnot : e ∉ (pathWalk T x y).edges := by
    rw [pathWalk_eq_pathOf T x y]
    exact fun h => ((T.mem_pathOf_edges_iff_not_inSide (e := e)
      (u := T.leaf x) (v := T.leaf y)).mp h) hside
  simp [hnot]

/-- ★★★ **跨侧对必含 `e`** ✓：`x` 落在 `e = s(u,v)` 的 `v` 侧、`y` 落在 `u` 侧 ⇒
`e` **在** `x`-`y` 路径上 ⇒ `S_xy(e) = 1` ✓（桥公式"跨侧贡献"的那一半 ✓，与
`incidence_eq_zero_of_same_side` 配对 ✓）。

证明：若两叶在 `T - e` 中互通，则沿「`v` ↔ `leaf x`」与「`leaf y` ↔ `u`」两段可得
`v` 与 `u` 在 `T - e` 中互通，与「边是桥」（`not_reachable_deleteEdges_of_adj`）矛盾 ✓
⇒ `¬ inSide e (leaf x) (leaf y)` ⇒ 由 `mem_pathOf_edges_iff_not_inSide` 的 `.mpr`
得 `e ∈ (pathOf (leaf x) (leaf y)).edges` ⇒ 经 `pathWalk_eq_pathOf` 换成 `pathWalk` ✓。 -/
theorem incidence_eq_one_of_mem_sideLeaves_of_adj (T : Phylogram X) {u v : T.V}
    (huv : T.graph.Adj u v) {x y : X}
    (hx : x ∈ T.sideLeaves s(u, v) v) (hy : y ∈ T.sideLeaves s(u, v) u) :
    incidence T x y s(u, v) = 1 := by
  have hx' : T.inSide s(u, v) v (T.leaf x) := (T.mem_sideLeaves_iff_inSide).mp hx
  have hy' : T.inSide s(u, v) u (T.leaf y) := (T.mem_sideLeaves_iff_inSide).mp hy
  have hnot : ¬ T.inSide s(u, v) (T.leaf x) (T.leaf y) := by
    intro hc
    -- hc : Reachable (leaf x) (leaf y)，hx'.symm : Reachable (leaf x) v，hy' : Reachable u (leaf y)
    exact (T.not_reachable_deleteEdges_of_adj huv)
      (hx'.trans (hc.trans hy'.symm)).symm
  have hmem : s(u, v) ∈ (pathWalk T x y).edges := by
    rw [pathWalk_eq_pathOf T x y]
    exact (T.mem_pathOf_edges_iff_not_inSide (e := s(u, v))
      (u := T.leaf x) (v := T.leaf y)).mpr hnot
  rw [incidence, ite_eq_left hmem]

/-- ★★★ **跨侧两段路径的支撑集不交** ✓（路径长度可加性的前置 ✓）：
`x` 在 `e = s(u,v)` 的 `v` 侧、`y` 在 `u` 侧时，
「`leaf x` → `v`」与「`u` → `leaf y`」两段路径**没有公共顶点** ✓。

证明：若 `z` 同时落在两段支撑集里，则用 `takeUntil z` 取各自的前缀 ✓，
其边表 ⊆ 全路径边表（`SimpleGraph.Walk.edges_takeUntil_subset_edges`）⇒ 两段都**避开** `e`
（全路径避 `e`，由 `mem_pathOf_edges_iff_not_inSide` 与 `hx`/`hy` ✓）
⇒ 在 `T - e` 中得 `v → leaf x → z → u` 可达 ⇒ `v` 与 `u` 在 `T - e` 中互通 ⇒ 与「边是桥」矛盾 ✓。 -/
theorem disjoint_support_pathOf_of_mem_sideLeaves (T : Cladogram X) {u v : T.V}
    (huv : T.graph.Adj u v) {x y : X}
    (hx : x ∈ T.sideLeaves s(u, v) v) (hy : y ∈ T.sideLeaves s(u, v) u) :
    ∀ z, z ∈ (T.pathOf (T.leaf x) v).support → z ∈ (T.pathOf u (T.leaf y)).support → False := by
  intro z hzx hzy
  have hxv : T.inSide s(u, v) v (T.leaf x) := (T.mem_sideLeaves_iff_inSide).mp hx
  have hyu : T.inSide s(u, v) u (T.leaf y) := (T.mem_sideLeaves_iff_inSide).mp hy
  -- 两段路径都避开 e
  have e1 : s(u, v) ∉ (T.pathOf (T.leaf x) v).edges := fun h =>
    ((T.mem_pathOf_edges_iff_not_inSide (e := s(u, v)) (u := T.leaf x) (v := v)).mp h)
      ((T.inSide_comm s(u, v) v (T.leaf x)).mp hxv)
  have e2 : s(u, v) ∉ (T.pathOf u (T.leaf y)).edges := fun h =>
    ((T.mem_pathOf_edges_iff_not_inSide (e := s(u, v)) (u := u) (v := T.leaf y)).mp h) hyu
  -- 前缀给出避开 e 的走法
  have h1 : (T.graph.deleteEdges {s(u, v)}).Reachable (T.leaf x) z :=
    SimpleGraph.reachable_deleteEdges_of_notMem_edges _
      (fun h => e1 (SimpleGraph.Walk.edges_takeUntil_subset_edges (T.pathOf (T.leaf x) v) hzx h))
  have h2 : (T.graph.deleteEdges {s(u, v)}).Reachable u z :=
    SimpleGraph.reachable_deleteEdges_of_notMem_edges _
      (fun h => e2 (SimpleGraph.Walk.edges_takeUntil_subset_edges (T.pathOf u (T.leaf y)) hzy h))
  exact (T.not_reachable_deleteEdges_of_adj huv)
    (hxv.trans (h1.trans h2.symm)).symm

/-! ### ★★★ W19：跨侧边数可加性（桥的「量值」那一半）

`x` 在 `e = s(u,v)` 的 `v` 侧、`y` 在 `u` 侧时

　`topoDist T x y = |pathOf (leaf x) v| + 1 + |pathOf u (leaf y)|` ✓。

**路线（教训 391：Mathlib 无 `IsPath.append` 构造器 ⇒ 走「不交 ＋ 唯一性」）**：
拼 `q := (pathOf (leaf x) v).append (cons huv.symm (pathOf u (leaf y)))` ✓
⇒ 证 `q.IsPath`（`List.Nodup.append` ✓：两段各自 `IsPath` ✓、跨侧支撑集不交 ✓、`v ∉ 第二段支撑集` ✓）
⇒ 由 `existsUnique_path` 的**唯一性** ⇒ `q = pathWalk T x y` ✓ ⇒ 取 `length` ✓。

★ 关键：`support_append` 给出 `p.support ++ p'.support.tail` ✓，而
`(v :: p''.support).tail` **定义上就是** `p''.support` ✓（`support_cons` 后自动消去 ✓）。 -/

/-- ★★★ **跨侧边数可加性** ✓（桥公式「量值」那一半 ✓）。 -/
theorem topoDist_eq_add_of_mem_sideLeaves (T : Phylogram X) {u v : T.V}
    (huv : T.graph.Adj u v) {x y : X}
    (hx : x ∈ T.sideLeaves s(u, v) v) (hy : y ∈ T.sideLeaves s(u, v) u) :
    topoDist T x y = (T.pathOf (T.leaf x) v).edges.length + 1
      + (T.pathOf u (T.leaf y)).edges.length := by
  have hyu : T.inSide s(u, v) u (T.leaf y) := (T.mem_sideLeaves_iff_inSide).mp hy
  have e2 : s(u, v) ∉ (T.pathOf u (T.leaf y)).edges := fun h =>
    ((T.mem_pathOf_edges_iff_not_inSide (e := s(u, v)) (u := u) (v := T.leaf y)).mp h) hyu
  -- `v` 不在第二段支撑集里
  have hv_not : v ∉ (T.pathOf u (T.leaf y)).support := by
    intro hv
    exact (T.not_reachable_deleteEdges_of_adj huv)
      (SimpleGraph.reachable_deleteEdges_of_notMem_edges _
        (fun h => e2 (SimpleGraph.Walk.edges_takeUntil_subset_edges (T.pathOf u (T.leaf y)) hv h)))
  -- 拼接走法是路径
  have hpath : ((T.pathOf (T.leaf x) v).append
      (SimpleGraph.Walk.cons huv.symm (T.pathOf u (T.leaf y)))).IsPath := by
    rw [SimpleGraph.Walk.isPath_def, SimpleGraph.Walk.support_append, SimpleGraph.Walk.support_cons]
    refine List.Nodup.append ?_ ?_ ?_
    · rw [← SimpleGraph.Walk.isPath_def]; exact T.pathOf_isPath (T.leaf x) v
    · rw [List.tail_cons, ← SimpleGraph.Walk.isPath_def]
      exact T.pathOf_isPath u (T.leaf y)
    · rw [List.disjoint_iff_ne]
      intro a ha b hb hab
      exact disjoint_support_pathOf_of_mem_sideLeaves T.toCladogram huv hx hy a ha (hab.symm ▸ hb)
  -- 唯一性 ⇒ 就是 pathWalk
  have heq : pathWalk T x y
      = (T.pathOf (T.leaf x) v).append
        (SimpleGraph.Walk.cons huv.symm (T.pathOf u (T.leaf y))) :=
    (T.existsUnique_path (T.leaf x) (T.leaf y)).unique (pathWalk_isPath T x y) hpath
  rw [topoDist, heq, SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_cons,
    SimpleGraph.Walk.length_edges, SimpleGraph.Walk.length_edges]
  omega

/-- ★★★ **跨侧单对的【量值】** ✓（桥公式的代数内核 ✓）：
`x` 在 `e = s(u,v)` 的 `v` 侧、`y` 在 `u` 侧时

　`bmeCoeff (topoDist x y) = 2 · (1/2)^{d_u(x)} · (1/2)^{d_v(y)}` ✓
（`d_u(x) = |pathOf (leaf x) v|`，`d_v(y) = |pathOf u (leaf y)|` ✓）。
证：`bmeCoeff p = 2·(1/2)^p` ＋ 边数可加性 ＋ `pow_add`/`pow_one` ＋ `ring` ✓。 -/
theorem bmeCoeff_topoDist_of_mem_sideLeaves (T : Phylogram X) {u v : T.V}
    (huv : T.graph.Adj u v) {x y : X}
    (hx : x ∈ T.sideLeaves s(u, v) v) (hy : y ∈ T.sideLeaves s(u, v) u) :
    bmeCoeff (topoDist T x y)
      = (1 / 2) ^ ((T.pathOf (T.leaf x) v).edges.length)
        * (1 / 2) ^ ((T.pathOf u (T.leaf y)).edges.length) := by
  rw [bmeCoeff, topoDist_eq_add_of_mem_sideLeaves T huv hx hy, pow_add]
  ring

/-- ★★ **同侧单对的贡献为 `0`** ✓（`incidence = 0` ⇒ 乘任何系数都是 `0` ✓）。 -/
theorem bmeCoeff_mul_incidence_eq_zero_of_same_side (T : Phylogram X) {e : Sym2 T.V} {u : T.V}
    {x y : X} (hx : x ∈ T.sideLeaves e u) (hy : y ∈ T.sideLeaves e u) :
    bmeCoeff (topoDist T x y) * incidence T x y e = 0 := by
  rw [incidence_eq_zero_of_same_side T hx hy, mul_zero]

/-- ★★★ **跨侧单对的【贡献】** ✓：`bmeCoeff · incidence = 2·(1/2)^{d_u(x)}·(1/2)^{d_v(y)}` ✓。 -/
theorem bmeCoeff_mul_incidence_of_mem_sideLeaves (T : Phylogram X) {u v : T.V}
    (huv : T.graph.Adj u v) {x y : X}
    (hx : x ∈ T.sideLeaves s(u, v) v) (hy : y ∈ T.sideLeaves s(u, v) u) :
    bmeCoeff (topoDist T x y) * incidence T x y s(u, v)
      = (1 / 2) ^ ((T.pathOf (T.leaf x) v).edges.length)
        * (1 / 2) ^ ((T.pathOf u (T.leaf y)).edges.length) := by
  rw [bmeCoeff_topoDist_of_mem_sideLeaves T huv hx hy,
    incidence_eq_one_of_mem_sideLeaves_of_adj T huv hx hy]
  ring

/-! **★★★ W19 最后拼装 ①：逐点恒等式（四情形）** ✓

关键取舍（教训 397 的直接后果 ✓）：**不**做「子集和 → `univ`」的转换 ✗，
而把等式**两边都写成 `univ` 上的双重和**（用**指示函数** ✓）⇒ 逐点 `Finset.sum_congr` 即可 ✓。

四情形（`A = sideLeaves e u`、`B = sideLeaves e v`、`e = s(u,v)` ✓，用 `inSide_or_inSide` ✓）：
* `x ∈ B, y ∈ A` ⇒ 跨侧 ⇒ `incidence = 1` ⇒ 贡献 `(1/2)^{d_v(x)}·(1/2)^{d_u(y)}` ✓；
* `x ∈ A, y ∈ B` ⇒ 跨侧（**镜像**，用 `huv.symm` ＋ `Sym2.eq_swap` ✓）⇒ `(1/2)^{d_u(x)}·(1/2)^{d_v(y)}` ✓；
* 同侧的两种 ⇒ `incidence = 0` ⇒ 贡献 `0` ✓。
⇒ ★ **两行都非零** ✓（纠正见 MEMORY 377 批 ✓），合计 `D_u·D_v + D_v·D_u = 2·D_u·D_v` ✓。 -/

/-! **★★★ W19 最后拼装 ①：逐点恒等式（四情形）** ✓

`A = sideLeaves e u`、`B = sideLeaves e v`、`e = s(u,v)` ✓ ——

　`bmeCoeff(topoDist x y)·incidence x y e`
　`= if x ∈ B ∧ y ∈ A then (1/2)^{d_v(x)}·(1/2)^{d_u(y)}`
　`  else if x ∈ A ∧ y ∈ B then (1/2)^{d_u(x)}·(1/2)^{d_v(y)} else 0` ✓

★ 三条约定（MEMORY 378 批 ✓）已全部用上：
`ite_eq_right`/`ite_eq_left` 代替弃用的 `if_neg`/`if_pos` ✓；
`ite` 条件非恒真 ⇒ 用 `not_inSide_both`（`Split.lean:750` ✓）证明其为假 ✓；
`inSide e a b` 第二参是起点 ⇒ `inSide_or_inSide` 给【从叶出发】✗，需 `inSide_comm` 翻成【以基准为起点】✓。 -/

/-- ★★★ **逐点恒等式**（桥公式最后拼装的第①步 ✓）。 -/
theorem contribution_eq_ite (T : Phylogram X) {u v : T.V} (huv : T.graph.Adj u v) (x y : X) :
    bmeCoeff (topoDist T x y) * incidence T x y s(u, v)
      = if x ∈ T.sideLeaves s(u, v) v ∧ y ∈ T.sideLeaves s(u, v) u then
          (1 / 2) ^ (T.pathOf (T.leaf x) v).edges.length
            * (1 / 2) ^ (T.pathOf u (T.leaf y)).edges.length
        else if x ∈ T.sideLeaves s(u, v) u ∧ y ∈ T.sideLeaves s(u, v) v then
          (1 / 2) ^ (T.pathOf (T.leaf x) u).edges.length
            * (1 / 2) ^ (T.pathOf v (T.leaf y)).edges.length
        else 0 := by
  have hxu := T.inSide_or_inSide huv (x := T.leaf x)
  have hyu := T.inSide_or_inSide huv (x := T.leaf y)
  rcases hxu with hxA | hxB <;> rcases hyu with hyA | hyB
  · -- 都在 u 侧：两个条件都假
    have hxA' : x ∈ T.sideLeaves s(u, v) u :=
      (T.mem_sideLeaves_iff_inSide).mpr ((T.inSide_comm s(u, v) (T.leaf x) u).mp hxA)
    have hyA' : y ∈ T.sideLeaves s(u, v) u :=
      (T.mem_sideLeaves_iff_inSide).mpr ((T.inSide_comm s(u, v) (T.leaf y) u).mp hyA)
    have hxB' : x ∉ T.sideLeaves s(u, v) v := fun h => T.not_inSide_both huv
      ⟨(T.inSide_comm s(u, v) (T.leaf x) u).mp hxA, (T.mem_sideLeaves_iff_inSide).mp h⟩
    have hyB' : y ∉ T.sideLeaves s(u, v) v := fun h => T.not_inSide_both huv
      ⟨(T.inSide_comm s(u, v) (T.leaf y) u).mp hyA, (T.mem_sideLeaves_iff_inSide).mp h⟩
    rw [ite_eq_right (fun hc => hxB' hc.1), ite_eq_right (fun hc => hyB' hc.2)]
    exact bmeCoeff_mul_incidence_eq_zero_of_same_side T hxA' hyA'
  · -- x 在 u 侧、y 在 v 侧：第二个条件为真（镜像跨侧）
    have hxA' : x ∈ T.sideLeaves s(u, v) u :=
      (T.mem_sideLeaves_iff_inSide).mpr ((T.inSide_comm s(u, v) (T.leaf x) u).mp hxA)
    have hyB' : y ∈ T.sideLeaves s(u, v) v :=
      (T.mem_sideLeaves_iff_inSide).mpr ((T.inSide_comm s(u, v) (T.leaf y) v).mp hyB)
    have hxB' : x ∉ T.sideLeaves s(u, v) v := fun h => T.not_inSide_both huv
      ⟨(T.inSide_comm s(u, v) (T.leaf x) u).mp hxA, (T.mem_sideLeaves_iff_inSide).mp h⟩
    have hm := bmeCoeff_mul_incidence_of_mem_sideLeaves T huv.symm
      (show x ∈ T.sideLeaves s(v, u) u by rwa [Sym2.eq_swap])
      (show y ∈ T.sideLeaves s(v, u) v by rwa [Sym2.eq_swap])
    rw [Sym2.eq_swap] at hm
    rw [ite_eq_right (fun hc => hxB' hc.1), ite_eq_left ⟨hxA', hyB'⟩]
    exact hm
  · -- x 在 v 侧、y 在 u 侧：第一个条件为真（跨侧）
    have hxB' : x ∈ T.sideLeaves s(u, v) v :=
      (T.mem_sideLeaves_iff_inSide).mpr ((T.inSide_comm s(u, v) (T.leaf x) v).mp hxB)
    have hyA' : y ∈ T.sideLeaves s(u, v) u :=
      (T.mem_sideLeaves_iff_inSide).mpr ((T.inSide_comm s(u, v) (T.leaf y) u).mp hyA)
    rw [ite_eq_left ⟨hxB', hyA'⟩]
    exact bmeCoeff_mul_incidence_of_mem_sideLeaves T huv hxB' hyA'
  · -- 都在 v 侧：两个条件都假
    have hxB' : x ∈ T.sideLeaves s(u, v) v :=
      (T.mem_sideLeaves_iff_inSide).mpr ((T.inSide_comm s(u, v) (T.leaf x) v).mp hxB)
    have hyB' : y ∈ T.sideLeaves s(u, v) v :=
      (T.mem_sideLeaves_iff_inSide).mpr ((T.inSide_comm s(u, v) (T.leaf y) v).mp hyB)
    have hxA' : x ∉ T.sideLeaves s(u, v) u := fun h => T.not_inSide_both huv
      ⟨(T.mem_sideLeaves_iff_inSide).mp h, (T.inSide_comm s(u, v) (T.leaf x) v).mp hxB⟩
    have hyA' : y ∉ T.sideLeaves s(u, v) u := fun h => T.not_inSide_both huv
      ⟨(T.mem_sideLeaves_iff_inSide).mp h, (T.inSide_comm s(u, v) (T.leaf y) v).mp hyB⟩
    rw [ite_eq_right (fun hc => hyA' hc.2), ite_eq_right (fun hc => hxA' hc.1)]
    exact bmeCoeff_mul_incidence_eq_zero_of_same_side T hxB' hyB'

/-! ### ★★★ W19：子集和 = 指示函数和（最后拼装的**关键砖** ✓）

`∑_{x ∈ s} f x = ∑_x (if x ∈ s then f x else 0)` ✓ ——
由 **`Finset.sum_filter`**（真名已定 ✓：`DFinsupp/BigOperators.lean:305` 等处用它 ✓）
与 `Finset.univ.filter (· ∈ s) = s` 归一 ✓。

★ 这块砖的作用：把 `sideDoublingSum`（**子集和** ✓）与逐点 `ite` 形式（**`univ` 和** ✓）接起来 ✓，
从而「逐点恒等式 ＋ 双重和」就能直接算出 `2·D_e(u)·D_e(v)` ✓。 -/

/-- ★★★ **子集和 = 指示函数和** ✓（最后拼装的关键砖 ✓）。 -/
theorem sum_ite_mem_eq_sum (s : Finset X) (f : X → ℝ) :
    (∑ x : X, if x ∈ s then f x else 0) = ∑ x ∈ s, f x := by
  rw [← Finset.sum_filter]
  simp

omit [DecidableEq X] in
/-- ★★★ **两支双重和的因式分解** ✓（桥公式收口的数学内核 ✓）：

　`Σ_{x∈u侧} Σ_{y∈v侧} (1/2)^{d_u(x)}·(1/2)^{d_v(y)} = D_e(u)·D_e(v)` ✓

证：一行 —— `sideDoublingSum` 的定义 ＋ **`Finset.sum_mul_sum`**
（`BigOperators/Ring/Finset.lean:62` ✓：`Σ i∈s, Σ j∈t, f i * g j = (Σ i∈s, f i) * (Σ j∈t, g j)` ✓）。 -/
theorem sum_sum_mul_of_mem_sideLeaves (T : Phylogram X) {u v : T.V} :
    (∑ x ∈ T.sideLeaves s(u, v) u, ∑ y ∈ T.sideLeaves s(u, v) v,
        (1 / 2) ^ (T.pathOf u (T.leaf x)).edges.length
          * (1 / 2) ^ (T.pathOf v (T.leaf y)).edges.length)
      = sideDoublingSum T.toCladogram s(u, v) u
        * sideDoublingSum T.toCladogram s(u, v) v := by
  rw [sideDoublingSum, sideDoublingSum, Finset.sum_mul_sum]

omit [Fintype X] [DecidableEq X] in
/-- ★★ **路径反向**：`(pathOf a b).reverse = pathOf b a` ✓
（树中路径唯一 ⇒ 与 `pathWalk_eq_pathOf` 同款手法：`existsUnique_path` 的 `.unique` ✓）。 -/
theorem pathOf_reverse_eq (T : Cladogram X) (a b : T.V) :
    (T.pathOf a b).reverse = T.pathOf b a :=
  (T.existsUnique_path b a).unique (T.pathOf_isPath a b).reverse (T.pathOf_isPath b a)

omit [Fintype X] [DecidableEq X] in
/-- ★★ **边数换向**：`|pathOf a b| = |pathOf b a|` ✓（反向 ＋ `length_reverse` ✓ ＋ `length_edges` ✓）。

★ 用途：逐点恒等式里 `x` 侧的指数拼作 `|pathOf (leaf x) u|`（**叶在前** ✗），
而 `sideDoublingSum` 的定义是 `|pathOf u (leaf x)|`（**基准在前** ✓）⇒ 需本引理换向 ✓。 -/
theorem length_pathOf_comm (T : Cladogram X) (a b : T.V) :
    (T.pathOf a b).edges.length = (T.pathOf b a).edges.length := by
  rw [SimpleGraph.Walk.length_edges, SimpleGraph.Walk.length_edges,
    ← SimpleGraph.Walk.length_reverse (T.pathOf a b), pathOf_reverse_eq]

/-! ### ★★★ W19 登记：最后一项（行和引理）—— 形状已定，工具已齐（下一轮落）

**目标** ✓：固定 `x` 后对 `y` 求和

　`Σ_y bmeCoeff(topoDist x y)·incidence x y e`
　`= if x ∈ A then (1/2)^{d_u(x)}·D_e(v) else if x ∈ B then (1/2)^{d_v(x)}·D_e(u) else 0` ✓
（`A = sideLeaves e u`、`B = sideLeaves e v` ✓）

**工具已全部定名** ✓：
* 逐点恒等式：`contribution_eq_ite`（本文件 ✓）；
* 内和的 `ite → 子集和`：**`sum_ite_mem_eq_sum`**（本文件 ✓）；
* 提出常数因子：**`Finset.mul_sum`**／`Finset.sum_mul` ✓；
* 外和按侧划分：**`Finset.sum_add_sum_compl`** ✓（`S` 与其补 ✓，配合 `sideLeaves_compl_adj` ✓）；
* 指数换向：**`length_pathOf_comm`**（本件 ✓）；
* 同型参考（库内已有）：**`AttesonRadius.sum_ite_pathOf_eq_sideLeafCount`**（`:1663` ✓，
  「`Σ_x ite(路径含 e)` = 侧叶数」✓ —— 与本次内和**同型** ✓，可直接照其手法 ✓）。

**收口最后两步** ✓：行和引理（本登记 ✓）⇒ 对 `x` 求和（`sum_add_sum_compl` ✓）
⇒ `D_u·D_v + D_v·D_u = 2·D_e(u)·D_e(v)` ⇒ 代入 `D = 1` ⇒ `= 2` ＝ **D2-A′** ⇒ 经已证的 `:458`/`:494`
⇒ **`pauplinFormula_gap`（`l̂ = l`）** ✓。 -/

/-! ### ★★★ W19 登记：行和引理 —— 六步全已定，卡在最后一步的 rw 匹配（下一轮内联即可）

**目标** ✓：`Σ_y bmeCoeff(topoDist x y)·incidence x y e`
　`= if x ∈ A then (1/2)^{d_u(x)}·D_e(v) else if x ∈ B then (1/2)^{d_v(x)}·D_e(u) else 0` ✓

**已定好的六步** ✓（本轮 5 次迭代逐一确认 ✓）：
1. `rw [Finset.sum_congr rfl (fun y _ => contribution_eq_ite T huv x y)]` ✓ 换成逐点四情形 ✓；
2. `hcompl : z ∉ A → z ∈ B` ✓ —— 用 `rw [T.sideLeaves_compl_adj huv]` 改**目标** ＋ `Finset.mem_compl.mpr` ✓
   （★ 教训：`rw … at h` 在这里无用，因为 `sideLeaves_compl_adj` 出现在**目标**里 ✗）；
3. `by_cases hxA : x ∈ A` ✓ 两情形 ✓（★ 第三情形真空 ✓，由 `hcompl` 覆盖 ✓）；
4. 每情形内先证 `hstep`：把「嵌套两 `ite`」换成 **`if y ∈ B then c·f y else 0`**
   （每支用 `ite_eq_left`/`ite_eq_right` **三连**：外层条件假 ✓、内层条件真/假 ✓、**RHS 那个 `if`** ✓）
   ★★ **注意**：`if_pos`/`if_neg` 已弃用 ✗ ⇒ 一律用 **`ite_eq_left`/`ite_eq_right`** ✓（教训 389）✓；
5. `rw [hstep, sum_ite_mem_eq_sum, Finset.mul_sum, ← sideDoublingSum]` ✓
   （`sum_ite_mem_eq_sum` 是本文件的关键砖 ✓）；
6. 指数用 **`length_pathOf_comm`** ✓ 从「叶在前」换成「基准在前」✓（与 `sideDoublingSum` 一致 ✓）。

**★★★ 唯一未过之处（教训 403）** ✗：第 5 步的 `rw [hstep, …]` 报
「Did not find an occurrence of the pattern `∑ y, if …`」（★ 而 target 里**明明**有同形的和 ✓）。
⇒ ★ **结论**：**`rw [h]` 要求【语法级】匹配** ✗，命名 `have` 的陈述与目标之间哪怕有
beta-还原/隐式参数的细微差别就会失败 ✓。
⇒ ★★ **推荐改法（下一轮）**：**不要**先 `have hstep` 再 `rw` ✗，而是
**直接在目标上用 `Finset.sum_congr`**（即把 `hstep` 的证明体内联进第 5 步 ✓），
或改用 `conv_lhs => rw [hstep]` ✓／`simp only [hstep]` ✓。

-//-! **★★★ W19 登记（续）：行和引理 —— 真因已定位到【语句里的嵌套 `if`】，下一步应拆成两条平铺引理**

**本轮新证据** ✓（三次门，同一症状 ✓）：
* 报错位置**始终是 `:= by` 之后**（`unsolved goals`，把**整个语句**列为目标 ✓），
  且紧接着一行报 **`unexpected identifier; expected command`（指向 `conv_lhs`）** ✓；
* ★ 把语句里的 `else if …` 加**显式括号** ⇒ **症状不变** ✗（列号仅移动 ✓）
  ⇒ **"嵌套 `if` 的括号"不是真因** ✗；
* ★★ 结合"`conv_lhs` 被判为 **identifier** ✗"这一事实 ⇒ 极可能是
  **Lean 把 `:= by` 之后的第一个 tactic 词当成【项的一部分】** ✓
  —— 即**嵌套 `if` 语句把证明体的起点吃掉了** ✗。

**★★★ 下一步（建议写法，避开嵌套 `if`）** ✓：把行和引理**拆成两条平铺引理** ✓（每条只含**一层** `ite`）：

1. `row_sum_eq_of_mem_u`：`x ∈ A ⇒ Σ_y (贡献) = (1/2)^{d_u(x)}·D_e(v)` ✓；
2. `row_sum_eq_of_mem_v`：`x ∈ B ⇒ Σ_y (贡献) = (1/2)^{d_v(x)}·D_e(u)` ✓；
3. （可选）`row_sum_eq`：用 `by_cases hxA` ＋ 上面两条 ＋ `hcompl` 拼成**两层 `ite`** 的版本，
   ★ 但**只在最后一步**才写嵌套 `ite` ✓（此时语句的解析问题可用**显式 `if … then … else (…)`** 或
   **先证平铺版再 `rw`** 规避 ✓）。

**六步证法照旧** ✓（见上一条登记 ✓，其中第 ⑤ 步若 `rw`/`conv_lhs` 仍不通，
改用 **`simp only [hstep]`** 或**直接在平铺引理里做** ✓）。

-//-! **★★★ W19 登记（第三轮）：行和引理的真因已收敛到【一个项】，建议改用 `@[simp]` ＋ `simp only`**

**本轮决定性发现** ✓（三种框架、同一位置、同一症状 ✗）：
我在**平铺**语句（各只含一层 `ite` ✓）下分别用三种写法：
| 写法 | 结果 |
|---|---|
| `conv_lhs => rw [Finset.sum_congr rfl (fun y _ => contribution_eq_ite T huv x y)]` | ✗ 同一症状 |
| `rw [Finset.sum_congr rfl (fun y _ => …)]` | ✗ 同一症状 |
| `refine (Finset.sum_congr rfl (fun y _ => …)).trans ?_` | ✗ 同一症状 |
症状**恒定**：报错在**该行同一列**（`unsolved goals` 把**整个定理目标**列出 ✓），
紧接着一行报 **`unexpected token '<下一个 tactic 词>'; expected command`** ✗。

⇒ ★★★ **结论**：问题**不在**语句的嵌套 `if` ✗（平铺版同样失败 ✓），也**不在** `conv_lhs`/`rw` 本身 ✗，
而**收敛到那个【项】**：`Finset.sum_congr rfl (fun y _ => contribution_eq_ite T huv x y)` ✓
—— 它在**作为 tactic 参数**时无法被 elaboration 消化 ✓（`g` 的推断 / `rfl` 的类型在此上下文里不成立 ✓）。

**★★★ 建议的下一轮路线（避开这个项）** ✓：
1. 给 **`contribution_eq_ite` 加 `@[simp]`** ✓（它无假设、是纯 `=` ✓），
   然后用 **`simp only [contribution_eq_ite]`** 直接化简目标和 ✓ —— **完全不出现 `sum_congr`** ✓；
2. 或者把行和引理的**被积项**改写为**指示函数形式**（用 `sum_ite_mem_eq_sum` 的逆 ✓）
   使 `contribution_eq_ite` 的 RHS 与目标**逐点同形** ⇒ `simp only [contribution_eq_ite]` 即可 ✓；
3. 亦可给 `contribution_eq_ite` 写一个 **`Finset.sum` 版**（即把 `sum_congr` 的结果**预先证成一条引理** ✓），
   再把这条引理的**名字**用于 `rw` ✓（★ 教训 403 的反面用法：**先证成独立引理再 `rw`** ✓）。

-//-! ## 2. 三条基本性质 -/

omit [Fintype X] [DecidableEq X] in
/-- `n_xx = 0`（`x → x` 的唯一路径是平凡 walk）。 -/
theorem topoDist_self (T : Phylogram X) (x : X) : topoDist T x x = 0 := by
  have hnil : pathWalk T x x = SimpleGraph.Walk.nil :=
    ((T.existsUnique_path (T.leaf x) (T.leaf x)).choose_spec.2 SimpleGraph.Walk.nil
      (by simp)).symm
  rw [topoDist, hnil, SimpleGraph.Walk.length_nil]

omit [Fintype X] [DecidableEq X] in
/-- ★ **`n_xy` 对称**（反向走不改变边数）。 -/
theorem topoDist_comm (T : Phylogram X) (x y : X) : topoDist T x y = topoDist T y x := by
  have h : (pathWalk T y x).reverse = pathWalk T x y :=
    (T.existsUnique_path (T.leaf x) (T.leaf y)).choose_spec.2 _
      (SimpleGraph.Walk.IsPath.reverse (pathWalk_isPath T y x))
  rw [topoDist, topoDist, ← h, SimpleGraph.Walk.length_reverse]

omit [Fintype X] [DecidableEq X] in
/-- ★★★ **可加性 ⟺ 关联和**：`d_xy = Σ_e S_xy(e)·w_e`（`wExt` 把非边取 0）。

这就是 `BMELeastSquares.lean:372` 缺口 (1) 的**构造性**内容：库内的「顶点对 ↔ 边」关联
`incidence` 从 `Phylogram` 里造出来了。 -/
theorem dist_eq_sum_incidence (T : Phylogram X) (x y : X) :
    T.dist (T.leaf x) (T.leaf y) = ∑ e : Sym2 T.V, incidence T x y e * T.wExt e := by
  have hl : (pathWalk T x y).edges.Nodup :=
    SimpleGraph.Walk.edges_nodup_of_support_nodup
      ((SimpleGraph.Walk.isPath_def _).mp (pathWalk_isPath T x y))
  have h1 : T.dist (T.leaf x) (T.leaf y) = (pathWalk T x y).edges.toFinset.sum T.wExt := by
    show T.walkDist (pathWalk T x y) = _
    rw [Phylogram.walkDist, List.sum_toFinset T.wExt hl]
  have h2 : (∑ e : Sym2 T.V, incidence T x y e * T.wExt e)
      = (pathWalk T x y).edges.toFinset.sum T.wExt := by
    have h3 : ∀ e : Sym2 T.V, incidence T x y e * T.wExt e
        = if e ∈ (pathWalk T x y).edges.toFinset then T.wExt e else 0 := by
      intro e
      rw [incidence]
      by_cases h : e ∈ (pathWalk T x y).edges
      · simp [h]
      · simp [h]
    rw [Finset.sum_congr rfl fun e _ => h3 e, Finset.sum_ite_mem, Finset.univ_inter]
  rw [h1, h2]

omit [Fintype X] [DecidableEq X] in
/-- ★★★ **关联计数 = 路径边数**：`Σ_e S_xy(e) = n_xy`。

这就是 `BMELeastSquares.lean:372` 缺口 (2) 的**构造性**内容
（「`p_ij` 是拓扑距离」，即 `S_ij(e)` 的计数恰是路径的边数）。 -/
theorem sum_incidence_eq_topoDist (T : Phylogram X) (x y : X) :
    (∑ e : Sym2 T.V, incidence T x y e) = (topoDist T x y : ℝ) := by
  have hl : (pathWalk T x y).edges.Nodup :=
    SimpleGraph.Walk.edges_nodup_of_support_nodup
      ((SimpleGraph.Walk.isPath_def _).mp (pathWalk_isPath T x y))
  have h3 : ∀ e : Sym2 T.V, incidence T x y e
      = if e ∈ (pathWalk T x y).edges.toFinset then (1 : ℝ) else 0 := by
    intro e
    rw [incidence]
    by_cases h : e ∈ (pathWalk T x y).edges
    · simp [h]
    · simp [h]
  rw [Finset.sum_congr rfl fun e _ => h3 e, Finset.sum_ite_mem, Finset.univ_inter,
    Finset.sum_const, nsmul_eq_mul, mul_one, topoDist, List.toFinset_card_of_nodup hl,
    SimpleGraph.Walk.length_edges]

/-! ## 3. `pauplinLength`（式 (4) 的树层字面转写）与 `trueLength` -/

/-- **树的真长**：全部边的权之和。 -/
noncomputable def trueLength (T : Phylogram X) : ℝ := ∑ e : Edge T.toCladogram, T.w e

/-- ★★★ **Pauplin 树长**（DesperGascuel2004 式 (4)，`:394–404`）：

　　`l̂(T) = Σ_{i<j} 2^{1−n_ij} d_ij`

其中 `d_ij = T.dist (leaf i) (leaf j)` 是**库内的树距离**（`Phylo/Core.lean:193`），
`n_ij = topoDist T i j` 是**真路径的边数**（§1）。有序对形式写成 `½ Σ_{i,j}`。 -/
noncomputable def pauplinLength (T : Phylogram X) : ℝ :=
  (1 / 2) * ∑ p ∈ Dissimilarity.plane,
    bmeCoeff (topoDist T p.1 p.2) * T.dist (T.leaf p.1) (T.leaf p.2)

/-- 树距离矩阵是 `Dissimilarity`（对称 + 对角 0）。 -/
noncomputable def treeDissim (T : Phylogram X) : Dissimilarity X where
  val x y := T.dist (T.leaf x) (T.leaf y)
  symm x y := Phylo.TreeDist.dist_comm T (T.leaf x) (T.leaf y)
  diag x := Phylogram.dist_self T (T.leaf x)

omit [DecidableEq X] in
/-- `pauplinLength` 就是 `bmeLength` 在「树距离 + 真路径边数」上的实例（**定义相等**）。 -/
theorem pauplinLength_eq_bmeLength (T : Phylogram X) :
    pauplinLength T = Dissimilarity.bmeLength (fun i j => bmeCoeff (topoDist T i j))
      (treeDissim T) := rfl

/-! ## 4. ★★★ 主定理：缺口精确收缩为「逐边 Pauplin 归一化」 -/

omit [DecidableEq X] in
/-- ★★★ **只要逐边 Pauplin 归一化成立，Pauplin 树长就等于真树长**。

即：若每个顶点对 `e` 满足式 (9)（`:2027`）

　　`Σ_{i,j} 2^{1−n_ij}·S_ij(e) = 2`，

则 `l̂(T) = Σ_e w_e`。证明 = 库内 ★★★ `bme_length_eq_true_length`
（`BMELeastSquares.lean:262`）＋ 本文件刚构造的 `dist_eq_sum_incidence`。

⇒ **一般树的 Pauplin 公式只剩「归一化」一步**（见 `pauplinEdgeCoeff_gap`）。 -/
theorem pauplinLength_eq_sum_wExt_of_edgeCoeff (T : Phylogram X)
    (h : ∀ e : Sym2 T.V,
      ∑ p ∈ Dissimilarity.plane, bmeCoeff (topoDist T p.1 p.2) * incidence T p.1 p.2 e = 2) :
    pauplinLength T = ∑ e : Sym2 T.V, T.wExt e := by
  rw [pauplinLength_eq_bmeLength]
  exact Dissimilarity.bme_length_eq_true_length (treeDissim T) T.wExt (incidence T)
    (topoDist T) (fun i j => dist_eq_sum_incidence T i j) h

omit [Fintype X] [DecidableEq X] in
/-- ★★ `Σ_e wExt e`（全顶点对上的扩展权和）就是真树长 `trueLength`。 -/
theorem sum_wExt_eq_trueLength (T : Phylogram X) :
    (∑ e : Sym2 T.V, T.wExt e) = trueLength T := by
  have h1 : (∑ e : Sym2 T.V, T.wExt e)
      = ∑ e ∈ (Finset.univ.filter fun e => e ∈ T.graph.edgeSet), T.wExt e := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun e _ => ?_
    by_cases h : e ∈ T.graph.edgeSet
    · simp [h]
    · rw [Phylo.TreeDist.wExt_eq_zero T h]
      simp [h]
  rw [h1, trueLength,
    Finset.sum_subtype (s := Finset.univ.filter fun e => e ∈ T.graph.edgeSet)
      (p := fun e => e ∈ T.graph.edgeSet) (f := T.wExt) (fun e => by simp)]
  refine Finset.sum_congr rfl fun a _ => ?_
  exact Phylo.TreeDist.wExt_eq_w T a.2

omit [DecidableEq X] in
/-- ★★★ **Pauplin 公式（带逐边归一化假设的完整形态）**：式 (4) 的 `l̂(T)` 等于真树长。 -/
theorem pauplinLength_eq_trueLength_of_edgeCoeff (T : Phylogram X)
    (h : ∀ e : Sym2 T.V,
      ∑ p ∈ Dissimilarity.plane, bmeCoeff (topoDist T p.1 p.2) * incidence T p.1 p.2 e = 2) :
    pauplinLength T = trueLength T := by
  rw [← sum_wExt_eq_trueLength T]
  exact pauplinLength_eq_sum_wExt_of_edgeCoeff T h

/-! ## 5. 泛性质：非负性与「和为零 ⟺ 所有叶对距离为零」 -/

/-- `bmeCoeff p = 2^{1−p} > 0`。 -/
theorem bmeCoeff_pos (p : ℕ) : 0 < bmeCoeff p := by
  rw [bmeCoeff]
  positivity

omit [DecidableEq X] in
/-- ★ **`pauplinLength` 非负**（系数正、距离非负）。 -/
theorem pauplinLength_nonneg (T : Phylogram X) : 0 ≤ pauplinLength T := by
  rw [pauplinLength]
  refine mul_nonneg (by norm_num) (Finset.sum_nonneg fun p _ => ?_)
  exact mul_nonneg (le_of_lt (bmeCoeff_pos _)) (Phylo.TreeDist.dist_nonneg T _ _)

omit [DecidableEq X] in
/-- ★★ **`pauplinLength = 0` ⟺ 所有叶对距离为 0**
（系数严格正，故「加权和为零」只能来自距离为零）。 -/
theorem pauplinLength_eq_zero_iff (T : Phylogram X) :
    pauplinLength T = 0 ↔ ∀ x y : X, T.dist (T.leaf x) (T.leaf y) = 0 := by
  rw [pauplinLength, mul_eq_zero]
  constructor
  · rintro (h | h)
    · exact absurd h (by norm_num)
    · intro x y
      have hmem : (x, y) ∈ Dissimilarity.plane := by
        rw [Dissimilarity.plane]
        exact Finset.mem_product.mpr ⟨Finset.mem_univ x, Finset.mem_univ y⟩
      have := (Finset.sum_eq_zero_iff_of_nonneg
        (fun p _ => mul_nonneg (le_of_lt (bmeCoeff_pos _)) (Phylo.TreeDist.dist_nonneg T _ _))).mp h
      have hprod := this (x, y) hmem
      rcases mul_eq_zero.mp hprod with h' | h'
      · exact absurd h' (ne_of_gt (bmeCoeff_pos _))
      · exact h'
  · intro h
    right
    refine Finset.sum_eq_zero fun p _ => ?_
    rw [h p.1 p.2, mul_zero]

/-! ## 6. ★B 反例检查：非二叉（星形）树上公式**失效** -/

/-- ★B 辅助量：把一个「有 `k` 个邻居的另一端」的内点上、`k` 条同样长度的路径的
Pauplin 系数写成 `k · 2^{1−2}`（路径边数都是 2 —— 这正是 4 叶星形的形状）。 -/
noncomputable def starCoeff (k : ℕ) : ℝ := (k : ℝ) * bmeCoeff 2

/-- ★B **二叉情形（内点度 3 ⇒ 另有两个邻居）系数恰为 1**。 -/
theorem starCoeff_two : starCoeff 2 = 1 := by
  rw [starCoeff, bmeCoeff]; norm_num

/-- ★B ★★★ **非二叉反例**：4 叶**星形树**（唯一内点度 4 ⇒ 挂边另一端有 3 个邻居）上，
挂边的 Pauplin 系数是 `3/2 ≠ 1`，故式 (4) **失效**：

　　`l̂(T) = ½·(3/2)·Σ_e w_e = (3/4)·l(T) ≠ l(T)`。

⇒ 一般性陈述**必须**带 `T.IsBinary`（式 (4) 的前提）。 -/
theorem starCoeff_three_ne_one : starCoeff 3 ≠ 1 := by
  rw [starCoeff, bmeCoeff]; norm_num

/-- ★B：二叉（`k = 2`）与非二叉（`k = 3`）的系数确实**不同** —— 星形反例不是空真。 -/
theorem starCoeff_two_ne_three : starCoeff 2 ≠ starCoeff 3 := by
  rw [starCoeff_two, starCoeff, bmeCoeff]; norm_num

/-! ## 7. ★C 最小具体例子：3 叶星形（`n = 3`，唯一二叉拓扑） -/

/-- ★C：3 叶真距离按 `w = (1,2,4)` 给出：`d(0,1) = 3`、`d(0,2) = 5`、`d(1,2) = 6`。 -/
def ex3d : Fin 3 → Fin 3 → ℝ
  | 0, 1 => 3 | 1, 0 => 3
  | 0, 2 => 5 | 2, 0 => 5
  | 1, 2 => 6 | 2, 1 => 6
  | _, _ => 0

/-- ★C：3 叶树 `n_ij ≡ 2`（星形；`n = 3` 时唯一的二叉拓扑）。 -/
def ex3n : ℕ := 2

/-- ★C 真树长 `l(T) = 1 + 2 + 4 = 7`。 -/
theorem ex3_total : (1 : ℝ) + 2 + 4 = 7 := by norm_num

/-- ★C 逐边 Pauplin 归一化（挂边，3 叶星形）：`2 · 2^{1−2} = 1`。 -/
theorem ex3_edgeCoeff : starCoeff 2 = 1 := starCoeff_two

/-- ★C ★★★ **端到端（精确算术）**：`Σ_{i<j} 2^{1−n_ij} d_ij`（有序对写法 `½ Σ_{i,j}`）
`= 7 = l(T)`。 -/
theorem ex3_pauplin_arith :
    (1 / 2 : ℝ) * (bmeCoeff ex3n * ex3d 0 1 + bmeCoeff ex3n * ex3d 1 0
      + bmeCoeff ex3n * ex3d 0 2 + bmeCoeff ex3n * ex3d 2 0
      + bmeCoeff ex3n * ex3d 1 2 + bmeCoeff ex3n * ex3d 2 1) = 7 := by
  norm_num [ex3n, bmeCoeff, ex3d]

/-- ★C 反空真：3 叶例的三条事实（真树长、逐边系数、端到端等式）互不空真。 -/
theorem ex3_nonempty :
    (1 : ℝ) + 2 + 4 = 7 ∧ starCoeff 2 = 1 ∧ starCoeff 3 ≠ 1 :=
  ⟨ex3_total, starCoeff_two, starCoeff_three_ne_one⟩

/-! ## 8. 缺口（`def … : Prop`，**不是** `axiom`、**不是** `sorry`） -/

/-- ⬜ ★★★ **缺口 D2-A：逐边 Pauplin 归一化**（式 (9)，`:2027`）—— 公式的**唯一**剩余难点。

**陈述**：对二叉树 `T`（`T.IsBinary`）与每条边 `e`，

　　`Σ_{i,j} 2^{1−n_ij}·S_ij(e) = 2`（有序对写法；无序对即 `= 1`）。

**缺什么**：一条「**子树的倍增恒等式**」：
设边 `e = {u,v}` 把叶集分成 `L_u`、`L_v`，`δ_u(i)` = `u` 到叶 `i` 的边数，则需

　　`Σ_{i∈L_u} 2^{−δ_u(i)} = 1`（`L_v` 同理），

再与「`n_ij = δ_u(i) + 1 + δ_v(j)`」相乘分解即得。该恒等式对**二叉**树归纳成立
（内点度 3 ⇒ 除来路边外恰有 2 个孩子 ⇒ 归约因子 `2·½ = 1`），对非二叉树**不成立**
（★B `starCoeff_three_ne_one`：`3·½ = 3/2`）。

**为什么未证**：库内 `Phylogram` 只有「两点间唯一路径」（`dist`），**没有**
「删去边 `e` 后的某一侧子树」这一算子（`Cladogram.sideLeaves` 只给**叶集**，
不给「以 `u` 为根、去掉 `v` 方向的子树」的**结构归纳**），故该恒等式的归纳
无法落地 ⇒ 落显式缺口。

**非空真**：★C `ex3_edgeCoeff`（3 叶，`k=2` ⇒ 系数 1）、
`BMELeastSquares.lean:314,321`（4 叶，内部边与挂边逐边验证 = 1）、
且 `pauplinLength` 在 4 叶例上确为 `15 = l(T)`（`ex4_bmeLength`）。 -/
def pauplinEdgeCoeff_gap (T : Phylogram X) : Prop :=
  T.IsBinary → ∀ e : Sym2 T.V,
    ∑ p ∈ Dissimilarity.plane, bmeCoeff (topoDist T p.1 p.2) * incidence T p.1 p.2 e = 2

/-- ⬜ ★★★ **缺口 D2-B：Pauplin 公式本体**（式 (4)，`:394–404`）：

　　`T.IsBinary → l̂(T) = Σ_{i,j} 2^{1−n_ij} d_ij = l(T)`。

**注意**：本缺口**已被本文件归约到 D2-A** ——
★★★ `pauplinLength_eq_trueLength_of_edgeCoeff` 说明：只要 D2-A 成立，
D2-B 立即成立（`pauplinFormula_gap_of_edgeCoeff_gap` 就是这次归约的形式化）。
⇒ 这是「**精确剩余**」，不是含糊的「很难」。 -/
def pauplinFormula_gap (T : Phylogram X) : Prop :=
  T.IsBinary → pauplinLength T = trueLength T

omit [DecidableEq X] in
/-- ★★★ **归约**：D2-A ⟹ D2-B（把缺口的两半接起来，说明 D2-A 是**唯一**剩余）。 -/
theorem pauplinFormula_gap_of_edgeCoeff_gap (T : Phylogram X)
    (h : pauplinEdgeCoeff_gap T) : pauplinFormula_gap T :=
  fun hb => pauplinLength_eq_trueLength_of_edgeCoeff T (h hb)

/-! ## 9. ★B 反例检查（W12e）：`pauplinEdgeCoeff_gap` 的量词**为假** -/

omit [Fintype X] [DecidableEq X] in
/-- ★B **非边列的关联恒为 0**：`e` 不是图的边 ⟹ 不在任何路径的边表里 ⟹ 整列为 0。

（用 `SimpleGraph.Walk.edges_subset_edgeSet`：walk 的每条边都是图的边。） -/
theorem incidence_eq_zero_of_not_mem_edgeSet (T : Phylogram X) {e : Sym2 T.V}
    (he : e ∉ T.graph.edgeSet) (x y : X) : incidence T x y e = 0 := by
  rw [incidence]
  by_cases h : e ∈ (pathWalk T x y).edges
  · exact absurd (SimpleGraph.Walk.edges_subset_edgeSet (pathWalk T x y) h) he
  · simp [h]

omit [DecidableEq X] in
/-- ★B 非边 `e` 上 Pauplin 归一化和是 `0`（列恒 0）。 -/
theorem edgeCoeff_sum_eq_zero_of_not_mem_edgeSet (T : Phylogram X) {e : Sym2 T.V}
    (he : e ∉ T.graph.edgeSet) :
    ∑ p ∈ Dissimilarity.plane, bmeCoeff (topoDist T p.1 p.2) * incidence T p.1 p.2 e = 0 := by
  refine Finset.sum_eq_zero fun p _ => ?_
  rw [incidence_eq_zero_of_not_mem_edgeSet T he p.1 p.2, mul_zero]

omit [DecidableEq X] in
/-- ★★★ **反例检查：`∀ e : Sym2 T.V` 这个量词为假** ——
`Sym2 T.V` 含**非边**顶点对（任何 `≥ 4` 叶的树都有），非边的归一化和是 `0 ≠ 2`。
⇒ 缺口（及 `pauplinLength_eq_trueLength_of_edgeCoeff` 的假设）**必须**把量词限制到
`e ∈ T.graph.edgeSet`（或 `Edge T.toCladogram`）；否则前提**不可满足**，
「带假设的定理」成为空真。 -/
theorem not_edgeCoeff_forall_eq_two (T : Phylogram X) {e : Sym2 T.V}
    (he : e ∉ T.graph.edgeSet) :
    ¬ (∀ e' : Sym2 T.V,
      ∑ p ∈ Dissimilarity.plane,
        bmeCoeff (topoDist T p.1 p.2) * incidence T p.1 p.2 e' = 2) := by
  intro h
  have h0 := edgeCoeff_sum_eq_zero_of_not_mem_edgeSet T he
  rw [h e] at h0
  norm_num at h0

omit [DecidableEq X] in
/-- ★★★ **`pauplinEdgeCoeff_gap` 可被证伪**：二叉树只要含非边顶点对即假。 -/
theorem pauplinEdgeCoeff_gap_refuted (T : Phylogram X) (hbin : T.IsBinary) {e : Sym2 T.V}
    (he : e ∉ T.graph.edgeSet) : ¬ pauplinEdgeCoeff_gap T := by
  intro h
  exact not_edgeCoeff_forall_eq_two T he (h hbin)


/-! ## 10. ★★★ 修复形态（W12e2）：把 D2-A 的量词限制到**真边**，并给出**非空真**归约

原 `def pauplinEdgeCoeff_gap`（§8）**逐字保留**，但它已由 ★★★ `pauplinEdgeCoeff_gap_refuted`
证伪：`∀ e : Sym2 T.V` 含**非边**，而非边列恒 `0`（§9 `incidence_eq_zero_of_not_mem_edgeSet`）
⇒ 前提不可满足 ⇒ 以它为假设的 `pauplinLength_eq_trueLength_of_edgeCoeff` 与
`pauplinFormula_gap_of_edgeCoeff_gap` **都是空真**。

本节给出**修复形态**（量词只到 `e ∈ T.graph.edgeSet`）与其**非空真**归约。 -/

/-- ★★★ **修复形态（D2-A′）**：逐边 Pauplin 归一化只在**真边**上要求

　　`Σ_{i,j} 2^{1−n_ij}·S_ij(e) = 2`（式 (9)，DesperGascuel2004 `:2027`；无序对即 `= 1`）。

与 §8 的原缺口**只差量词范围**：`∀ e : Sym2 T.V` ↦ `∀ e ∈ T.graph.edgeSet`。
★B 已核：4 叶二叉树上真边的系数确实是 `2`（★C `ex4S_normalization`；无序对写法的
`ex4_pauplin_internal`/`ex4_pauplin_pendant` 给 `1`），故本形态**可满足、不空真**。 -/
def pauplinEdgeCoeff_gap_correct_shape (T : Phylogram X) : Prop :=
  T.IsBinary → ∀ e ∈ T.graph.edgeSet,
    ∑ p ∈ Dissimilarity.plane, bmeCoeff (topoDist T p.1 p.2) * incidence T p.1 p.2 e = 2

omit [DecidableEq X] in
/-- ★ **原缺口 ⟹ 修复形态**（只是变弱，未偷换命题）：`∀ e` 推出 `∀ e ∈ edgeSet`。 -/
theorem pauplinEdgeCoeff_gap_correct_shape_of_gap (T : Phylogram X)
    (h : pauplinEdgeCoeff_gap T) : pauplinEdgeCoeff_gap_correct_shape T :=
  fun hb e _ => h hb e

omit [DecidableEq X] in
/-- ★★★ **非空真归约（W12e2）**：修复形态（只在真边上归一化）⟹ `l̂(T) = l(T)`。

证明与 ★★★ `pauplinLength_eq_trueLength_of_edgeCoeff` 同构，但归一化假设只在真边上用；
非边的项由 ★B `edgeCoeff_sum_eq_zero_of_not_mem_edgeSet` 与 `wExt_eq_zero` 双双归零，
故**前提可真**（对照：原归约的前提因非边列 `0 ≠ 2` 而不可满足 ⇒ 原归约空真）。 -/
theorem pauplinLength_eq_trueLength_of_edgeCoeff_on_edges (T : Phylogram X)
    (h : ∀ e ∈ T.graph.edgeSet,
      ∑ p ∈ Dissimilarity.plane, bmeCoeff (topoDist T p.1 p.2) * incidence T p.1 p.2 e = 2) :
    pauplinLength T = trueLength T := by
  have hterm : ∀ e : Sym2 T.V,
      (∑ x ∈ Dissimilarity.plane,
          bmeCoeff (topoDist T x.1 x.2) * incidence T x.1 x.2 e) * T.wExt e
        = 2 * T.wExt e := by
    intro e
    by_cases he : e ∈ T.graph.edgeSet
    · rw [h e he]
    · rw [edgeCoeff_sum_eq_zero_of_not_mem_edgeSet T he,
        Phylo.TreeDist.wExt_eq_zero T he, zero_mul, mul_zero]
  have hstep : (∑ x ∈ Dissimilarity.plane,
        bmeCoeff (topoDist T x.1 x.2) * T.dist (T.leaf x.1) (T.leaf x.2))
      = ∑ e : Sym2 T.V,
          (∑ x ∈ Dissimilarity.plane,
            bmeCoeff (topoDist T x.1 x.2) * incidence T x.1 x.2 e) * T.wExt e := by
    have h1 : ∀ x ∈ Dissimilarity.plane,
        bmeCoeff (topoDist T x.1 x.2) * T.dist (T.leaf x.1) (T.leaf x.2)
          = ∑ e : Sym2 T.V,
              T.wExt e * (bmeCoeff (topoDist T x.1 x.2) * incidence T x.1 x.2 e) := by
      intro x _
      rw [dist_eq_sum_incidence T x.1 x.2, Finset.mul_sum]
      exact Finset.sum_congr rfl fun e _ => by ring
    rw [Finset.sum_congr rfl h1, Dissimilarity.wls_fubini]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [← Finset.mul_sum]
    ring
  rw [pauplinLength, hstep, ← sum_wExt_eq_trueLength T,
    Finset.sum_congr rfl fun e _ => hterm e, ← Finset.mul_sum]
  ring

omit [DecidableEq X] in
/-- ★★★ **修复形态 ⟹ Pauplin 公式本体（D2-B）**：`T.IsBinary → l̂(T) = l(T)`。
这是 `pauplinFormula_gap_of_edgeCoeff_gap` 的**非空真**替代。 -/
theorem pauplinFormula_gap_of_correct_shape (T : Phylogram X)
    (h : pauplinEdgeCoeff_gap_correct_shape T) : pauplinFormula_gap T :=
  fun hb => pauplinLength_eq_trueLength_of_edgeCoeff_on_edges T (h hb)

/-! ## 11. ★B ★C 可满足性见证（W12e2）：4 叶二叉树的**真路径关联数据** -/

/-- ★C **4 叶二叉树 `((0,1),(2,3))` 的边集**：`0..3` = 四片挂边，`4` = 内部边。 -/
abbrev ex4E := Fin 5

/-- ★C **4 叶二叉树的路径关联** `S_ij(e)`：`e` 是否在叶 `i`–叶 `j` 的路径上
（挂边：恰有一端是 `i`；内部边：两端分属 `{0,1}` 与 `{2,3}`）。 -/
noncomputable def ex4S (i j : Fin 4) (e : ex4E) : ℝ :=
  if e = 0 then (if (i = 0) ↔ (j = 0) then 0 else 1)
  else if e = 1 then (if (i = 1) ↔ (j = 1) then 0 else 1)
  else if e = 2 then (if (i = 2) ↔ (j = 2) then 0 else 1)
  else if e = 3 then (if (i = 3) ↔ (j = 3) then 0 else 1)
  else (if ((i = 0 ∨ i = 1) ↔ (j = 0 ∨ j = 1)) then 0 else 1)

/-- ★B ★★★ **修复形态的逐边归一化在真 4 叶二叉树上成立**：
`∀ e, Σ_{i,j ∈ plane} 2^{1−p_ij}·S_ij(e) = 2`（式 (9)，`:2027`；有序对写法，无序对即 `1`）。

⇒ 把量词限制到**真边**之后，归一化条件**可满足**（本见证在**关联层**，正是 D2-A 所在的那一层；
与 ★C `ex4_pauplin_internal`（内部边）/ `ex4_pauplin_pendant`（挂边）的 `= 1` 一致）。 -/
theorem ex4S_normalization :
    ∀ e : ex4E, ∑ x ∈ Dissimilarity.plane,
      bmeCoeff (ex4p x.1 x.2) * ex4S x.1 x.2 e = 2 := by
  intro e
  rw [← Dissimilarity.sum_sum_eq_plane (fun i j => bmeCoeff (ex4p i j) * ex4S i j e)]
  fin_cases e <;> (simp only [sum_univ_four_fin, bmeCoeff, ex4p]; norm_num [ex4S])


end Pauplin

end NJ
