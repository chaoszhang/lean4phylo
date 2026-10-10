/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.TreeDistance
import Phylo.BMELeastSquares

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

/-! ## 2. 三条基本性质 -/

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

end Pauplin

end NJ
