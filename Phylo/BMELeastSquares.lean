/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.AttesonRadius
import Mathlib.Combinatorics.SimpleGraph.Star

/-!
# `Phylo.BMELeastSquares` —— BME（平衡最小演化）与加权最小二乘（W11g · D3）

## 文献与逐行依据

`references/md/DesperGascuel2004_BalancedMinimumEvolution.md`
（R. Desper & O. Gascuel, *Theoretical Foundation of the Balanced Minimum Evolution Method of
Phylogenetic Inference and Its Relationship to Weighted Least-Squares Tree Fitting*,
Mol. Biol. Evol. 21(3):587–598 (2004)）。行号指该 md 文件。

* **式 (1)**（`:307–311`）：WLS 树长估计 `l̂(T) = 1ᵗ(SᵗV⁻¹S)⁻¹SᵗV⁻¹δ`，
  `V = diag(v_ij)` 是距离估计的方差矩阵。
* **式 (4)**（`:394–404`）★ **BME 目标函数**：`l̂(T) = Σ_{i,j} 2^{1−p_ij} d_ij`，
  其中 `p_ij` 是 **i 到 j 的拓扑距离**（`T` 上路径的**边数**）。`Σ_{i,j}` 读作
  **无序对** `Σ_{i<j}`（故系数是 `2^{1−p}` 而非 `2^{−p}`）。
* **式 (5)**（`:422–435`）：NNI 的树长差 `l̂(T) − l̂(T') = ¼[(d^T_AB + d^T_CD) − (d^T_AC + d^T_BD)]`。
* **式 (6)**（`:598–604`）★ **WLS 权重**：`Var(d_ij) = k·2^{p_ij}`（`k` 为常数）。
  ⇒ WLS 权重 `w_ij = 1/v_ij ∝ 2^{−p_ij}`。
* **§"From Balanced Tree Length to Minimum Variance…"**（`:580–617`）
  与 **Theorem 1**（`:619–625`）：**在式 (6) 的方差假设 + WLS 框架（协方差为 0）下，
  BME 树长估计是 (1) `T` 的**最小方差**树长估计；(2) **等同于**式 (1) 定义的长度。**
  ← 这就是「**BME 是 WLS 的一个特例**」。
* **Appendix 2**（`:2019–2050`）给出证明的代数骨架：
  任意线性树长估计可写为 `Fᵗδ`（系数 `f_ij`）；一致性（= 无偏，对**任意**边权都等于真树长）
  **当且仅当**
  **式 (9)（`:2027`）`SᵗF = 1`**；WLS 框架下方差为 **式 (10)（`:2035–2042`）**
  `Var(Fᵗδ) = Σ_{i,j} v_ij f_ij²`；在 (9) 的约束下最小化 (10) 即得 WLS 解。
  「(9) 不仅是必要的，也是充分的」（`:2031–2032` 原文）—— 本文件的 ★★★
  `wls_consistent_of_incidence_one` 就是这句话的形式化。
* **Theorem 2**（`:694–699`）**统计一致性**：`Δ = D` 时，`W ≠ T ⇒ l̂(W) > l̂(T) = l(T)`；
  由 `:682–691` 的**连续性论证**：树长是距离矩阵的连续函数 ⟹ `Δ̂` 足够接近 `D` 时
  `T` 仍是唯一最短树 ⟹ 一致性。
* **`:701–703`**：`l̂(T) = l(T)`「simply results from the consistency of equation 1 or equation 4」。

## 本文件证了什么 / 缺什么

✅ **已证（零 `sorry` / 零 `axiom` / 零 `native_decide`）**

* ★★ `bmeCoeff_eq_two_mul_wlsWeight`：**`2^{1−p} = 2 · 2^{−p}`** —— 式 (4) 的系数与式 (6) 的
  WLS 权重**逐点只差常数 `2`**（这就是「BME 是 WLS 的特例」在系数层的精确内容）；
* ★★ `wlsWeight_mul_bmeVariance`：`w · Var(d) = k` —— WLS 权重是方差（式 (6)）的**倒数**；
* ★★ `bmeCoeff_succ` / `wlsWeight_succ`：平衡权的**折半递归**（`:379–384` 的 `d^T_AB` 递归）；
* ★★ `bmeLength_eq_two_mul_wlsWeight`：`Σ_{i<j} 2^{1−p_ij} d_ij = 2 · Σ_{i<j} 2^{−p_ij} d_ij`；
* ★★★ `wls_consistent_of_incidence_one`：**式 (9) `SᵗF = 1` ⟹ 线性估计量一致**
  （`Σ_{i,j} f_ij d_ij = Σ_e l_e`，对**任意**边权 `l`），即 Appendix 2 `:2031–2032` 的「充分性」；
* ★★★ `bme_length_eq_true_length`：**配上 Pauplin 归一化，BME 树长 = 真树长** ——
  Theorem 1 之 (2) 与 Theorem 2 的基例 `l̂(T) = l(T)`（`:623–625`、`:701–703`）；
* ★★ `bme_shortest_tree_stable`：**局部稳定性**（`:682–691`、Theorem 2 的定量形式）——
  真矩阵上 `T` 严格最短 + 各拓扑长度为 `C`-Lipschitz ⟹ 半径 `η` 邻域内 `T` 仍严格最短；
* ★★ `bme_consistency_of_consistent_estimator`：把「距离估计量的相合性」作为假设的**逻辑收口**；
* ★C `Fin 4` 具体例（4 叶树 `((0,1),(2,3))`，挂边 `1,2,3,4`、内部边 `5`）：
  Pauplin 归一化**逐边验证**（`ex4_pauplin_internal` / `ex4_pauplin_pendant`），
  且 `bmeLength = 15 = 真树长`。

⚠️ **缺口（落成 `Prop`）**

* `bme_pauplin_identity_gap`：**一般树的 Pauplin 归一化**（式 (9) 的内容）——
  需要「边 ∈ 路径 `P_ij`」与「路径边数 `p_ij`」的接口（`Phylogram` 只有 `dist`）；
* `bme_statistical_consistency_gap`：**距离估计量的相合性**（模型/概率层，`:653–669`）。

-/

open Finset
open scoped BigOperators

noncomputable section

namespace NJ

/-! ## 1. BME 系数与 WLS 权重（式 (4) 与式 (6)） -/

/-- ★ **BME 系数** `2^{1−p}`（DesperGascuel2004 式 (4)，`:396–404`），
取 `p` = 拓扑距离（路径的边数）。写成 `2 · (½)^p` 以便折半递归与 `ring` 计算。 -/
def bmeCoeff (p : ℕ) : ℝ := 2 * (1 / 2) ^ p

/-- ★ **WLS 权重** `2^{−p}`（由式 (6) `Var(d_ij) = k·2^{p_ij}` 取倒数得到，`:598–604`）。 -/
def wlsWeight (p : ℕ) : ℝ := (1 / 2) ^ p

/-- **式 (6) 的方差**：`Var(d_ij) = k · 2^{p_ij}`（`:602`）。 -/
def bmeVariance (k : ℝ) (p : ℕ) : ℝ := k * (2 : ℝ) ^ p

/-- ★★ **BME 系数 = `2` × WLS 权重**（式 (4) vs 式 (6)）：

`2^{1−p_ij} = 2 · 2^{−p_ij}`。

这就是「**BME 是加权最小二乘的一个特例**」（Theorem 1，`:619–625`）在**系数层**的精确内容：
两者的权重系统只差一个整体常数 `2`（而整体常数不影响拓扑优化）。 -/
theorem bmeCoeff_eq_two_mul_wlsWeight (p : ℕ) : bmeCoeff p = 2 * wlsWeight p := rfl

/-- ★ `2^{−p} = (2^p)⁻¹` —— 与文献记号 `2^{−p_ij}` 对齐。 -/
theorem wlsWeight_eq_inv_pow (p : ℕ) : wlsWeight p = ((2 : ℝ) ^ p)⁻¹ := by
  simp only [wlsWeight, one_div, inv_pow]

/-- ★ `2^{1−p} = 2 · (2^p)⁻¹` —— 式 (4) 的文献记号。 -/
theorem bmeCoeff_eq_two_mul_inv_pow (p : ℕ) : bmeCoeff p = 2 * ((2 : ℝ) ^ p)⁻¹ := by
  rw [bmeCoeff_eq_two_mul_wlsWeight, wlsWeight_eq_inv_pow]

/-- ★★ **WLS 权重是式 (6) 方差的倒数（差常数 `k`）**：`w_ij · Var(d_ij) = k`。 -/
theorem wlsWeight_mul_bmeVariance (p : ℕ) (k : ℝ) :
    wlsWeight p * bmeVariance k p = k := by
  rw [wlsWeight_eq_inv_pow, bmeVariance, mul_comm k ((2 : ℝ) ^ p), ← mul_assoc,
    inv_mul_cancel₀ (pow_ne_zero p (by norm_num)), one_mul]

/-- ★★ **平衡权的折半递归**（DesperGascuel2004 `:379–384` 的
`d^T_AB = (d^T_{AB₁} + d^T_{AB₂})/2` 权重版）：`2^{1−(p+1)} = 2^{1−p} / 2`。 -/
theorem bmeCoeff_succ (p : ℕ) : bmeCoeff (p + 1) = bmeCoeff p / 2 := by
  simp only [bmeCoeff, pow_succ]
  ring

/-- ★★ `2^{−(p+1)} = 2^{−p} / 2`。 -/
theorem wlsWeight_succ (p : ℕ) : wlsWeight (p + 1) = wlsWeight p / 2 := by
  simp only [wlsWeight, pow_succ]
  ring

/-! ## 2. 局部稳定性：Theorem 2 的定量形式（`:682–691`） -/

/-- ★★ **「严格最短」在 `C`-Lipschitz 扰动下稳定**（DesperGascuel2004 `:682–691` 的定量形式，
Theorem 2 `:694–699` 的一致性机制）。

设 `{L W}` 是各拓扑在**真矩阵** `D` 上的树长、`{L' W}` 是在扰动矩阵 `Δ` 上的树长。
若

* `D` 上真树 `T` 严格最短、且余量足够：`L T + 2Cη < L W` 对所有 `W ≠ T`；
* 每个拓扑的树长是 `C`-Lipschitz 的：`|L' W − L W| ≤ Cη`（所有 `W`）；

则 `Δ` 上 `T` **仍**严格最短。

证明是一行线性算术：`L' W ≥ L W − Cη > L T + Cη ≥ L' T`。
（把 `L := L_D`、`L' := L_Δ` 逐点实例化，即得 `:688–691` 的「`Δ̂` 足够接近 `D` 时
`T` 仍是唯一最短树」。） -/
theorem bme_shortest_tree_stable {ι : Type*} (L L' : ι → ℝ) (T : ι) {C η : ℝ}
    (hgap : ∀ W : ι, W ≠ T → L T + 2 * C * η < L W)
    (hT : |L' T - L T| ≤ C * η)
    (hW : ∀ W : ι, W ≠ T → |L' W - L W| ≤ C * η) :
    ∀ W : ι, W ≠ T → L' T < L' W := by
  intro W hWne
  have h1 : L' T - L T ≤ C * η := (abs_le.mp hT).2
  have h2 : -(C * η) ≤ L' W - L W := (abs_le.mp (hW W hWne)).1
  have h3 : L T + 2 * C * η < L W := hgap W hWne
  linarith

/-- ★★ **一致性的逻辑收口**（DesperGascuel2004 `:682–691`）：把「距离估计量的相合性」
（★ `bme_statistical_consistency_gap`）作为假设，配合 ★★ `bme_shortest_tree_stable` 的结论，
即得「**样本量足够大后 BME 一定输出真树**」。 -/
theorem bme_consistency_of_consistent_estimator {ι : Type*} (L : (X → X → ℝ) → ι → ℝ)
    (Δhat : ℕ → X → X → ℝ) (T : ι) (C η : ℝ) (D : X → X → ℝ)
    (hstab : ∀ Δ : X → X → ℝ, (∀ W : ι, W ≠ T → |L Δ W - L D W| ≤ C * η) →
      (∀ W : ι, W ≠ T → L D T + 2 * C * η < L D W) →
      ∀ W : ι, W ≠ T → L Δ T < L Δ W)
    (hgrow : ∃ N : ℕ, ∀ n ≥ N, ∀ W : ι, W ≠ T → |L (Δhat n) W - L D W| ≤ C * η)
    (hgap : ∀ W : ι, W ≠ T → L D T + 2 * C * η < L D W) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ W : ι, W ≠ T → L (Δhat n) T < L (Δhat n) W := by
  obtain ⟨N, hN⟩ := hgrow
  exact ⟨N, fun n hn W hW => hstab (Δhat n) (hN n hn) hgap W hW⟩

/-! ## 3. BME 目标函数（式 (4)） -/

namespace Dissimilarity

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- **平面索引集** `L × L`。把双重求和折成对 `X × X` 的一次求和，
  便于用 `Finset.sum_comm` 交换「标签」与「边」的求和次序。 -/
def plane : Finset (X × X) := (Finset.univ : Finset X).product (Finset.univ : Finset X)

omit [DecidableEq X] in
/-- ★ **双重和 = 平面对和**：`Σ_i Σ_j g i j = Σ_{x ∈ L×L} g x.1 x.2`。
（折成一对是为了让 `Finset.sum_comm` 的高阶匹配落在 Miller pattern `fun x e => …` 上。） -/
theorem sum_sum_eq_plane (g : X → X → ℝ) :
    (∑ i : X, ∑ j : X, g i j) = ∑ x ∈ plane, g x.1 x.2 := by
  have h := Finset.sum_product (s := (Finset.univ : Finset X)) (t := (Finset.univ : Finset X))
    (f := fun x : X × X => g x.1 x.2)
  rw [plane]
  exact h.symm

/-- ★ **BME 树长**（DesperGascuel2004 式 (4)，`:396–404`）：

`l̂(T) = Σ_{i<j} 2^{1−p_ij} d_ij = ½ · Σ_{i,j} 2^{1−p_ij} d_ij`
（`c` 取 `fun i j => bmeCoeff (p i j)`；对角项因 `diag = 0` 自动消失，
故这里无需 `i ≠ j` 的过滤）。 -/
def bmeLength (c : X → X → ℝ) (δ : Dissimilarity X) : ℝ :=
  (1 / 2) * ∑ x ∈ plane, c x.1 x.2 * δ.val x.1 x.2

omit [DecidableEq X] in
/-- ★★ **式 (4) = `2` × （式 (6) 权重的加权和）**：

`Σ_{i<j} 2^{1−p_ij} d_ij = 2 · Σ_{i<j} 2^{−p_ij} d_ij`。

即：**BME 目标是把 WLS 权重 `w_ij = 2^{−p_ij}` 的加权和整体乘 `2`**
（系数层见 ★★ `bmeCoeff_eq_two_mul_wlsWeight`）。 -/
theorem bmeLength_eq_two_mul_wlsWeight (p : X → X → ℕ) (δ : Dissimilarity X) :
    bmeLength (fun i j => bmeCoeff (p i j)) δ
      = 2 * bmeLength (fun i j => wlsWeight (p i j)) δ := by
  have h : (∑ x ∈ plane, bmeCoeff (p x.1 x.2) * δ.val x.1 x.2)
      = 2 * ∑ x ∈ plane, wlsWeight (p x.1 x.2) * δ.val x.1 x.2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [bmeCoeff_eq_two_mul_wlsWeight]
    ring
  simp only [bmeLength, h]
  ring

/-! ## 4. ★★★ 式 (9) `SᵗF = 1` ⟹ 线性估计量一致（Appendix 2 `:2021–2032`） -/

omit [DecidableEq X] in
/-- ★★ **Fubini：交换「标签对」与「边」的求和次序**（`:2021–2032` 的代数核心）。 -/
theorem wls_fubini {E : Type*} [Fintype E] (g : X × X → E → ℝ) :
    (∑ x ∈ plane, ∑ e : E, g x e) = ∑ e : E, ∑ x ∈ plane, g x e :=
  Finset.sum_comm

omit [DecidableEq X] in
/-- ★★★ **式 (9) `SᵗF = 1` ⟹ 一致估计量**（DesperGascuel2004 Appendix 2，`:2021–2032`）。

设 `d_ij = Σ_{e∈E} S_ij(e)·l_e`（`S` = 路径关联、`l` = 边权），
并设线性估计量 `Fᵗδ = Σ_{i,j} f_ij d_ij` 的系数满足

　　**式 (9)**：`∀ e, Σ_{i,j} f_ij·S_ij(e) = 1`

（即 `SᵗF = 1`）。则对**任意**边权 `l`，

　　`Σ_{i,j} f_ij d_ij = Σ_e l_e`

—— 线性估计量**无偏**（`:2024–2027` 的 `FᵗD = FᵗSL = 1ᵗL`），
且 `:2031–2032` 指出这条件不仅必要而且**充分**（本定理即充分性）。

⚠️ 注意求和约定：这里 `Σ_{i,j}` 是**有序对**（含对角），故 Pauplin 归一化在文献的
无序对写法下是 `Σ_{i<j} 2^{1−p_ij} S_ij(e) = 1`，本定理的有序版本对应 `= 2`。 -/
theorem wls_consistent_of_incidence_one {E : Type*} [Fintype E]
    (f : X → X → ℝ) (S : X → X → E → ℝ) (l : E → ℝ)
    (h : ∀ e : E, ∑ x ∈ plane, f x.1 x.2 * S x.1 x.2 e = 1) :
    (∑ x ∈ plane, f x.1 x.2 * (∑ e : E, S x.1 x.2 e * l e)) = ∑ e : E, l e := by
  have h1 : ∀ x ∈ plane, f x.1 x.2 * (∑ e : E, S x.1 x.2 e * l e)
      = ∑ e : E, l e * (f x.1 x.2 * S x.1 x.2 e) := by
    intro x _
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun e _ => by ring
  rw [Finset.sum_congr rfl h1, wls_fubini]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [← Finset.mul_sum, h e, mul_one]

omit [DecidableEq X] in
/-- ★★★ **BME 树长 = 真树长**（Theorem 1 之 (2) 与 Theorem 2 的基例，`:623–625`、`:701–703`）。

设 `δ` 由**路径关联数据**给出：`δ.val i j = Σ_e S_ij(e)·l_e`（可加性），
且 BME 系数满足 **Pauplin 归一化**（式 (9)，`:2027`）：

　　`∀ e, Σ_{i,j} 2^{1−p_ij}·S_ij(e) = 2`

（有序对写法；无序对写法即 `Σ_{i<j} 2^{1−p_ij} S_ij(e) = 1`）。则

　　`l̂(T) = Σ_{i<j} 2^{1−p_ij} d_ij = Σ_e l_e`（真树长）。

这是 ★★★ `wls_consistent_of_incidence_one` 的直接实例，也是把
「BME 是 WLS 的特例」（Theorem 1）提升到**树长估计一致**的关键一步。 -/
theorem bme_length_eq_true_length {E : Type*} [Fintype E] (δ : Dissimilarity X)
    (l : E → ℝ) (S : X → X → E → ℝ) (p : X → X → ℕ)
    (hl : ∀ i j : X, δ.val i j = ∑ e : E, S i j e * l e)
    (hp : ∀ e : E, ∑ x ∈ plane, bmeCoeff (p x.1 x.2) * S x.1 x.2 e = 2) :
    bmeLength (fun i j => bmeCoeff (p i j)) δ = ∑ e : E, l e := by
  have hstep : (∑ x ∈ plane, bmeCoeff (p x.1 x.2) * (∑ e : E, S x.1 x.2 e * l e))
      = ∑ e : E, (∑ x ∈ plane, bmeCoeff (p x.1 x.2) * S x.1 x.2 e) * l e := by
    have h1 : ∀ x ∈ plane, bmeCoeff (p x.1 x.2) * (∑ e : E, S x.1 x.2 e * l e)
        = ∑ e : E, l e * (bmeCoeff (p x.1 x.2) * S x.1 x.2 e) := by
      intro x _
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun e _ => by ring
    rw [Finset.sum_congr rfl h1, wls_fubini]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [← Finset.mul_sum]
    ring
  have hS : (∑ x ∈ plane, bmeCoeff (p x.1 x.2) * δ.val x.1 x.2)
      = ∑ x ∈ plane, bmeCoeff (p x.1 x.2) * (∑ e : E, S x.1 x.2 e * l e) := by
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [hl x.1 x.2]
  have h3 : (∑ e : E, (∑ x ∈ plane, bmeCoeff (p x.1 x.2) * S x.1 x.2 e) * l e)
      = 2 * ∑ e : E, l e := by
    have h4 : ∀ e : E,
        (∑ x ∈ plane, bmeCoeff (p x.1 x.2) * S x.1 x.2 e) * l e = 2 * l e := by
      intro e
      rw [hp e]
    rw [Finset.sum_congr rfl fun e _ => h4 e, Finset.mul_sum]
  simp only [bmeLength]
  rw [hS, hstep, h3]
  ring

/-! ## 5. ★C 最小具体例子：`Fin 4`，树 `((0,1),(2,3))`，挂边 `1,2,3,4`、内部边 `5`

拓扑距离 `p`：同侧 `p(0,1) = p(2,3) = 2`，跨侧 `p = 3`。
真距离矩阵沿用 D1（`Phylo/AttesonRadius.lean`）的 ★C 例子 `exDiss`：
`d(0,1) = 3`、`d(2,3) = 7`、`d(0,2) = 9`、`d(0,3) = 10`、`d(1,2) = 10`、`d(1,3) = 11`。

真树长 `l(T) = 1+2+3+4+5 = 15`。 -/

/-- ★C 的拓扑距离：树 `((0,1),(2,3))` 上路径的边数。 -/
def ex4p : Fin 4 → Fin 4 → ℕ
  | 0, 0 => 0 | 1, 1 => 0 | 2, 2 => 0 | 3, 3 => 0
  | 0, 1 => 2 | 1, 0 => 2
  | 2, 3 => 2 | 3, 2 => 2
  | 0, 2 => 3 | 2, 0 => 3
  | 0, 3 => 3 | 3, 0 => 3
  | 1, 2 => 3 | 2, 1 => 3
  | 1, 3 => 3 | 3, 1 => 3

/-- ★C **Pauplin 归一化（内部边）**：分离 `{0,1} | {2,3}` 的那条边 `e*` 上

`Σ_{i<j : e* ∈ P_ij} 2^{1−p_ij} = 2^{1−3}·4 = 1`（DesperGascuel2004 式 (9)，`:2027`）。 -/
theorem ex4_pauplin_internal :
    bmeCoeff (ex4p 0 2) + bmeCoeff (ex4p 0 3) + bmeCoeff (ex4p 1 2) + bmeCoeff (ex4p 1 3) = 1 := by
  norm_num [bmeCoeff, ex4p]

/-- ★C **Pauplin 归一化（挂边）**：叶 `0` 的挂边上

`Σ_{i<j : e₀ ∈ P_ij} 2^{1−p_ij} = 2^{1−2} + 2^{1−3} + 2^{1−3} = 1`（式 (9)，`:2027`）。 -/
theorem ex4_pauplin_pendant :
    bmeCoeff (ex4p 0 1) + bmeCoeff (ex4p 0 2) + bmeCoeff (ex4p 0 3) = 1 := by
  norm_num [bmeCoeff, ex4p]

/-- ★C ★★★ **端到端**：4 叶具体树上 `l̂(T) = Σ_{i<j} 2^{1−p_ij} d_ij = 15 = 真树长`。 -/
theorem ex4_bmeLength : bmeLength (fun i j => bmeCoeff (ex4p i j)) exDiss = 15 := by
  rw [bmeLength, ← sum_sum_eq_plane (fun i j => bmeCoeff (ex4p i j) * exDiss.val i j)]
  simp only [sum_univ_four_fin, bmeCoeff, ex4p, exDiss, exVal]
  norm_num

/-- ★C：`Σ_{i<j} 2^{−p_ij} d_ij = 15/2` —— 式 (6) 权重下的加权和（BME 目标的一半）。 -/
theorem ex4_wlsWeightedSum : bmeLength (fun i j => wlsWeight (ex4p i j)) exDiss = 15 / 2 := by
  rw [bmeLength, ← sum_sum_eq_plane (fun i j => wlsWeight (ex4p i j) * exDiss.val i j)]
  simp only [sum_univ_four_fin, wlsWeight, ex4p, exDiss, exVal]
  norm_num

/-- 反空真：★C 的两条 Pauplin 归一化 + BME 树长 = 真树长，互不空真。 -/
theorem ex4_nonempty :
    bmeCoeff (ex4p 0 2) + bmeCoeff (ex4p 0 3) + bmeCoeff (ex4p 1 2) + bmeCoeff (ex4p 1 3) = 1 ∧
    bmeLength (fun i j => bmeCoeff (ex4p i j)) exDiss = 15 ∧
    bmeLength (fun i j => bmeCoeff (ex4p i j)) exDiss
      = 2 * bmeLength (fun i j => wlsWeight (ex4p i j)) exDiss :=
  ⟨ex4_pauplin_internal, ex4_bmeLength,
    bmeLength_eq_two_mul_wlsWeight ex4p exDiss⟩

/-! ## 6. 缺口命题（**不是数学缺口，是本库的接口缺口**） -/

/-- ★★★ **缺口 1：一般树的 Pauplin 归一化 + 路径关联表示**（式 (9)，`:2027`）。

**陈述**：对每个可加、正定的相异度 `δ`（⇒ 由 `Phylo/Buneman.lean:563` 的
`ExistsRealizingPhylogram` 存在**正边权**实现树），存在

* 有限边集 `E`、路径关联 `S : X → X → E → ℝ`（`S_ij(e) = 1` 当且仅当 `e ∈ P_ij`）、
* 边权 `l : E → ℝ`、路径边数 `p : X → X → ℕ`，

使

1. `δ.val i j = Σ_e S_ij(e)·l_e`（可加性）；
2. `Σ_e S_ij(e) = p_ij`（关联计数 = 路径边数，即 `p_ij` 是**拓扑距离**）；
3. **Pauplin 归一化**：`∀ e, Σ_{i,j} 2^{1−p_ij}·S_ij(e) = 2`（式 (9)，`:2027`）。

**为什么未证**：本库 `Phylogram` 有 `dist`（`Phylo/Core.lean:193`，唯一路径的边权和）与边权 `w`，
但**没有**「顶点对 ↔ 边」的关联判定 `e ∈ P_ij`，也没有「沿路径计数」的接口，
因此无法把 `S` 与 `p` 从树里构造出来。

**非空真**：★C 的 4 叶树 `((0,1),(2,3))` 给出满足 (3) 的显式数据
（★★ `ex4_pauplin_internal`（内部边）、★★ `ex4_pauplin_pendant`（挂边）），
且 `bmeLength` 恰等于真树长 `15`（★★★ `ex4_bmeLength`）。

**一旦补上**，★ ★★★ `bme_length_eq_true_length` 立即给出一般树的
`l̂(T) = l(T)`（DesperGascuel2004 Theorem 1 之 (2) 与 Theorem 2 的等式半）。

**现状（W25-B 更正）**：上面「为什么未证」一段已**过期**——「树上的 `e ∈ P_ij`」接口
**已**在本库落地（`Cladogram.pathOf` ＋ `Phylogram` 边权），§9 的
★★★ `bme_pauplin_identity_gap_of_normalization` 已把本缺口**归约**到
`BmePauplinNormalization T`（§7）。⇒ 剩下的唯一数学内容 = `BmePauplinNormalization`
（§10 的逐边倍增和 `D_e = 1`），**且它必须配 `T.IsBinary`**：
多分叉时该命题**为假**（4 叶星形树 plane 和 `= 3 ≠ 2`，见 §12）。 -/
def bme_pauplin_identity_gap (δ : Dissimilarity X) : Prop :=
  δ.FourPoint → δ.PositiveDefinite →
    ∃ (E : Type) (_ : Fintype E) (S : X → X → E → ℝ) (l : E → ℝ) (p : X → X → ℕ),
      (∀ i j : X, δ.val i j = ∑ e : E, S i j e * l e) ∧
      (∀ i j : X, i ≠ j → (∑ e : E, S i j e) = (p i j : ℝ)) ∧
      (∀ e : E, ∑ x ∈ plane, bmeCoeff (p x.1 x.2) * S x.1 x.2 e = 2)

/-- ★★★ **缺口 2：距离估计量的相合性（模型/概率层）**（DesperGascuel2004 `:653–669`）。

**陈述**：设 `Δ̂ n` 是样本量 `n` 下的距离估计矩阵，`D` 是真距离矩阵。则

　　`∀ η > 0, ∃ N, ∀ n ≥ N, Σ_{i,j} |Δ̂ n(i,j) − D(i,j)| < η`

（即 `Δ̂ n → D`）。「缺」的是**从序列数据到该收敛**的那一层：
替换模型 + 大数律 + 「成对距离估计量相合」。本库 `Phylo/Stat/` 有测度与律的工具
（`KingmanLaw` 等），但没有把它接到距离估计上。

**一旦补上**，★★ `bme_consistency_of_consistent_estimator` 即给出
「样本量足够后 BME 输出真树」（DesperGascuel2004 `:701–712` 的统计一致性）。

**W25-C 判定**：本 `def` 是**假设槽**（§13）：无假设的 `_holds` **不存在**
（★★★ `bme_statistical_consistency_gap_refuted`）；「相合性 ⟹ 输出真树」的收口见
★★★ `bme_consistency_of_gap`。 -/
def bme_statistical_consistency_gap (Δhat : ℕ → X → X → ℝ) (D : Dissimilarity X) : Prop :=
  ∀ η : ℝ, 0 < η → ∃ N : ℕ, ∀ n ≥ N,
    (∑ x ∈ plane, |Δhat n x.1 x.2 - D.val x.1 x.2|) < η

/-! ## 7. 反空真（W12e）：缺口 2 是「假设槽」而**非**待证命题 -/

omit [DecidableEq X] in
/-- ★C **反空真**：`bme_statistical_consistency_gap Δ̂ D` 的**前提可满足** ——
取 `Δ̂ n ≡ D`（「估计量恰好等于真值」，相合性的退化情形），则对每个 `η > 0`
和差之和是 `0 < η`。⇒ 该 `def` 是**假设槽**（把「估计量相合」登记为条件），
不是一条可无条件证明的命题：换成发散序列 `Δ̂ n := D + 1` 时同一 `Prop` 为假。
真正的数学内容仍是「序列数据 → 相合估计量」那一层（模型/大数律），不在 L2 距离层。 -/
theorem bme_statistical_consistency_gap_satisfiable (D : Dissimilarity X) :
    ∃ Δhat : ℕ → X → X → ℝ, bme_statistical_consistency_gap Δhat D := by
  refine ⟨fun _ x y => D.val x y, ?_⟩
  intro η hη
  refine ⟨0, fun n _ => ?_⟩
  have h0 : (∑ x ∈ plane, |D.val x.1 x.2 - D.val x.1 x.2|) = 0 := by
    refine Finset.sum_eq_zero fun x _ => ?_
    simp
  rw [h0]
  exact hη


/-! ## 7. ★★★ `bme_pauplin_identity_gap` 的归约材料（W12e14）

★D 穷举核查（`scripts/msc/w12e_bme_check.py`：n ≤ 6 的全部标号无根二叉拓扑，拓扑数 1/3/15/105
与 `(2n−5)!!` 吻合 ⇒ 枚举自校验 ✓；**1068 次边检查、0 反例** ✓）表明缺口的 (1)(2)(3) 在
「实现树 + 路径关联」的**规范数据**上成立：

　`E := 树的边`、`S i j e := [e ∈ P_ij]`、`l := 边权`、`p i j := #(P_ij)`。

本节落下两件**不依赖任何未证假设**的事：
* ★★★ `BmePauplinNormalization`：把 (3)（Pauplin 归一化，式 (9)，`:2027`）**抽成一条独立的组合命题**
　——即归约后**剩下的唯一内容**；
* ★★★ `bme_pauplin_identity_gap_of_card_le_one`：**退化情形** `|Fintype.card X| ≤ 1` 直接可证
　（取 `E := ULift Empty` ⟹ (1)(2)(3) 全空真）——故缺口陈述**不必**加 `card X ≠ 1` ✓。

⚠️ **归约定理本身**（`bme_pauplin_identity_gap_of_normalization`，把缺口化归到
`BmePauplinNormalization`）**本轮未落地**：见 W12e14 报告的卡点（`E` 的宇宙提升 ＋
`Finset.sum_subtype` 必须配 `univ.filter (· ∈ edgeSet)` 而非 `univ`）。 -/

/-- ★★★ **Pauplin 归一化（组合命题；DesperGascuel2004 式 (9)，`:2027`）**：对实现树 `T` 的
**每条边** `e`，

　`Σ_{(i,j) ∈ plane} 2^{1−p_ij} · [e ∈ P_ij] = 2`，

其中 `p_ij` 是树上唯一路径 `P_ij` 的**边数**（拓扑距离）、`[·]` 是 0/1 指示。
（`plane` 是**有序对**含对角；对角项 `S i i e = 0`，故等价于无序版 `Σ_{i<j} 2^{1−p_ij} = 1` ✓。）

⚠ **W25-B 忠实性更正**：本条**只对二叉树**（`T.IsBinary`，内部顶点度恰 3，
`Phylo/Core.lean:93`）成立。`no_degree_two`（`Phylo/Core.lean:46`）只排除度 2、
**允许**多分叉；度 `k ≥ 4` 的星形树中心 `c` 上 `D_e(c) = (k−1)/2 ≠ 1` ⇒
每条挂边的 plane 和 `= k−1 ≠ 2`（★ `star4_plane_sum`，§12）。
故 §9 的归约定理**不能**对任意实现树使用，须先有二叉实现（§12 器材 2）。 -/
def BmePauplinNormalization (T : Phylogram X) : Prop :=
  ∀ e : Sym2 T.V, e ∈ T.graph.edgeSet →
    ∑ x ∈ plane, bmeCoeff ((T.pathOf (T.leaf x.1) (T.leaf x.2)).edges.length)
        * (if e ∈ (T.pathOf (T.leaf x.1) (T.leaf x.2)).edges then (1 : ℝ) else 0) = 2

omit [DecidableEq X] in
/-- ★★★ **退化情形**（`Fintype.card X ≤ 1`）：取 `E := ULift Empty` ⟹ 三条合取全为**空真**
——(1) 只剩对角、由 `δ.diag`；(2) 要求 `i ≠ j` 而 `|X| ≤ 1` 时无此对；(3) 对空类型空真。
（`E` 取 `ULift Empty` 是**必要**的：缺口陈述里 `∃ (E : Type)` 的宇宙是待定的，`Empty` 钉死 0 会失败。） -/
theorem bme_pauplin_identity_gap_of_card_le_one (δ : Dissimilarity X)
    (h : Fintype.card X ≤ 1) : bme_pauplin_identity_gap δ := by
  have hsub : ∀ a b : X, a = b := Fintype.card_le_one_iff.mp h
  intro _hFP _hPD
  refine ⟨ULift Empty, inferInstance, (fun _ _ e => nomatch e.down), (fun e => nomatch e.down),
    (fun _ _ => 0), ?_, ?_, ?_⟩
  · intro i j
    rw [hsub i j, δ.diag]
    simp
  · intro i j hij
    exact absurd (hsub i j) hij
  · intro e
    exact nomatch e.down

/-! ## 8. ★★★ 库级**宇宙事实**（W12e16 探针）＋ 边集的 `Fin n` 索引

对 `def bme_pauplin_identity_gap`（`:372`）里 `∃ (E : Type)` 的 `E` 槽做了 5 个探针
（`lake env lean` 实测，`_scripts_tmp/w12e16_probe_univ*.lean`）：

* ✗ `E := Sym2 T.V` —— `type mismatch: T.V has type Type u_2 … but is expected to have type Type`
　⇒ **该槽的期望宇宙是 `Type 0`**（既不是 `X` 的宇宙、也不是待定的元变量）；
* ✗ `E := PLift Empty` —— 同类 `type mismatch`；
* ✓ `E := PUnit`；✓ `E := ULift.{0, 0} Empty`；✓ `E := Fin 3`（三者都是 `Type 0`）。

⇒ **结论（可复用的库级事实）**：该 `E` 只能是 **`Type 0`** 的类型；
「树的边子类型」`{e : Sym2 T.V // e ∈ T.graph.edgeSet}` 住在 `T.V` 的宇宙 `Type u_2`，
**不能**直接充当 `E` ✗ —— 必须经 `Fin n`（或 `ULift.{0,0}`）**搬运**。
这正是 W12e14/W12e15 里 (c) 归约的真正障碍（当时误以为 `ULift` 能修，实测**不能** ✗）。

※ 另一条实测事实（命名空间）：在 `namespace NJ / Dissimilarity` 内引用 `Phylo.AttesonRadius`
的引理必须写**全名** `Cladogram.pathOf_edges_nodup`（不带限定符会报 `Unknown identifier`）。 -/

omit [Fintype X] [DecidableEq X] in
/-- ★★★ **边集可被 `Fin n` 索引**（`n` = 边数）：这是 (c) 归约在「宇宙 0」约束下的**第一步** ——
把 `{e : Sym2 T.V // e ∈ T.graph.edgeSet}` 沿等价搬到 `Fin n : Type 0`，之后
`S`/`l`/`p` 都定义在 `Fin n` 上（用 `Equiv.sum_comp`/`Finset.sum_equiv` 搬运和）。
⚠️ 注意：本定理**不是**缺口本身，也不声称缺口已被归约。 -/
theorem exists_equiv_fin_edgeSet (T : Phylogram X) :
    ∃ n : ℕ, Nonempty ({e : Sym2 T.V // e ∈ T.graph.edgeSet} ≃ Fin n) := by
  classical
  exact ⟨_, ⟨Fintype.equivFin _⟩⟩

/-! ## 9. ★★★ 归约（W12e17）：缺口 ⟸「实现树 + Pauplin 归一化」

`def bme_pauplin_identity_gap`（`:372`）的**结论**由两件假设推出：

* ★★ `hreal : ∀ i j, T.dist (T.leaf i) (T.leaf j) = δ.val i j`（`T` 实现 `δ`）；
* ★★★ `hnorm : BmePauplinNormalization T`（§7 的 Pauplin 归一化，式 (9)）。

构造（**宇宙合规**：§8 探针已证 `E` 必须是 `Type 0`）：取 §8 的
`idx : {e // e ∈ T.graph.edgeSet} ≃ Fin n` ⇒ **`E := Fin n`**（`Type 0` ✓），

* `S i j k := [(idx.symm k).1 ∈ P_ij]`（0/1 关联）、`l k := T.wExt (idx.symm k).1`、`p i j := #(P_ij)`；

再用 `Equiv.sum_comp` ＋ `Finset.sum_subtype` ＋ `Finset.sum_filter` 把 `Fin n` 上的和搬回
「全 `Sym2 T.V` 上的和」（非边项由 `hp`/`he` 归零 ⇒ 无需 `wExt_eq_zero` 也成立 ✓）：

* (1) 可加性：`Cladogram.dist_eq_sum_pathOf`（§15）＋ 逐项 `by_cases`；
* (2) 指示和 = 路径边数：`hcard`（`List.toFinset_card_of_nodup` ＋ `Cladogram.pathOf_edges_nodup`）
　＋ ℕ 版 `Finset.card_filter` ＋ `exact_mod_cast`；
* (3) 归一化：直接由 `hnorm`。

⇒ 缺口**归约**到 `BmePauplinNormalization T`（唯一剩下的组合内容 = (d)，见 §7）。
⚠️ 本定理是**条件形态**（命名如实 ✓，不叫 `…_proof`）：它**没有**证明 (d)，也**不**声称缺口已证。 -/

omit [DecidableEq X] in
/-- ★★★★ **BME 分解（归一化形态）**：`T` 实现 `δ`（`T.dist = δ.val`）且 `T` 满足
Pauplin 归一化 ⟹ 存在分解数据 `(E, S, l, p)` 使三条合取成立（可加性 / 指示和 = `p` /
Pauplin 归一化）—— 即 `def bme_pauplin_identity_gap` 的**结论内容**，与它的
`FourPoint` / `PositiveDefinite` 前提**无关**。

**W32 抽取**：本定理的证明体**原样**来自 `bme_pauplin_identity_gap_of_normalization`；
原证明体开头的 `intro _hFP _hPD` 把两个前提**双双丢弃** ⇒ 「归一化 ⟹ 分解」这一步
既不需要 `FourPoint` 也不需要 `PositiveDefinite`（`FourPoint` 只用于「产生实现树」，
见 `exists_binary_realizingPhylogram`，`Phylo/BinaryRealization.lean:240`）。
⇒ **无 `PositiveDefinite` 的更强形态**见 `exists_bmeDecomposition_of_fourPoint`
（`Phylo/BinaryRealization.lean`，仅需 `2 ≤ card X` 与 `FourPoint`）。
构造：取 `E := Fin n`（`n` = 边数，`Type 0` ✓，见 §8 宇宙事实）、
`S i j k := [(idx.symm k).1 ∈ P_ij]`、`l k := T.wExt (idx.symm k).1`、`p i j := #(P_ij)`。
★ 命名**不含** `gap`/`Gap`：本定理不是缺口，而是缺口的结论（旧 `def` 逐字未动，★C）。 -/
theorem exists_bmeDecomposition_of_normalization (δ : Dissimilarity X) (T : Phylogram X)
    (hreal : ∀ i j : X, T.dist (T.leaf i) (T.leaf j) = δ.val i j)
    (hnorm : BmePauplinNormalization T) :
    ∃ (E : Type) (_ : Fintype E) (S : X → X → E → ℝ) (l : E → ℝ) (p : X → X → ℕ),
      (∀ i j : X, δ.val i j = ∑ e : E, S i j e * l e) ∧
      (∀ i j : X, i ≠ j → (∑ e : E, S i j e) = (p i j : ℝ)) ∧
      (∀ e : E, ∑ x ∈ plane, bmeCoeff (p x.1 x.2) * S x.1 x.2 e = 2) := by
  classical
  obtain ⟨n, ⟨idx⟩⟩ := exists_equiv_fin_edgeSet T
  refine ⟨Fin n, inferInstance,
    (fun i j (k : Fin n) =>
      if (idx.symm k).1 ∈ (T.pathOf (T.leaf i) (T.leaf j)).edges then (1 : ℝ) else 0),
    (fun k : Fin n => T.wExt (idx.symm k).1),
    (fun i j => (T.pathOf (T.leaf i) (T.leaf j)).edges.length), ?_, ?_, ?_⟩
  · -- (1) 可加性
    intro i j
    rw [← hreal i j, Cladogram.dist_eq_sum_pathOf T (T.leaf i) (T.leaf j)]
    rw [Equiv.sum_comp idx.symm
      (fun s : {e : Sym2 T.V // e ∈ T.graph.edgeSet} =>
        (if s.1 ∈ (T.pathOf (T.leaf i) (T.leaf j)).edges then (1 : ℝ) else 0) * T.wExt s.1)]
    rw [← Finset.sum_subtype
      (s := (Finset.univ.filter fun e : Sym2 T.V => e ∈ T.graph.edgeSet))
      (p := fun e : Sym2 T.V => e ∈ T.graph.edgeSet) (h := fun e => by simp)
      (f := fun s : Sym2 T.V =>
        (if s ∈ (T.pathOf (T.leaf i) (T.leaf j)).edges then (1 : ℝ) else 0) * T.wExt s)]
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun e _ => ?_
    by_cases he : e ∈ T.graph.edgeSet
    · by_cases hp : e ∈ (T.pathOf (T.leaf i) (T.leaf j)).edges <;> simp [he, hp]
    · have hp : e ∉ (T.pathOf (T.leaf i) (T.leaf j)).edges := fun h =>
        he (SimpleGraph.Walk.edges_subset_edgeSet _ h)
      simp [he, hp]
  · -- (2) 指示和 = 路径边数
    intro i j _
    have hcard : (Finset.univ.filter
          (fun e : Sym2 T.V => e ∈ (T.pathOf (T.leaf i) (T.leaf j)).edges)).card
        = (T.pathOf (T.leaf i) (T.leaf j)).edges.length := by
      rw [show (Finset.univ.filter
            (fun e : Sym2 T.V => e ∈ (T.pathOf (T.leaf i) (T.leaf j)).edges))
          = (T.pathOf (T.leaf i) (T.leaf j)).edges.toFinset from ?_]
      · exact List.toFinset_card_of_nodup
          (Cladogram.pathOf_edges_nodup T.toCladogram (T.leaf i) (T.leaf j))
      · ext e
        simp [List.mem_toFinset]
    have hsumNat : (∑ e : Sym2 T.V,
          (if e ∈ (T.pathOf (T.leaf i) (T.leaf j)).edges then (1 : ℕ) else 0))
        = (T.pathOf (T.leaf i) (T.leaf j)).edges.length := by
      rw [← hcard, Finset.card_filter]
    have hsumR : (∑ e : Sym2 T.V,
          (if e ∈ (T.pathOf (T.leaf i) (T.leaf j)).edges then (1 : ℝ) else 0))
        = ((T.pathOf (T.leaf i) (T.leaf j)).edges.length : ℝ) := by
      exact_mod_cast hsumNat
    rw [Equiv.sum_comp idx.symm
      (fun s : {e : Sym2 T.V // e ∈ T.graph.edgeSet} =>
        if s.1 ∈ (T.pathOf (T.leaf i) (T.leaf j)).edges then (1 : ℝ) else 0)]
    rw [← Finset.sum_subtype
      (s := (Finset.univ.filter fun e : Sym2 T.V => e ∈ T.graph.edgeSet))
      (p := fun e : Sym2 T.V => e ∈ T.graph.edgeSet) (h := fun e => by simp)
      (f := fun s : Sym2 T.V =>
        if s ∈ (T.pathOf (T.leaf i) (T.leaf j)).edges then (1 : ℝ) else 0)]
    rw [Finset.sum_filter]
    refine Eq.trans (Finset.sum_congr rfl fun e _ => ?_) hsumR
    by_cases he : e ∈ T.graph.edgeSet
    · by_cases hp : e ∈ (T.pathOf (T.leaf i) (T.leaf j)).edges <;> simp [he, hp]
    · have hp : e ∉ (T.pathOf (T.leaf i) (T.leaf j)).edges := fun h =>
        he (SimpleGraph.Walk.edges_subset_edgeSet _ h)
      simp [he, hp]
  · -- (3) 归一化
    intro k
    exact hnorm (idx.symm k).1 (idx.symm k).2

omit [DecidableEq X] in
/-- ★★★ **归约**：`δ` 由 `T` 实现（`T.dist = δ.val`）且 `T` 满足 Pauplin 归一化
⟹ `bme_pauplin_identity_gap δ`。取 `E := Fin n`（`n` = 边数，`Type 0` ✓，见 §8 宇宙事实）、
`S i j k := [(idx.symm k).1 ∈ P_ij]`、`l k := T.wExt (idx.symm k).1`、`p i j := #(P_ij)`。

**W32**：证明体已抽成 ★★★★ `exists_bmeDecomposition_of_normalization`（上一条）；
本定理现在只剩 `intro _ _; exact …` —— 两个前提（`FourPoint`、`PositiveDefinite`）**仍被丢弃**。 -/
theorem bme_pauplin_identity_gap_of_normalization (δ : Dissimilarity X) (T : Phylogram X)
    (hreal : ∀ i j : X, T.dist (T.leaf i) (T.leaf j) = δ.val i j)
    (hnorm : BmePauplinNormalization T) :
    bme_pauplin_identity_gap δ := by
  intro _ _
  exact exists_bmeDecomposition_of_normalization δ T hreal hnorm

/-! ## 10. ★★★ 子树倍增和接口（W12e18）：(d) 的等价形式

`BmePauplinNormalization`（§7 = (d)）的**逐边**和

　`Σ_{(i,j) ∈ plane} 2^{1−p_ij}·[e ∈ P_ij]`

在交叉对 `i ∈ A`、`j ∈ B`（`e = s(a,b)` 的两侧）上满足 `p_ij = d_a(i) + 1 + d_b(j)`，故
`2^{1−p_ij} = 2^{−d_a(i)}·2^{−d_b(j)}`；`plane` 是**有序**对 ⇒ 该和 `= 2·D_e(a)·D_e(b)`，其中

　`D_e(u) := Σ_{x ∈ L_u(e)} (1/2)^{d_u(x)}`（`d_u(x)` = `u` 到叶 `x` 的路径边数）。

⇒ **(d) ⟺ 每条边两侧的倍增和都等于 1**（这就是接下来要证的组合命题）。

⚠ **W25-B 忠实性更正**：`D_e(u) = 1` **要求二叉**（内部顶点度恰 3）。星形树中心 `c`（度 `k`）
上 `D_e(c) = (k−1)/2`，plane 和 `= 2·1·(k−1)/2 = k−1`：`k = 3`（二叉）⇒ `2` ✓，
`k = 4`（多分叉）⇒ `3 ≠ 2` ✗（★ `star4_plane_sum`，§12）。下面的 ★D 穷举由**叶插入法**
生成，**只含二叉拓扑**，从未测过多分叉 ⇒ 本轮把 (d) 的正确形态钉为
`T.IsBinary → D_e = 1`。

★D 穷举证据（`scripts/msc/w12e_bme_check.py`，n ≤ 6 全部标号无根二叉拓扑、**1068 次边检查**、
精确有理数）：对每条边的**两侧**都有 `D = 1`，**0 反例** ✓（该检查本轮新增，脚本 md5 `e8f59914…` ✓）。

本节先落下这个**接口**（定义 ＋ 非负性）；恒等式 `D = 1` 本身（= (d) 的本体）**未证** ✗，
需对树做结构化归纳（「子树内叶到根的路径边数和」的分层），见 W12e18 报告。 -/

/-- ★★★ **子树倍增和（(d) 的核心量）**：从 `u` 出发，沿 `u` 侧各叶的路径边数 `d_u(x)` 的
`2^{−d_u(x)}` 加权和：

　`D_e(u) := Σ_{x ∈ L_u(e)} (1/2)^{d_u(x)}`。

★D 穷举（`scripts/msc/w12e_bme_check.py`：n ≤ 6 全部标号无根二叉拓扑、**1068 次边检查**）实测：
对**每条边** `e = s(a,b)` 的两侧都有 `D_e(a) = 1`、`D_e(b) = 1`（**0 反例** ✓）。
⚠ 该枚举用**叶插入法**生成，**只覆盖二叉拓扑** ⇒ 这 1068 次检查**不含**多分叉的证据；
多分叉时 `D_e(u) = (deg(u)−1)/2 ≠ 1`（`Phylo/Core.lean:46` 只排除度 2），见 §12。
而 (d) 的 `plane` 和等于 `2·D_e(a)·D_e(b)`（交叉对 `i ∈ A, j ∈ B` 满足
`2^{1−p_ij} = 2^{−d_a(i)}·2^{−d_b(j)}` ✓）⇒

　**(d) ⟺ 每条边两侧的倍增和都等于 1** —— 这就是把 `BmePauplinNormalization` 归约到的
「子树倍增和恒等式」（下一步的证明对象）。 -/
noncomputable def sideDoublingSum (T : Cladogram X) (e : Sym2 T.V) (u : T.V) : ℝ :=
  ∑ x ∈ T.sideLeaves e u, (1 / 2) ^ ((T.pathOf u (T.leaf x)).edges.length)

omit [DecidableEq X] in
/-- ★★ **倍增和非负**。 -/
theorem sideDoublingSum_nonneg (T : Cladogram X) (e : Sym2 T.V) (u : T.V) :
    0 ≤ sideDoublingSum T e u := by
  refine Finset.sum_nonneg fun x _ => ?_
  exact pow_nonneg (by norm_num) _

/-! ## 11. ★★★ (d) 的**叶侧实例**（W12e19）：挂边上的一侧倍增和 = 1

(d)（§7 `BmePauplinNormalization`）在 §10 被归约为「每条边**两侧**的倍增和 `D_e = 1`」。
本节落下其中**最便宜的一半**：

* ★★ `pathOf_self_edges_eq_zero`：`(T.pathOf u u).edges.length = 0`（由路径唯一性 `pathOf u u = nil`）；
* ★★★ `sideDoublingSum_leaf_edge`：**叶 `x` 在其挂边 `s(T.leaf x, b)` 上的那一侧**
　`L_{leaf x}(s(x,b)) = {x}`（★★ `sideLeaves_leaf_edge`）且 `d = 0` ⇒ **`D = (1/2)^0 = 1`** ✓。

⚠️ 边界如实：本节**只**证了挂边的**叶侧**；(d) 本体（**每条边的两侧**都 `= 1`，等价于 §10 的
「子树倍增和恒等式」）**仍未证** ✗ —— 需要先落**递归恒等式**
`D_e(u) = Σ_{v ∈ N(u) ∖ (朝 e 的那一支)} (1/2)·D_{s(u,v)}(v)`
（把 `sideLeaves e u` 按 `u` 的邻接分支**分划**；库内有 `sideVertices`/`SideSubtree` 的分层 ✓
但分支分划的 Finset 记账未完成 ✗），见 W12e19 报告。 -/

omit [Fintype X] [DecidableEq X] in
/-- ★★ **到自身的唯一路径没有边**（`pathOf u u = nil`，由路径唯一性）。 -/
theorem pathOf_self_edges_eq_zero (T : Cladogram X) (u : T.V) :
    (T.pathOf u u).edges.length = 0 := by
  have hnil : T.pathOf u u = SimpleGraph.Walk.nil :=
    ((T.existsUnique_path u u).choose_spec.2 SimpleGraph.Walk.nil
      SimpleGraph.Walk.IsPath.nil).symm
  rw [hnil]
  simp

/-- ★★★ **(d) 在挂边上的一侧实例**：叶 `x` 与其挂边 `s(T.leaf x, b)`（`Adj`）——
`L_{leaf x}(s(x,b)) = {x}` 且到自身的路径无`边` ⇒ `D = (1/2)^0 = 1` ✓
（这正是 (d)「每条边两侧的倍增和 = 1」中**叶侧**那一半）。 -/
theorem sideDoublingSum_leaf_edge (T : Cladogram X) {b : T.V} {x : X}
    (h : T.graph.Adj (T.leaf x) b) :
    sideDoublingSum T s(T.leaf x, b) (T.leaf x) = 1 := by
  rw [sideDoublingSum, Cladogram.sideLeaves_leaf_edge T h, Finset.sum_singleton,
    pathOf_self_edges_eq_zero T (T.leaf x)]
  simp

/-! ## 12. ⚠ W25-B 忠实性更正：`BmePauplinNormalization` 缺 `T.IsBinary`（缺口本体仍未证）

§7 把缺口归约到 `BmePauplinNormalization T`（= (d)），§10 再把它归约为「每条边两侧的
倍增和 `D_e(u) = 1`」。**本轮（W25-B）发现：这条归约目标按现状为假。**

* `e = s(a,b)`、`i ∈ A`、`j ∈ B` ⇒ `p_ij = d_a(i) + 1 + d_b(j)`
  ⇒ plane 和 `= 2·D_e(a)·D_e(b)`（只用 `pathOf` 的边可分解性，**不需要**二叉假设）；
* 若 `u` 的每个「非 e 向」分支侧都满足 `D = 1`，则
  `D_e(u) = (分支数)/2 = (deg(u)−1)/2` —— 这是**递归**形态（§11 已注：分支分划的
  Finset 记账未完成 ✗）。`(deg−1)/2 = 1` **当且仅当** `deg = 3`（二叉，
  `Phylo/Core.lean:93` 的 `IsBinary`）。

⭐ **一叶知秋的算术反例（已机器核查）**：`k` 叶**星形**树（唯一内部顶点度 `= k`、`p_ij = 2`）
的每条挂边上，plane 和 `= 2(k−1)·2^{1−2} = k−1`：

* `k = 3`（`deg = 3`，**二叉**）⇒ `= 2` ✓ —— §7 的命题**恰好**在二叉树上成立；
* `k = 4`（`deg = 4`，**多分叉**）⇒ `= 3 ≠ 2` ✗（★★ `star4_plane_sum`、
  ★★ `star4_plane_sum_ne_two`）。

`Cladogram` 的 `no_degree_two`（`Phylo/Core.lean:46`）**只排除度 2**，度 4 的星形树是**合法**的
`Cladogram (Fin 4)` ⇒ 对这样的 `T`，`BmePauplinNormalization T` 为**假**，
§9 的 `bme_pauplin_identity_gap_of_normalization` **不可**对任意实现树实例化。

⇒ **缺的具名器材（下一步，按成本排序）**：

1. `BmePauplinNormalization` **加 `T.IsBinary` 前提**（`Phylo/Core.lean:93`）——一句话修正；
2. **二叉实现**：`δ.ExistsRealizingPhylogram`（`Phylo/Buneman.lean:563` 的
   `exists_phylogram_of_fourPoint`，`:601`）产出的树是否二叉**未被告知**；若不是，需要
   **零长边细化**（把度 `≥ 4` 顶点拆成二叉，`w = 0` 仍满足 `w_nonneg`）——
   即缺引理 `exists_binary_realizing_phylogram`（库内**无** ✗）；
3. **分支分划递归** `D_e(u) = Σ_{v ∈ N(u) ∖ e-向} (1/2)·D_{s(u,v)}(v)`
   （Finset 记账：用 `T.graph.neighborFinset u` 上的 `biUnion` 分划 `sideLeaves e u`，
   再用 `sideLeafCount_lt_card_of_adj`（`Phylo/AttesonRadius.lean:1286`）做**良基归纳**
   ⇒ 二叉树上 `D_e(u) = 1`）。

⚠ 本节**不**声称缺口已证或已证伪：`bme_pauplin_identity_gap` 本体（以及证伪所需的
「星形树是合法 `Cladogram` 实例」的形式化）本轮**未**落地。 -/

omit [Fintype X] [DecidableEq X] in
/-- ★★ **3 叶星形**（中心度 3 = 二叉）每条挂边的 plane 和 `= 2·(3−1)·2^{1−2} = 2` ✓
—— §7 的 Pauplin 归一化在二叉树上成立。 -/
theorem star3_plane_sum : (2 * (3 - 1) : ℝ) * bmeCoeff 2 = 2 := by
  norm_num [bmeCoeff]

omit [Fintype X] [DecidableEq X] in
/-- ★★ **4 叶星形**（中心度 4 = 多分叉）每条挂边的 plane 和 `= 2·(4−1)·2^{1−2} = 3` ✗
—— 多分叉树上 `BmePauplinNormalization` 为假（§12 的忠实性更正）。 -/
theorem star4_plane_sum : (2 * (4 - 1) : ℝ) * bmeCoeff 2 = 3 := by
  norm_num [bmeCoeff]

omit [Fintype X] [DecidableEq X] in
/-- ★★ **反例判定**：4 叶星形的 plane 和 `3 ≠ 2` ⇒ 该树上 §7 的 `BmePauplinNormalization`
不可能成立（而这样的星形树是**合法** `Cladogram`：`no_degree_two` 只排除度 2）。 -/
theorem star4_plane_sum_ne_two : (2 * (4 - 1) : ℝ) * bmeCoeff 2 ≠ 2 := by
  norm_num [bmeCoeff]

/-! ## 13. ★★★ 缺口 2 的**判定**（W25-C）：`bme_statistical_consistency_gap` 是**假设槽**而非定理

§6 的 `bme_statistical_consistency_gap`（`:402`）陈述「样本距离序列 `Δ̂ n` 依 plane ℓ¹ 范数
收敛到真矩阵 `D`」。本节把它的**逻辑地位**钉死，并给出它作为**假设**时的收口 —— 三件独立材料：

1. ★★★ `bme_statistical_consistency_gap_refuted`：**判定 = 证伪（全称闭包为假）**。
   取 `Δ̂ n ≡ exPert` —— `Fin 4` 上**合法**的相异度（真矩阵 ＋ 有界扰动 `‖ε‖_∞ = 2/5`，
   `Phylo/AttesonRadius.lean:650–670`）—— 时 plane ℓ¹ 和恒为 `14/5`，在 `η = 1` 处不成立。
   与 §7 ★C `bme_statistical_consistency_gap_satisfiable`（`:414`，取 `Δ̂ ≡ D`）**合起来**：
   该 `def` 是**真谓词**（既可满足、又可假）⇒ **不存在**无假设的 `_holds`。
   ※ 与文献一致：DesperGascuel2004 `:656–659` 原文即「**Assuming that** `Δ̂` is a consistent
   estimate of `D`, …」—— 相合性在文献里**也是假设**；`:660–662` 才是由它推出的结论。
2. ★★ `bmeLength_abs_sub_le`：BME 树长（`:188`）在 plane ℓ¹ 范数下是 `C/2`-Lipschitz（`|c| ≤ C`）
   —— 即 `:682–691` 的「树长是距离矩阵的连续函数」的**定量形式**；★ `abs_bmeCoeff_le_two`
   给出 `c := bmeCoeff ∘ p` 时 `C = 2` 可用（`0 < bmeCoeff p ≤ 2`）。
3. ★★★ `bme_consistency_of_gap`（抽象系数）／★★★ `bme_consistency_of_gap_bmeCoeff`（`bmeCoeff` 实例）：
   缺口（作为**假设**）＋ (2) ＋「真矩阵上 `T` 严格最短、且留出余量」⟹
   **样本量足够后 `T` 仍是唯一最短树**。这正是 `:660–662` 的「as soon as `Δ̂` is sufficiently
   close to `D`」；同时把 `bme_consistency_of_consistent_estimator`（`:152`）里的 `hgrow`
   （**树长层**的接近性）变成缺口（**距离层** ℓ¹ 接近性）的**推论** —— 两层之间的桥就是 (2)。

**与库内先例同构**（「确定性收敛谓词证不出来」在本库已是第三次出现，模板可复用）：
`Phylo/Stat/Parsimony.lean` 把「ISM 位点采样 ＋ 大数律」公理化成 `SiteSampling.converges`，
其确定性形状「**没有概率空间，所以它证不出来**」（`Phylo/Stat/SiteSamplingAE.lean:14`）。
那里的正解是**两步**：先「真律固定版 = 假设槽 ＋ 算法稳定性 ⟹ 一致性定理」
（`SiteSamplingFixed`，`:247–253`；`parsimony_statisticallyConsistent_fixed`，`:288–304`），
再**独立地**用 SLLN 给 a.e. 版（`exists_siteSamplingFixed_ae`，`:269–284`；
`parsimony_statisticallyConsistent_ae`，`:311–328`）。本节交付的是 **BME 版的「真律固定」定理**
(2)(3) ＋ 缺口 (1) 的**判定**；BME 版的 a.e. 形态仍缺下列**具名**器材（库内**无** ✗）：

* `exists_bme_distance_estimator_ae`：由**替换模型 ＋ 位点 iid ＋ SLLN**（库内已有
  `strong_law_ae`，`Phylo/Stat/EmpiricalConvergence.lean:36`）构造 `Δ̂ n` 并证
  「成对距离估计量相合」—— 形态须为 `∀ᵐ ω, ∀ η > 0, ∃ N, ∀ n ≥ N, …`，库内**未接** ✗；
* `ae_gap_to_deterministic_gap`（**形态桥**）：概率层只能给 `∀ᵐ ω, …`，而 §6 的 `def` 是
  **确定性** `∀ η > 0, ∃ N, ∀ n ≥ N, …`；把 a.e. 一致性转成 §6 形态（Egorov／子列抽取）库内**无** ✗。
  （先例的同一诚实边界：`SiteSamplingAE.lean:52–58`；那里的 a.e. 定理是**另立**的
  `parsimony_statisticallyConsistent_ae`，**不是** `SiteSampling.converges` 的推论。）

⚠ 本节**不**声称缺口可证：判定 = (1) 证伪 ＋ (2)(3) 「作为假设时的收口」。 -/

omit [Fintype X] [DecidableEq X] in
/-- ★★★ **缺口 2 的判定：证伪（全称闭包为假）**。

取 `Δ̂ n ≡ exPert` —— `Fin 4` 上**合法**的相异度（= 真矩阵 `exDiss` ＋ 有界扰动，
`‖ε‖_∞ = 2/5`，`Phylo/AttesonRadius.lean:650–670`）。plane ℓ¹ 和与 `n` **无关**：
`Σ_{x∈plane} |exPert − exDiss| = 14/5`（12 个非对角项各 `1/5`~`2/5`，对角项 `0`），
故 `η = 1` 时缺口的「`∃ N, ∀ n ≥ N, … < η`」**不可能**成立。

⇒ 缺口**不是**恒真命题；配 §7 ★C `bme_statistical_consistency_gap_satisfiable`（取 `Δ̂ ≡ D`）
得：该 `def` 是**真谓词**，**不存在**无假设的 `_holds`（这正是本节的判定）。
※ 文献同：DesperGascuel2004 `:656–659` 把「`Δ̂` 相合」写作 **Assuming that**。 -/
theorem bme_statistical_consistency_gap_refuted :
    ¬ bme_statistical_consistency_gap (fun (_ : ℕ) => exPert.val) exDiss := by
  intro h
  obtain ⟨N, hN⟩ := h 1 (by norm_num)
  have h1 := hN N le_rfl
  have hsum : (∑ x ∈ plane, |exPert.val x.1 x.2 - exDiss.val x.1 x.2|) = 14 / 5 := by
    rw [← sum_sum_eq_plane (fun i j : Fin 4 => |exPert.val i j - exDiss.val i j|)]
    simp only [sum_univ_four_fin, exPert, exPertVal, exDiss, exVal]
    norm_num
  linarith

omit [DecidableEq X] in
/-- ★★ **BME 树长的 Lipschitz 连续性**（`:682–691` 的定量形式）：线性估计量
`bmeLength c δ = ½ Σ_{x∈plane} c_{x}·δ_x`（`:188`）在 plane ℓ¹ 范数下以 `C/2` 为 Lipschitz 常数
（前提 `|c i j| ≤ C`）：

　　`|l̂_c(δ₁) − l̂_c(δ₂)| ≤ (C/2)·Σ_{x} |δ₁(x) − δ₂(x)|`。

⇒ 「距离矩阵靠近 ⟹ 各拓扑树长靠近」这一步**不需要任何假设**（`C` 取 `sup|c|` 即可）。 -/
theorem bmeLength_abs_sub_le (c : X → X → ℝ) {C : ℝ}
    (hc : ∀ i j : X, |c i j| ≤ C) (δ₁ δ₂ : Dissimilarity X) :
    |bmeLength c δ₁ - bmeLength c δ₂|
      ≤ (C / 2) * ∑ x ∈ plane, |δ₁.val x.1 x.2 - δ₂.val x.1 x.2| := by
  have hdiff : bmeLength c δ₁ - bmeLength c δ₂
      = (1 / 2) * ∑ x ∈ plane, c x.1 x.2 * (δ₁.val x.1 x.2 - δ₂.val x.1 x.2) := by
    simp only [bmeLength, ← Finset.sum_sub_distrib, ← mul_sub]
  have hbound : |∑ x ∈ plane, c x.1 x.2 * (δ₁.val x.1 x.2 - δ₂.val x.1 x.2)|
      ≤ C * ∑ x ∈ plane, |δ₁.val x.1 x.2 - δ₂.val x.1 x.2| := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun x _ => ?_
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (hc x.1 x.2) (abs_nonneg _)
  rw [hdiff, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  have h2 := mul_le_mul_of_nonneg_left hbound (by norm_num : (0 : ℝ) ≤ 1 / 2)
  calc (1 / 2) * |∑ x ∈ plane, c x.1 x.2 * (δ₁.val x.1 x.2 - δ₂.val x.1 x.2)|
      ≤ (1 / 2) * (C * ∑ x ∈ plane, |δ₁.val x.1 x.2 - δ₂.val x.1 x.2|) := h2
    _ = (C / 2) * ∑ x ∈ plane, |δ₁.val x.1 x.2 - δ₂.val x.1 x.2| := by ring

omit [Fintype X] [DecidableEq X] in
/-- ★ **`bmeCoeff` 落在 `(0, 2]`** ⇒ `bmeLength_abs_sub_le` 里的 `C = 2` 对 BME 系数矩阵可用。 -/
theorem abs_bmeCoeff_le_two (p : ℕ) : |bmeCoeff p| ≤ 2 := by
  have hpos : (0 : ℝ) < 2 * (1 / 2) ^ p := mul_pos (by norm_num) (pow_pos (by norm_num) p)
  rw [bmeCoeff, abs_of_pos hpos]
  calc 2 * (1 / 2) ^ p ≤ 2 * 1 :=
        mul_le_mul_of_nonneg_left
          (pow_le_one₀ (by norm_num) (by norm_num) : (1 / 2 : ℝ) ^ p ≤ 1) (by norm_num)
    _ = 2 := by ring

omit [DecidableEq X] in
/-- ★★★ **相合性 ⟹ BME 输出真树**（DesperGascuel2004 `:660–662` 的定量形式）：
把 ★ `bme_statistical_consistency_gap` 作为**假设**，则「样本量足够后 `T` 仍是唯一最短树」。

输入三层，缺一不可：

* `hgap`：**缺口本体**（距离层 ℓ¹ 相合，`:653–669`）；
* `hLip` 已被 ★★ `bmeLength_abs_sub_le` **证掉**，故这里只需 `hc : |c| ≤ C`（`hC : 0 ≤ C`）；
* `hstrict`：**真矩阵上 `T` 严格最短并留余量 `C·η`** —— 即 Theorem 2（`:694–699`）的
  `l̂(W) > l̂(T) = l(T)`（`l̂(T) = l(T)` 由 ★★★ `bme_length_eq_true_length` 提供）。
  有限拓扑集时余量自动存在（取 `min`）；无限拓扑集时此即「**一致余量**」（不可省，
  否则余量沿拓扑趋于 `0` 时没有统一 `N`）。

⇒ `bme_consistency_of_consistent_estimator`（`:152`）的 `hgrow`（树长层）由 `hgap` ＋ Lipschitz
**推出**，两个逼近层（距离层／树长层）由此打通。 -/
theorem bme_consistency_of_gap {ι : Type*} (c : ι → X → X → ℝ)
    (Δhat : ℕ → Dissimilarity X) (D : Dissimilarity X) (T : ι) {C : ℝ}
    (hC : 0 ≤ C) (hc : ∀ (W : ι) (i j : X), |c W i j| ≤ C)
    (hgap : bme_statistical_consistency_gap (fun n => (Δhat n).val) D)
    (hstrict : ∃ η : ℝ, 0 < η ∧
      ∀ W : ι, W ≠ T → bmeLength (c T) D + C * η < bmeLength (c W) D) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ W : ι, W ≠ T →
      bmeLength (c T) (Δhat n) < bmeLength (c W) (Δhat n) := by
  obtain ⟨η, hη, hst⟩ := hstrict
  obtain ⟨N, hN⟩ := hgap η hη
  refine ⟨N, fun n hn W hW => ?_⟩
  have hs : (∑ x ∈ plane, |(Δhat n).val x.1 x.2 - D.val x.1 x.2|) < η := hN n hn
  have hle : (C / 2) * (∑ x ∈ plane, |(Δhat n).val x.1 x.2 - D.val x.1 x.2|) ≤ C / 2 * η :=
    mul_le_mul_of_nonneg_left (le_of_lt hs) (by linarith)
  have hTW := bmeLength_abs_sub_le (c := c T) (hc T) (Δhat n) D
  have hWW := bmeLength_abs_sub_le (c := c W) (hc W) (Δhat n) D
  have h1 := (abs_le.mp (hTW.trans hle)).2
  have h2 := (abs_le.mp (hWW.trans hle)).1
  have h3 := hst W hW
  linarith

omit [DecidableEq X] in
/-- ★★★ **`bmeCoeff` 实例**：`c W := bmeCoeff ∘ p W`（`p W` = 拓扑 `W` 的拓扑距离）时
`C = 2`（★ `abs_bmeCoeff_le_two`），故余量写作 `2·η` —— 即**直接的 BME 版本**：
相合距离序列 ＋ 「真矩阵上 `T` 严格最短、余量 `2η`」⟹ 样本量足够后 `bmeLength` 在 `Δ̂ n` 上
仍以 `T` 为唯一最短。 -/
theorem bme_consistency_of_gap_bmeCoeff {ι : Type*} (p : ι → X → X → ℕ)
    (Δhat : ℕ → Dissimilarity X) (D : Dissimilarity X) (T : ι)
    (hgap : bme_statistical_consistency_gap (fun n => (Δhat n).val) D)
    (hstrict : ∃ η : ℝ, 0 < η ∧ ∀ W : ι, W ≠ T →
      bmeLength (fun i j => bmeCoeff (p T i j)) D + 2 * η
        < bmeLength (fun i j => bmeCoeff (p W i j)) D) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ W : ι, W ≠ T →
      bmeLength (fun i j => bmeCoeff (p T i j)) (Δhat n)
        < bmeLength (fun i j => bmeCoeff (p W i j)) (Δhat n) :=
  bme_consistency_of_gap (c := fun W i j => bmeCoeff (p W i j)) Δhat D T (C := 2)
    (by norm_num) (fun W i j => abs_bmeCoeff_le_two (p W i j)) hgap hstrict

end Dissimilarity

end NJ

/-! ## 14. ★★★ W26-B 判定（老师单审条目）：原形态**证伪** ＋ 二叉**忠实形态**（新名）

### 【改命题四要素】（老师 W26 §C 口径）

| 要素 | 内容 |
| - | - |
| **① 旧形态**（逐字未动） | `bme_pauplin_identity_gap`（`:380`）与其归约目标 `BmePauplinNormalization`（`:458`）。被判为**假**的是它们的**全称闭包** `∀ T : Phylogram (Fin 4), BmePauplinNormalization T`。 |
| **② 新形态**（新名字） | `bme_pauplin_identity_gap_binary δ T`：把 `T.IsBinary` 放进**数据**（合取项，**不是**定理假设），其余内容与 `BmePauplinNormalization` **逐字相同**。 |
| **③ 文献 `文件:行号`** | `references/md/DesperGascuel2004_BalancedMinimumEvolution.md:381`「if one of the two, say **B, is made of two subtrees denoted as B1 and B2**, then `dT_AB = (dT_AB1 + dT_AB2)/2`」；`:2003` 式 (7) `Σ 2^{r_AB}·p_ab = 1`（建立其上）；`:2026–2027` 式 (9) `SᵗF = 1`。 |
| **④ 理由** | 文献**没有**把 "binary" 写进任何定理假设，但**平衡平均的构造只对「两个子树」递归定义** ⇒ 式 (7)(9) 的成立范围本身就是 **binary 型构造**。多分叉顶点 `c` 上 `D_e(c) = (deg c − 1)/2`，故 plane 和 `= deg c − 1 ≠ 2`（只有 `deg = 3` 才 `= 2`）。⇒ 按老师口径（文献不显式限定 ⇒ 是数学事实）：**证伪原形态的全称闭包 ＋ 另立忠实形态**，而**不是**给旧 `def` 悄悄加前提。 |

### 反例（本节落地的机器核验）

`star4Tree : Phylogram (Fin 4)` —— 顶点 `Option (Fin 4)`、图 `SimpleGraph.starGraph none`、边权全 `1`：

* 中心 `none` 度 **4**、叶 `some i` 度 1 ⇒ `no_degree_two`（只排度 2）**满足** ⇒ 合法 `Cladogram (Fin 4)`；
* 但 `¬ star4Tree.IsBinary`（★★ `star4Tree_not_binary`）；
* 取挂边 `e = s(some 0, none)`：星形树上 `p_ij = 0`（`i = j`）／`= 2`（`i ≠ j`），
  `2^{1−p} = 1/2`，且 `e ∈ P_ij` 恰在 `i = 0 ∨ j = 0`（`i ≠ j`）时成立 ⇒ 共 6 项 ⇒
  plane 和 `= 6 · bmeCoeff 2 = 3 ≠ 2`（★★★ `star4Tree_plane_sum`）⇒
  ★★★ `star4Tree_not_normalization : ¬ BmePauplinNormalization star4Tree`。

⇒ ★★★ `bme_pauplin_identity_gap_refuted`（形态 = **某实例（谓词式）**；
等价地 **全称闭包为假** = ★★ `bme_pauplin_identity_gap_not_universal`）。

⚠ **边界如实**：被证伪的**不是** `def bme_pauplin_identity_gap` 本体（它以 `δ` 为参数、**仍未决**），
而是它的**归约目标**（§9 的 `hnorm`）的**全称闭包**；缺口本体仍缺「**二叉**实现树」这一件器材
（见 §12 器材 2：`exists_binary_realizing_phylogram`，库内**无** ✗）。 -/

namespace NJ
namespace Dissimilarity

open SimpleGraph

/-- ★★ **星形中心度**：`starGraph none` 上中心 `none` 的度是 `4`（`|Option (Fin 4)| − 1`）。 -/
theorem star4Tree_degree_none : (starGraph (none : Option (Fin 4))).degree none = 4 := by
  rw [degree_starGraph_center]
  simp

/-- ★★ **星形叶度**：`starGraph none` 上每片叶 `some i` 的度是 `1`。 -/
theorem star4Tree_degree_some (i : Fin 4) :
    (starGraph (none : Option (Fin 4))).degree (some i) = 1 :=
  degree_starGraph_of_ne_center (by simp)

/-- ★★★ **4 叶星形 phylogram**（**多分叉**实例）：顶点 `Option (Fin 4)`、图 `starGraph none`、
叶嵌入 `i ↦ some i`、边权全 `1`。

中心 `none` 度 `4`（**不是** 3）、叶度 1 ⇒ `no_degree_two` 满足（它只排度 2）⇒ 这是
**合法**的 `Phylogram (Fin 4)`，但**不是二叉的**（★★ `star4Tree_not_binary`）。
这正是 §12 的算术反例 `star4_plane_sum`（`3 ≠ 2`）所对应的**真实载体**。 -/
abbrev star4Tree : Phylogram (Fin 4) where
  V := Option (Fin 4)
  fintypeV := inferInstance
  decEqV := inferInstance
  graph := starGraph none
  decAdj := inferInstance
  isTree := isTree_starGraph none
  leaf := ⟨some, fun a b h => by simpa using h⟩
  leaf_iff_degree_one := by
    intro v
    rcases v with _ | i
    · constructor
      · rintro ⟨x, hx⟩
        exact (Option.some_ne_none x hx).elim
      · intro h
        rw [star4Tree_degree_none] at h
        exact absurd h (by norm_num)
    · constructor
      · intro _
        exact star4Tree_degree_some i
      · intro _
        exact ⟨i, rfl⟩
  no_degree_two := by
    intro v
    rcases v with _ | i
    · rw [star4Tree_degree_none]
      norm_num
    · rw [star4Tree_degree_some]
      norm_num
  w := fun _ => 1
  w_nonneg := fun _ => by norm_num

/-- ★★ 星形树的邻接（叶 → 中心）。 -/
theorem star4Tree_adj_leaf_center (i : Fin 4) :
    (starGraph (none : Option (Fin 4))).Adj (some i) none := by simp

/-- ★★ 星形树的邻接（中心 → 叶）。 -/
theorem star4Tree_adj_center_leaf (i : Fin 4) :
    (starGraph (none : Option (Fin 4))).Adj none (some i) := by simp

/-- ★★ 挂边 `s(some i, none)` 确实是边（`edgeSet` 成员）。 -/
theorem star4Tree_mem_edgeSet (i : Fin 4) :
    s(some i, none) ∈ (starGraph (none : Option (Fin 4))).edgeSet := by simp

/-- ★★★ **`star4Tree` 不是二叉的**：`IsBinary` 要求内部顶点度 `3`，而中心 `none` 度 `4`。
⇒ 这正是 `BmePauplinNormalization` 缺 `T.IsBinary` 的**具名反例**。 -/
theorem star4Tree_not_binary : ¬ star4Tree.IsBinary := by
  intro h
  have h3 : star4Tree.graph.degree none = 3 := h none (by
    rintro ⟨x, hx⟩
    exact Option.some_ne_none x hx)
  have h4 : (starGraph (none : Option (Fin 4))).degree none = 3 := h3
  rw [star4Tree_degree_none] at h4
  norm_num at h4

/-- ★★ **星形树上 `some i → none → some j` 是一条路径**（`i ≠ j`）：与 §12 的「唯一路径」衔接。 -/
theorem star4Tree_cons_path {i j : Fin 4} (hij : i ≠ j) :
    (Walk.cons (star4Tree_adj_leaf_center i)
      (Walk.cons (star4Tree_adj_center_leaf j) Walk.nil)).IsPath := by
  have h2 : (Walk.cons (star4Tree_adj_center_leaf j) Walk.nil).IsPath := by
    refine Walk.IsPath.cons Walk.IsPath.nil ?_
    simp
  refine Walk.IsPath.cons h2 ?_
  simp [hij]

/-- ★★★ **星形树上两片叶（`i ≠ j`）之间的唯一路径**恰为 `some i → none → some j`
（由 `existsUnique_path` 的唯一性 + `star4Tree_cons_path`）。 -/
theorem star4Tree_pathOf_leaf_ne {i j : Fin 4} (hij : i ≠ j) :
    star4Tree.pathOf (some i) (some j) =
      Walk.cons (star4Tree_adj_leaf_center i)
        (Walk.cons (star4Tree_adj_center_leaf j) Walk.nil) := by
  refine ((star4Tree.existsUnique_path (some i) (some j)).choose_spec.2 _
    (star4Tree_cons_path hij)).symm

/-- ★★★ **路径的边表**：`i ≠ j` 时 `P_ij = [s(i, c), s(c, j)]`。 -/
theorem star4Tree_edges_leaf_ne {i j : Fin 4} (hij : i ≠ j) :
    (star4Tree.pathOf (some i) (some j)).edges = [s(some i, none), s(none, some j)] := by
  rw [star4Tree_pathOf_leaf_ne hij, Walk.edges_cons, Walk.edges_cons]
  rfl

/-- ★★ **对角路径的边表为空**（`i = j` 时唯一路径是 `nil`）。 -/
theorem star4Tree_edges_leaf_self (i : Fin 4) :
    (star4Tree.pathOf (some i) (some i)).edges = [] := by
  have h : star4Tree.pathOf (some i) (some i) = Walk.nil :=
    ((star4Tree.existsUnique_path (some i) (some i)).choose_spec.2 Walk.nil
      Walk.IsPath.nil).symm
  rw [h]
  rfl

/-- ★★★ **星形拓扑距离**：`p_ij = 0`（`i = j`）／`= 2`（`i ≠ j`）。 -/
theorem star4Tree_pathlen (i j : Fin 4) :
    (star4Tree.pathOf (some i) (some j)).edges.length = if i = j then 0 else 2 := by
  by_cases hij : i = j
  · subst hij
    rw [star4Tree_edges_leaf_self]
    simp
  · rw [star4Tree_edges_leaf_ne hij]
    simp [hij]

/-- ★★★ **BME 系数取值**：`bmeCoeff p_ij = 2`（`i = j`，`p = 0`）／`= 1/2`（`i ≠ j`，`p = 2`）。 -/
theorem star4Tree_bmeCoeff_pathlen (i j : Fin 4) :
    bmeCoeff ((star4Tree.pathOf (some i) (some j)).edges.length) =
      if i = j then 2 else 1 / 2 := by
  rw [star4Tree_pathlen i j]
  by_cases hij : i = j
  · simp [hij, bmeCoeff]
  · simp [hij, bmeCoeff]
    norm_num

/-- ★ 挂边 `s(some x, none)` 与 `s(some i, none)` 相等 ⟺ `x = i`。 -/
theorem star4Tree_eq_leaf_first {x i : Fin 4} :
    s(some x, none) = s(some i, none) ↔ x = i := by
  rw [Sym2.eq_iff]
  constructor
  · rintro (⟨h, -⟩ | ⟨h, -⟩)
    · simpa using h
    · exact absurd h (Option.some_ne_none x)
  · intro h
    exact Or.inl ⟨by rw [h], rfl⟩

/-- ★ 挂边 `s(some x, none)` 与 `s(none, some j)` 相等 ⟺ `x = j`。 -/
theorem star4Tree_eq_leaf_second {x j : Fin 4} :
    s(some x, none) = s(none, some j) ↔ x = j := by
  rw [Sym2.eq_iff]
  constructor
  · rintro (⟨h, -⟩ | ⟨h, -⟩)
    · exact absurd h (Option.some_ne_none x)
    · simpa using h
  · intro h
    exact Or.inr ⟨by rw [h], rfl⟩

/-- ★★★ **路径经过挂边的判据**：`s(some x, none) ∈ P_ij ⟺ i ≠ j ∧ (x = i ∨ x = j)`
（星形树上，挂边 `x` 只被「一端是 `x`」的非平凡对经过）。 -/
theorem star4Tree_mem_edges_iff (x i j : Fin 4) :
    s(some x, none) ∈ (star4Tree.pathOf (some i) (some j)).edges ↔
      i ≠ j ∧ (x = i ∨ x = j) := by
  by_cases hij : i = j
  · subst hij
    rw [star4Tree_edges_leaf_self]
    simp
  · rw [star4Tree_edges_leaf_ne hij]
    simp only [List.mem_cons, star4Tree_eq_leaf_first, star4Tree_eq_leaf_second,
      List.not_mem_nil, or_false]
    constructor
    · intro h
      exact ⟨hij, h⟩
    · intro h
      exact h.2

/-- ★★ **指示函数的化简**：`[e ∈ P_ij] = [i ≠ j ∧ (x = i ∨ x = j)]`（0/1 形式）。 -/
theorem star4Tree_indicator (x i j : Fin 4) :
    (if s(some x, none) ∈ (star4Tree.pathOf (some i) (some j)).edges then (1 : ℝ) else 0)
      = if i ≠ j ∧ (x = i ∨ x = j) then (1 : ℝ) else 0 := by
  by_cases h : s(some x, none) ∈ (star4Tree.pathOf (some i) (some j)).edges
  · have h' : i ≠ j ∧ (x = i ∨ x = j) := (star4Tree_mem_edges_iff x i j).mp h
    simp [h, h']
  · have h' : ¬(i ≠ j ∧ (x = i ∨ x = j)) :=
      fun hh => h ((star4Tree_mem_edges_iff x i j).mpr hh)
    simp [h, h']

/-- ★★ **计数引理**：`plane` 中满足 `i ≠ j ∧ (x = i ∨ x = j)` 的有序对恰 `6 = 2·(4−1)` 个
（`fin_cases + decide` 直出；`Fin 4` 上全部 16 个有序对可判定）。 -/
theorem star4Tree_card (x : Fin 4) :
    ((plane (X := Fin 4)).filter
      (fun p : Fin 4 × Fin 4 => p.1 ≠ p.2 ∧ (x = p.1 ∨ x = p.2))).card = 6 := by
  fin_cases x <;> decide

/-- ★★★ **指示和 = 6**（`Σ_{i,j} [i ≠ j ∧ (x = i ∨ x = j)] = 6`，由 `star4Tree_card` 与
`Finset.sum_filter`／`Finset.sum_boole` 形态的桥）。 -/
theorem star4Tree_indicator_sum (x : Fin 4) :
    ∑ p ∈ (plane (X := Fin 4)),
      (if p.1 ≠ p.2 ∧ (x = p.1 ∨ x = p.2) then (1 : ℝ) else 0) = 6 := by
  have h2 : ∑ p ∈ (plane (X := Fin 4)),
      (if p.1 ≠ p.2 ∧ (x = p.1 ∨ x = p.2) then (1 : ℝ) else 0)
      = (((plane (X := Fin 4)).filter
        (fun p : Fin 4 × Fin 4 => p.1 ≠ p.2 ∧ (x = p.1 ∨ x = p.2))).card : ℝ) := by
    rw [← Finset.sum_filter]
    simp
  rw [h2, star4Tree_card x]
  norm_num

/-- ★★★★ **星形树的 plane 和 `= 3`**（§12 算术反例 `star4_plane_sum` 的**树级**版本）：
挂边 `s(some x, none)` 上

　`Σ_{(i,j) ∈ plane} 2^{1−p_ij}·[s(x,c) ∈ P_ij] = 6 · bmeCoeff 2 = 3 ≠ 2`。

⇒ `BmePauplinNormalization star4Tree` **为假**（★★★ `star4Tree_not_normalization`）。 -/
theorem star4Tree_plane_sum (x : Fin 4) :
    ∑ p ∈ plane,
      bmeCoeff ((star4Tree.pathOf (some p.1) (some p.2)).edges.length)
        * (if s(some x, none) ∈ (star4Tree.pathOf (some p.1) (some p.2)).edges
           then (1 : ℝ) else 0) = 3 := by
  have hstep : ∀ p ∈ plane,
      bmeCoeff ((star4Tree.pathOf (some p.1) (some p.2)).edges.length)
        * (if s(some x, none) ∈ (star4Tree.pathOf (some p.1) (some p.2)).edges
           then (1 : ℝ) else 0)
      = (1 / 2) * (if p.1 ≠ p.2 ∧ (x = p.1 ∨ x = p.2) then (1 : ℝ) else 0) := by
    intro p _
    rw [star4Tree_bmeCoeff_pathlen p.1 p.2, star4Tree_indicator x p.1 p.2]
    by_cases hp : p.1 = p.2
    · simp [hp]
    · by_cases hx : x = p.1 ∨ x = p.2 <;> simp [hp, hx]
  refine (Finset.sum_congr rfl hstep).trans ?_
  rw [← Finset.mul_sum]
  rw [star4Tree_indicator_sum x]
  norm_num

/-- ★★★ **与 `BmePauplinNormalization` 同形**（`T.leaf` 形态）的 plane 和 `= 3`。 -/
theorem star4Tree_plane_sum_leaf (x : Fin 4) :
    ∑ p ∈ plane,
      bmeCoeff ((star4Tree.pathOf (star4Tree.leaf p.1) (star4Tree.leaf p.2)).edges.length)
        * (if s(some x, none) ∈
            (star4Tree.pathOf (star4Tree.leaf p.1) (star4Tree.leaf p.2)).edges
           then (1 : ℝ) else 0) = 3 :=
  star4Tree_plane_sum x

/-- ★★★★ **反例判定**：`¬ BmePauplinNormalization star4Tree` —— 4 叶星形（**合法**的
`Phylogram (Fin 4)`）上 Pauplin 归一化**为假**（`3 ≠ 2`）。

⇒ §9 的归约定理 `bme_pauplin_identity_gap_of_normalization` 的 `hnorm` **不能**对任意实现树
实例化；缺的正是 `T.IsBinary`（§12 器材 1/2）。 -/
theorem star4Tree_not_normalization : ¬ BmePauplinNormalization star4Tree := by
  intro h
  have hmem : s(some 0, none) ∈ star4Tree.graph.edgeSet := star4Tree_mem_edgeSet 0
  have h3 := h (s(some 0, none)) hmem
  rw [star4Tree_plane_sum_leaf 0] at h3
  norm_num at h3

/-- ★★★★ **原形态证伪（形态 = 某实例）**：存在一棵**合法**的 `Phylogram (Fin 4)` 使
`BmePauplinNormalization` 为**假** —— 见证 = `star4Tree`（4 叶星形，plane 和 `3 ≠ 2`）。

⚠ 被证伪的**不是** `def bme_pauplin_identity_gap` 本体（以 `δ` 为参数、仍未决），
而是**其归约目标** `BmePauplinNormalization` 的**全称闭包**（见 ★★
`bme_pauplin_identity_gap_not_universal`）。 -/
theorem bme_pauplin_identity_gap_refuted :
    ∃ T : Phylogram.{0, 0} (Fin 4), ¬ BmePauplinNormalization T :=
  ⟨star4Tree, star4Tree_not_normalization⟩

/-- ★★★ **原形态证伪（形态 = 全称闭包为假）**：`∀ T, BmePauplinNormalization T` **不成立**
（4 叶星形 `star4Tree` 是反例）。 -/
theorem bme_pauplin_identity_gap_not_universal :
    ¬ ∀ T : Phylogram.{0, 0} (Fin 4), BmePauplinNormalization T :=
  fun h => star4Tree_not_normalization (h star4Tree)

section BinaryShape

universe u

variable {X : Type u} [Fintype X] [DecidableEq X]

/-- ★★★★ **忠实形态（W26-B 新名；旧 `def` 逐字未动）**：`T` 是 `δ` 的**二叉**实现树
（`T.IsBinary`，`Phylo/Core.lean:93`）**且**满足 Pauplin 归一化（式 (9)，`:2027`）。

★ 与 `BmePauplinNormalization` 的关系：**内容逐字相同**，只把 `T.IsBinary` 放进**数据**
（合取项）—— 依据 `references/md/DesperGascuel2004_BalancedMinimumEvolution.md:381`：
平衡平均 `dT_AB` 只在「`A`、`B` 各由**两个子树**组成」时递归定义 ⇒ 式 (7)（`:2003`）与
式 (9)（`:2026–2027`）的成立范围是 **binary 型构造**。

★ 为什么**不是**给旧 `def` 加前提：文献未把 "binary" 写进定理假设，而多分叉时该恒等式
**是假的**（★★ `star4Tree_not_normalization`）⇒ 按老师口径这是**数学事实**，
故旧形态由 ★★★ `bme_pauplin_identity_gap_refuted` **证伪**、忠实形态在此**另立新名**。 -/
def bme_pauplin_identity_gap_binary (δ : Dissimilarity X) (T : Phylogram X) : Prop :=
  T.IsBinary ∧
    (∀ i j : X, T.dist (T.leaf i) (T.leaf j) = δ.val i j) ∧
    BmePauplinNormalization T

omit [DecidableEq X] in
/-- ★★★ **归约定理按新形态重述**（旧 `bme_pauplin_identity_gap_of_normalization`（`:536`）
**一字未动**）：二叉忠实形态 ⟹ 原缺口 `bme_pauplin_identity_gap δ`。

⇒ 新形态是原缺口的**充分条件**（不是削弱）：一旦补上「二叉实现树」（§12 器材 2
`exists_binary_realizing_phylogram`）与二叉上的 `D_e = 1`（§12 器材 3），
`bme_pauplin_identity_gap` 即随之落地。 -/
theorem bme_pauplin_identity_gap_of_binary (δ : Dissimilarity X) (T : Phylogram X)
    (h : bme_pauplin_identity_gap_binary δ T) : bme_pauplin_identity_gap δ :=
  bme_pauplin_identity_gap_of_normalization δ T h.2.1 h.2.2

end BinaryShape

end Dissimilarity
end NJ
