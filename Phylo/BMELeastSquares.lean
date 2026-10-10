/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.AttesonRadius

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

**陈述**：对每个可加、正定的相异度 `δ`（⇒ 由 `Phylo/Buneman.lean:589` 的
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
`l̂(T) = l(T)`（DesperGascuel2004 Theorem 1 之 (2) 与 Theorem 2 的等式半）。 -/
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
「样本量足够后 BME 输出真树」（DesperGascuel2004 `:701–712` 的统计一致性）。 -/
def bme_statistical_consistency_gap (Δhat : ℕ → X → X → ℝ) (D : Dissimilarity X) : Prop :=
  ∀ η : ℝ, 0 < η → ∃ N : ℕ, ∀ n ≥ N,
    (∑ x ∈ plane, |Δhat n x.1 x.2 - D.val x.1 x.2|) < η

end Dissimilarity

end NJ
