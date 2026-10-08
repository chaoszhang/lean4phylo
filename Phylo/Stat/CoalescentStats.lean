/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.Stat.Coalescent

/-!
# `Phylo.Stat.CoalescentStats` —— 溯祖理论里的经典统计量（总枝长 / Watterson / Tajima / SFS）

本文件把**群体遗传学里由溯祖直接给出的经典期望**形式化。全部结论都是**实数层的期望**
（与 `Phylo/Stat/Coalescent.lean` 同一层次）：`k` 条谱系的逗留时间期望是
`E[τ_k] = 1/d_k = 2/(k(k−1))`（K82 (1.7)/(1.11)，见 `Coalescent.sojournMean`）。

## 1. 总枝长期望

`n` 条谱系的溯祖树在「有 `k` 条谱系」的时期有 `k` 条枝，故**总枝长**为

  `L_n = Σ_{k=2}^{n} k · τ_k`，`E[L_n] = Σ_{k=2}^{n} k·2/(k(k−1)) = Σ_{k=2}^{n} 2/(k−1) = 2·H_{n−1}`，

`H_m = Σ_{j=1}^{m} 1/j` 是调和数。见 `totalTreeLengthMean_eq`。

## 2. Watterson (1975)

无限位点模型，**每位点每谱系**的突变率取 `θ/2`（这是**模型约定**，本文件显式写出）。
则分离位点数 `S` 满足 `E[S] = (θ/2)·E[L_n] = θ·H_{n−1}`（`watterson_expected_segregating`），
且 Watterson 估计量 `θ_W = S / H_{n−1}` **无偏**（`wattersonTheta_unbiased`）。

出处（**转述/教科书级**，教师明示允许转述）：Watterson, G. A. (1975),
*On the number of segregating sites in genetical models without recombination*,
Theoretical Population Biology **7**:256–276；Hein–Schierup–Wiuf, *Gene Genealogies,
Variation and Evolution*（第 2–3 章）；Wakeley, *Coalescent Theory*（第 3 章）。

## 3. Tajima (1983) 与 SFS

* `Σ_{k=2}^{n} E[τ_k]·d_k = n − 1`（`sum_sojournMean_mul_rate`）——「每段时期恰贡献 `1`」；
* 两两差异的平均数 `π`：`E[T₂] = sojournMean 2 = 1`，故在 `θ/2` 约定下 `E[π] = θ`
  （`tajima_expected_pi`）；
* **site frequency spectrum 的对账**：`Σ_{i=1}^{n−1} θ/i = θ·H_{n−1} = E[S]`
  （`sfs_sum_eq`、`sfs_sum_of_itemwise`）。
  出处：Tajima, F. (1983), *Evolutionary relationship of DNA sequences in finite populations*,
  Genetics **105**:437–460（**转述**）。

## 4. 诚实边界（逐条）

| 条目 | 状态 |
|---|---|
| `E[L_n] = 2·H_{n−1}` | **已证**（`totalTreeLengthMean_eq`；与 `Coalescent.sojournMean` 接合见 `mul_sojournMean` / `totalTreeLengthMean_eq_sum_sojourn`） |
| `E[S] = θ·H_{n−1}`、`θ_W` 无偏 | **已证**（**在 `θ/2` 的模型约定下**） |
| `Σ E[τ_k]·d_k = n − 1` | **已证** |
| SFS 的**求和**对账 `Σ θ/i = θ·H_{n−1}` | **已证** |
| SFS 的**逐项**期望 `E[ξ_i] = θ/i` | ❌ **未形式化**：需要「一般 `n` 的 MSC 谱系计数分布」（size-biased 论证）。本文件只给**条件形式** `sfs_sum_of_itemwise`（假设逐项期望 ⇒ 求和一致） |
| `E[π] = θ` | ⚠️ **只在「两序列」这一层的记账**（`tajima_expected_pi`）；一般 `n` 的 `π` 分布未形式化 |
| 以上是**实数层期望**还是**测度层随机变量** | ⚠️ **实数层**。不是测度层的随机变量，也没有用到大数定律。 |
-/

noncomputable section

namespace Phylo.Stat.CoalescentStats

open Coalescent

/-! ## 1. 调和数 -/

/-- 调和数 `H_m = Σ_{j=1}^{m} 1/j`。 -/
noncomputable def harmonic (m : ℕ) : ℝ := ∑ j ∈ Finset.range m, 1 / ((j : ℝ) + 1)

theorem harmonic_zero : harmonic 0 = 0 := by simp [harmonic]

theorem harmonic_succ (m : ℕ) : harmonic (m + 1) = harmonic m + 1 / ((m : ℝ) + 1) := by
  rw [harmonic, Finset.sum_range_succ, harmonic]

theorem harmonic_nonneg (m : ℕ) : 0 ≤ harmonic m := by
  rw [harmonic]
  exact Finset.sum_nonneg fun j _ => by positivity

theorem harmonic_pos {m : ℕ} (hm : 0 < m) : 0 < harmonic m := by
  obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hm)
  rw [harmonic_succ]
  have h1 : 0 ≤ harmonic m' := harmonic_nonneg m'
  have h2 : 0 < 1 / ((m' : ℝ) + 1) := by positivity
  linarith

theorem harmonic_strictMono : StrictMono harmonic := by
  apply strictMono_nat_of_lt_succ
  intro m
  rw [harmonic_succ]
  have h : 0 < 1 / ((m : ℝ) + 1) := by positivity
  linarith

theorem harmonic_mono : Monotone harmonic := harmonic_strictMono.monotone

/-! ## 2. 总枝长期望 -/

/-- ★★★ **每条谱系对总枝长的贡献**：`k · E[τ_k] = k · 2/(k(k−1)) = 2/(k−1)`。 -/
theorem mul_sojournMean (k : ℕ) (hk : 2 ≤ k) :
    (k : ℝ) * sojournMean k = 2 / ((k : ℝ) - 1) := by
  have hk' : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have h0 : (k : ℝ) ≠ 0 := by linarith
  have h1 : (k : ℝ) - 1 ≠ 0 := by linarith
  rw [sojournMean]
  field_simp

/-- ★★★ **`n` 条谱系的溯祖树的总枝长期望** `E[L_n] = Σ_{k=2}^{n} 2/(k−1)`
（写成 `j = k − 2` 的 `n−1` 项和）。 -/
noncomputable def totalTreeLengthMean (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (n - 1), 2 / ((j : ℝ) + 1)

/-- ★★★ **闭形式**：`E[L_n] = 2·H_{n−1}`。 -/
theorem totalTreeLengthMean_eq (n : ℕ) : totalTreeLengthMean n = 2 * harmonic (n - 1) := by
  rw [totalTreeLengthMean, harmonic, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- ★★★ **与库内 `Coalescent.sojournMean` 的接合**：`E[L_n] = Σ_{k=2}^{n} k·E[τ_k]`。 -/
theorem totalTreeLengthMean_eq_sum_sojourn (n : ℕ) :
    totalTreeLengthMean n
      = ∑ j ∈ Finset.range (n - 1), ((j + 2 : ℕ) : ℝ) * sojournMean (j + 2) := by
  rw [totalTreeLengthMean]
  exact Finset.sum_congr rfl fun j _ => by
    rw [mul_sojournMean (j + 2) (by omega)]
    push_cast
    ring

/-- ★★ 总枝长期望非负。 -/
theorem totalTreeLengthMean_nonneg (n : ℕ) : 0 ≤ totalTreeLengthMean n := by
  rw [totalTreeLengthMean]
  exact Finset.sum_nonneg fun j _ => by positivity

/-- ★★ 总枝长期望随 `n`（弱）单调不减。 -/
theorem totalTreeLengthMean_mono : Monotone totalTreeLengthMean := by
  intro a b hab
  rw [totalTreeLengthMean_eq, totalTreeLengthMean_eq]
  have h : harmonic (a - 1) ≤ harmonic (b - 1) := harmonic_mono (by omega)
  linarith

/-! ## 3. Watterson (1975)：分离位点数 -/

/-- **分离位点数的期望**（`θ/2` = 每位点每谱系的突变率，**模型约定**）：
`E[S] = (θ/2)·E[L_n]`。 -/
noncomputable def segregatingSitesMean (θ : ℝ) (n : ℕ) : ℝ :=
  (θ / 2) * totalTreeLengthMean n

/-- ★★★ **Watterson (1975)**：`E[S] = θ·H_{n−1}`。 -/
theorem watterson_expected_segregating (θ : ℝ) (n : ℕ) :
    segregatingSitesMean θ n = θ * harmonic (n - 1) := by
  rw [segregatingSitesMean, totalTreeLengthMean_eq]
  ring

/-- **Watterson 估计量** `θ_W = S / H_{n−1}`。 -/
noncomputable def wattersonTheta (S : ℝ) (n : ℕ) : ℝ := S / harmonic (n - 1)

/-- ★★ **`θ_W` 无偏**：把 `S` 换成它的期望 `θ·H_{n−1}` 得回 `θ`。 -/
theorem wattersonTheta_unbiased {n : ℕ} (θ : ℝ) (h : harmonic (n - 1) ≠ 0) :
    wattersonTheta (θ * harmonic (n - 1)) n = θ := by
  rw [wattersonTheta, mul_div_cancel_right₀ _ h]

/-- ★★ `E[S]` 与 `θ_W` 的**一致性对账**：`θ_W(E[S]) · H_{n−1} = θ · H_{n−1}`。 -/
theorem wattersonTheta_of_mean (θ : ℝ) (n : ℕ) :
    wattersonTheta (segregatingSitesMean θ n) n * harmonic (n - 1)
      = θ * harmonic (n - 1) := by
  by_cases h : harmonic (n - 1) = 0
  · rw [h, mul_zero, mul_zero]
  · rw [wattersonTheta, watterson_expected_segregating,
      mul_div_cancel_right₀ _ h]

/-! ## 4. Tajima (1983) 与 site frequency spectrum -/

/-- ★★ **Tajima 的核心恒等式**：`Σ_{k=2}^{n} E[τ_k]·d_k = n − 1`
（每个「有 `k` 条谱系」的时期恰贡献 `1`，因为 `d_k·E[τ_k] = 1`）。
写成 `j = k − 2` 的 `m` 项和：`Σ_{j=0}^{m−1} E[τ_{j+2}]·d_{j+2} = m`。 -/
theorem sum_sojournMean_mul_rate (m : ℕ) :
    (∑ j ∈ Finset.range m, sojournMean (j + 2) * kingmanRate (j + 2)) = (m : ℝ) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    have h := kingmanRate_mul_sojournMean (k := m + 2) (by omega)
    rw [mul_comm (sojournMean (m + 2)) (kingmanRate (m + 2)), h]
    push_cast
    ring

/-- ★★ **Tajima (1983)**：两两差异的平均数 `π` 的期望为 `θ`。
在「每位点每谱系突变率 `θ/2`」的约定下，两个序列的谱系总长为 `2·T₂`，且
`E[T₂] = sojournMean 2 = 1`，故 `E[π] = (θ/2)·2·1 = θ`。 -/
theorem tajima_expected_pi (θ : ℝ) : (θ / 2) * (2 * sojournMean 2) = θ := by
  rw [sojournMean_two]; ring

/-- ★★ **SFS 的求和记账**：`Σ_{i=1}^{n−1} θ/i = θ·H_{n−1}`（与 `E[S]` 一致）。 -/
theorem sfs_sum_eq (θ : ℝ) (n : ℕ) :
    (∑ i ∈ Finset.range (n - 1), θ / ((i : ℝ) + 1)) = θ * harmonic (n - 1) := by
  rw [harmonic, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- ★★ **SFS 对账（条件形式）**：**若**频率谱满足逐项期望 `ξ_i = θ/i`（`i = 1..n−1`），
**则**其总和 = `θ·H_{n−1}` = `E[S]`。

⚠️ 「逐项期望 `E[ξ_i] = θ/i` 本身」**未形式化**（需要一般 `n` 的 MSC 谱系计数分布，
size-biased 论证）—— 见文件头诚实边界表；本定理把它写成**显式前提**。 -/
theorem sfs_sum_of_itemwise (θ : ℝ) (n : ℕ) (ξ : ℕ → ℝ)
    (h : ∀ i, ξ i = θ / ((i : ℝ) + 1)) :
    (∑ i ∈ Finset.range (n - 1), ξ i) = θ * harmonic (n - 1) := by
  rw [harmonic, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [h i]; ring

end Phylo.Stat.CoalescentStats
