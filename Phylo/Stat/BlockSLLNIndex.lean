/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.Stat.BlockSLLN

/-!
# `Phylo.Stat.BlockSLLNIndex` —— 换指标引理：前 `n` 个位点 vs 前 `k` 棵树（W13j）

## 1. 问题（规格 §3.3）

`Phylo/Stat/BlockSLLN.lean` 的 `BlockSLLNIdx` 给出的是「**前 `k` 棵树的全部位点**」上的加权平均收敛：

    (∑_{j<k} M_j) / (∑_{j<k} L_j)  →  lim          （几乎必然）

而端到端定理里的 `n` 是**位点序号**（如 `MSCSamplingAE` 的 `emp n`），问的是「前 `n` 个位点的平均」。
两者只差在「**第 `n` 个位点落在第几棵树里**」。规格 §4③ 给的 `L_j ≤ C` 正是为这一步准备的
（主定理 `BlockSLLN` 的证明**用不到**它，见其 docstring）。

## 2. 记号与结论

* `cumSites L k ω = ∑_{j<k} L_j ω` —— 第 `k` 棵树**之前**的位点总数（规格 §3.3 的 `N_k`）；
* `treesCovered L n ω` —— 按位点序号数满 `n` 个位点时**已经数完的完整树**的棵数 `k(n)`
  （最大的 `k ≤ n` 使 `N_k ≤ n`）。

则 **尾块至多 `C` 个位点**（`n - N_{k(n)} ≤ C`）、且 `k(n) → ∞`（只需 `L ≥ 1`）。
于是对任意「单位点权重 `≤ B`」的位点权重序列 `S`、其块和 `M_j = ∑_{该块位点} S`：

    | ∑_{m<n} S_m  -  ∑_{j<k(n)} M_j |  ≤  B · C        （与 n 无关的常数）

即规格 §3.3 的「**两者相差 ≤ `C` 个位点**」（按权重口径就是 `B·C`）；
再除以 `n` ⇒ 相对误差 `→ 0` ⇒ **两者同极限**（本文件的主定理）。

## 3. 本文件交付

| 声明 | 内容 |
|---|---|
| `cumSites` / `treesCovered` | 累计位点数 `N_k` 与换指标映射 `k(n)` |
| `cumSites_mono` / `cumSites_succ` / `le_cumSites` / `cumSites_le_mul` | 记账：`N` 单调（**零假设**）、`k ≤ N_k`（只需 `L ≥ 1`）、`N_k ≤ C·k`（只需 `L ≤ C`） |
| `sub_cumSites_treesCovered_le` | **尾块 ≤ `C` 个位点**（规格 §4③ 的 `L ≤ C` 在此**必需**） |
| `lt_cumSites_treesCovered_succ` | `n < N_{k(n)+1}`（`k(n)` 的极大性） |
| `abs_sum_sub_blockSum_le` | **换指标误差界** `≤ B·C` |
| `treesCovered_mono` / `treesCovered_tendsto_atTop` | 两者都**零假设**（不需要 `L ≥ 1`，与 `C` 无关） |
| `tendsto_prefixAvg_of_tendsto_blockAvg` | 逐 `ω`：块平均 → `lim` ⇒ 前缀平均 → `lim` |
| `prefixAvg_tendsto_of_blockAvg_tendsto` | 逐指标 a.e. 版（吃 `BlockSLLNIdx` 的**结论**） |
| `prefixAvg_tendsto_ae` | 端到端可组合：吃 `BlockSLLNIdx` 的**假设**，内部调用它 |
| `cumSites_const_one` / `treesCovered_const_one` | 退化一致性：`L ≡ 1` ⇒ `k(n) = n` |
| `prefixAvg_concrete_instance` | 具体实例（`L ≡ 1`、`M ≡ 0`、`S ≡ 0`）：反空洞 |

## 4. 诚实边界（逐条，不藏）

| 条目 | 状态 |
|---|---|
| `L_j ≤ C`（规格 §4③） | 本文件**必须显式假设**（`hC`）：尾块 ≤ `C` 个位点、`N_{k(n)}/n → 1` **两处**都要它。这是 `L ≤ C` 在 W13 里唯一的用途 |
| `L_j ≥ 1` | 显式假设（`hL1`）：`k(n) → ∞` 与 `N_k ≥ k`（分母不退化）都要它 |
| 逐位点权重序列 `S` | 本文件把「块和 = 该块全部位点之和」写成显式假设 `hS`、单位点权重界写成 `hw`。**这两条是生成模型的逐点事实**（规格 §1.2 的双向界），但库内**没有**「逐位点权重序列」这一层对象（BRIEF §10 侦察实测：`geneScoreWith` 在库内**除本 docstring 行外** 0 命中）⇒ 本文件把它作为**干净接口**，不假装已经构造出来 |
| 「块平均 → lim」的来源 | 由调用方供给（`BlockSLLNIdx`，或识别等式）；本文件不重复证它 |
| 「同树位点条件独立」（规格 §3.4） | **完全不进入本文件**：这里只谈**块和**与**位点和**的记账关系，位点在块内是否独立无关 |
| 反空洞 | 本文件**没有**新增 `structure`、也没有新增 `def … : Prop`；仍给出具体实例 `prefixAvg_concrete_instance` 与退化恒等式 `treesCovered_const_one` |
-/

set_option autoImplicit false

noncomputable section

open Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal

namespace Phylo.Stat.BlockSLLNIndex

open Phylo.Stat.BlockSLLN

variable {Ω : Type*}

/-! ## 1. 累计位点数 `N_k` 与换指标映射 `k(n)` -/

/-- **累计位点数** `N k ω = ∑_{j<k} L j ω`：第 `k` 棵树**之前**的位点总数（规格 §3.3 的 `N_k`）。 -/
def cumSites (L : ℕ → Ω → ℕ) (k : ℕ) (ω : Ω) : ℕ :=
  ∑ j ∈ Finset.range k, L j ω

/-- **换指标映射** `k(n)`：最大的 `k ≤ n` 使 `N_k ω ≤ n`
（即按位点序号数满 `n` 个位点时，**已经数完的完整树**的棵数）。

上界 `k(n) ≤ n` 由 `Nat.findGreatest` 自带；配合 `L ≥ 1` 得 `n < N_{k(n)+1}`
（`lt_cumSites_treesCovered_succ`），配合 `L ≤ C` 得 `n - N_{k(n)} ≤ C`
（`sub_cumSites_treesCovered_le`）。 -/
def treesCovered (L : ℕ → Ω → ℕ) (n : ℕ) (ω : Ω) : ℕ :=
  Nat.findGreatest (fun k => cumSites L k ω ≤ n) n

theorem cumSites_zero (L : ℕ → Ω → ℕ) (ω : Ω) : cumSites L 0 ω = 0 := by
  simp [cumSites]

theorem cumSites_succ (L : ℕ → Ω → ℕ) (k : ℕ) (ω : Ω) :
    cumSites L (k + 1) ω = cumSites L k ω + L k ω := by
  simp [cumSites, Finset.sum_range_succ]

/-- `N` 关于块编号**单调**（**零假设**：正项和）。 -/
theorem cumSites_mono (L : ℕ → Ω → ℕ) (ω : Ω) : Monotone fun k => cumSites L k ω := by
  intro m n hmn
  show cumSites L m ω ≤ cumSites L n ω
  rw [cumSites, cumSites, ← Finset.sum_range_add_sum_Ico (fun j => L j ω) hmn]
  exact Nat.le_add_right _ _

/-- 位点总数的实数形式（把 `ℝ`-值的块长和与 `ℕ`-值的 `N_k` 接起来）。 -/
theorem sum_cast_eq_cumSites (L : ℕ → Ω → ℕ) (k : ℕ) (ω : Ω) :
    (∑ j ∈ Finset.range k, (L j ω : ℝ)) = (cumSites L k ω : ℝ) := by
  rw [cumSites, Nat.cast_sum]

/-- **块长不退化**：`k ≤ N_k`。**只需 `L ≥ 1`**（这也是 `k(n) → ∞` 的唯一来源）。 -/
theorem le_cumSites (L : ℕ → Ω → ℕ) (hL1 : ∀ j ω, 1 ≤ L j ω) (k : ℕ) (ω : Ω) :
    k ≤ cumSites L k ω := by
  induction k with
  | zero => exact Nat.zero_le 0
  | succ k ih =>
    rw [cumSites_succ]
    exact Nat.add_le_add ih (hL1 k ω)

/-- **块长有上界**：`N_k ≤ C·k`。**只需 `L ≤ C`**。 -/
theorem cumSites_le_mul (L : ℕ → Ω → ℕ) (C : ℕ) (hC : ∀ j ω, L j ω ≤ C) (k : ℕ) (ω : Ω) :
    cumSites L k ω ≤ C * k := by
  induction k with
  | zero => simp [cumSites]
  | succ k ih =>
    rw [cumSites_succ]
    calc cumSites L k ω + L k ω ≤ C * k + C := Nat.add_le_add ih (hC k ω)
      _ = C * (k + 1) := by ring

/-- `N_k = 0` 当且仅当 `k = 0`（**只需 `L ≥ 1`**）：`N_k` 不退化。 -/
theorem cumSites_eq_zero_iff (L : ℕ → Ω → ℕ) (hL1 : ∀ j ω, 1 ≤ L j ω) (k : ℕ) (ω : Ω) :
    cumSites L k ω = 0 ↔ k = 0 := by
  constructor
  · intro h
    have hle := le_cumSites L hL1 k ω
    omega
  · intro hk
    rw [hk, cumSites_zero]

/-! ## 2. 换指标映射的两条关键性质 -/

theorem treesCovered_le (L : ℕ → Ω → ℕ) (n : ℕ) (ω : Ω) : treesCovered L n ω ≤ n :=
  Nat.findGreatest_le n

theorem cumSites_treesCovered_le (L : ℕ → Ω → ℕ) (n : ℕ) (ω : Ω) :
    cumSites L (treesCovered L n ω) ω ≤ n :=
  Nat.findGreatest_spec (P := fun k => cumSites L k ω ≤ n) (m := 0) (Nat.zero_le n)
    (by rw [cumSites_zero]; exact Nat.zero_le n)

/-- **`k(n)` 的极大性**：`n < N_{k(n)+1}`（**只需 `L ≥ 1`**）。

证明：若 `N_{k(n)+1} ≤ n`，则 `k(n) + 1 ≤ N_{k(n)+1} ≤ n`（第一个不等号用 `le_cumSites`），
于是由 `Nat.findGreatest` 的极大性得 `k(n) + 1 ≤ k(n)`，矛盾。 -/
theorem lt_cumSites_treesCovered_succ (L : ℕ → Ω → ℕ) (hL1 : ∀ j ω, 1 ≤ L j ω)
    (n : ℕ) (ω : Ω) : n < cumSites L (treesCovered L n ω + 1) ω := by
  by_contra hcon
  have hle : cumSites L (treesCovered L n ω + 1) ω ≤ n := Nat.le_of_not_lt hcon
  have hb : treesCovered L n ω + 1 ≤ treesCovered L n ω :=
    Nat.le_findGreatest (P := fun k => cumSites L k ω ≤ n)
      (le_trans (le_cumSites L hL1 _ ω) hle) hle
  exact absurd hb (Nat.not_succ_le_self _)

/-- **尾块 ≤ `C` 个位点**（规格 §3.3 的「相差 ≤ `C` 个位点」的**数量**形态）：
`n - N_{k(n)} ≤ C`。**只需 `L ≥ 1` 与 `L ≤ C`**。 -/
theorem sub_cumSites_treesCovered_le (L : ℕ → Ω → ℕ) (C : ℕ)
    (hL1 : ∀ j ω, 1 ≤ L j ω) (hC : ∀ j ω, L j ω ≤ C) (n : ℕ) (ω : Ω) :
    n - cumSites L (treesCovered L n ω) ω ≤ C := by
  have hlt := lt_cumSites_treesCovered_succ L hL1 n ω
  rw [cumSites_succ] at hlt
  have hb := hC (treesCovered L n ω) ω
  omega

/-- `k(n)` 关于 `n` **单调**（**零假设**）。 -/
theorem treesCovered_mono (L : ℕ → Ω → ℕ) (ω : Ω) :
    Monotone fun n => treesCovered L n ω := by
  intro m n hmn
  show treesCovered L m ω ≤ treesCovered L n ω
  exact Nat.le_findGreatest (P := fun k => cumSites L k ω ≤ n)
    (le_trans (treesCovered_le L m ω) hmn)
    (le_trans (cumSites_treesCovered_le L m ω) hmn)

/-- **`k(n) → ∞`**（规格 §3.3 的「`n ≳ k → ∞`」）。**零假设**（连 `L ≥ 1` 都不用），
与 `C` 也无关：取 `a = max b (N_b)`，则 `b ≤ a` 且 `N_b ≤ a` ⇒ `b ≤ k(a)`。 -/
theorem treesCovered_tendsto_atTop (L : ℕ → Ω → ℕ) (ω : Ω) :
    Tendsto (fun n => treesCovered L n ω) atTop atTop := by
  refine (treesCovered_mono L ω).tendsto_atTop_atTop fun b =>
    ⟨max b (cumSites L b ω), ?_⟩
  exact Nat.le_findGreatest (P := fun k => cumSites L k ω ≤ max b (cumSites L b ω))
    (le_max_left _ _) (le_max_right _ _)

/-! ## 3. 换指标误差界（规格 §3.3 的「相差 ≤ `C` 个位点」） -/

/-- **换指标误差界**：设 `S : ℕ → Ω → ℝ` 是**逐位点权重**（`|S m ω| ≤ B`），
`M j` 是第 `j` 块的**块总权重**，且 `hS` 说「块和 = 该块全部位点之和」；
则**前 `n` 个位点的权重和**与**前 `k(n)` 棵树的块权重和**之差 `≤ B · C`。

证明：两者只差**尾块**（第 `k(n)` 块的、落在前 `n` 个位点内的那部分），其位点数
`= n - N_{k(n)} ≤ C`（`sub_cumSites_treesCovered_le`），每个位点权重 `≤ B` ⇒ 总差 `≤ B·C`。 -/
theorem abs_sum_sub_blockSum_le
    {S M : ℕ → Ω → ℝ} {L : ℕ → Ω → ℕ} {B : ℝ} {C : ℕ}
    (hL1 : ∀ j ω, 1 ≤ L j ω) (hC : ∀ j ω, L j ω ≤ C)
    (hw : ∀ m ω, |S m ω| ≤ B)
    (hS : ∀ k ω, ∑ m ∈ Finset.range (cumSites L k ω), S m ω = ∑ j ∈ Finset.range k, M j ω)
    (n : ℕ) (ω : Ω) :
    |(∑ m ∈ Finset.range n, S m ω) - ∑ j ∈ Finset.range (treesCovered L n ω), M j ω|
      ≤ B * (C : ℝ) := by
  have hNle : cumSites L (treesCovered L n ω) ω ≤ n := cumSites_treesCovered_le L n ω
  have hgap : n - cumSites L (treesCovered L n ω) ω ≤ C :=
    sub_cumSites_treesCovered_le L C hL1 hC n ω
  have hB : 0 ≤ B := le_trans (abs_nonneg (S 0 ω)) (hw 0 ω)
  have hsum : (∑ m ∈ Finset.range n, S m ω)
      = (∑ m ∈ Finset.range (cumSites L (treesCovered L n ω) ω), S m ω)
        + ∑ m ∈ Finset.Ico (cumSites L (treesCovered L n ω) ω) n, S m ω :=
    (Finset.sum_range_add_sum_Ico (fun m => S m ω) hNle).symm
  rw [← hS (treesCovered L n ω) ω, hsum, add_sub_cancel_left]
  calc |∑ m ∈ Finset.Ico (cumSites L (treesCovered L n ω) ω) n, S m ω|
      ≤ ∑ m ∈ Finset.Ico (cumSites L (treesCovered L n ω) ω) n, |S m ω| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _m ∈ Finset.Ico (cumSites L (treesCovered L n ω) ω) n, B :=
        Finset.sum_le_sum fun m _ => hw m ω
    _ = B * ((Finset.Ico (cumSites L (treesCovered L n ω) ω) n).card : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
    _ = B * ((n - cumSites L (treesCovered L n ω) ω : ℕ) : ℝ) := by rw [Nat.card_Ico]
    _ ≤ B * (C : ℝ) := by
        have hgapR : ((n - cumSites L (treesCovered L n ω) ω : ℕ) : ℝ) ≤ (C : ℝ) := by
          exact_mod_cast hgap
        exact mul_le_mul_of_nonneg_left hgapR hB

/-! ## 4. 换指标引理（极限形态） -/

/-- **换指标引理**（逐 `ω`）：若「块平均」（前 `k` 棵树的加权平均）收敛到 `lim`，
则「前 `n` 个位点的平均」也收敛到 `lim`。

证明骨架：

1. `k(n) → ∞`（`treesCovered_tendsto_atTop`，只需 `L ≥ 1`）⇒ 块平均沿 `k(n)` 也 `→ lim`；
2. `N_{k(n)} / n → 1`：由 `N_{k(n)} ≤ n` 与 `n - N_{k(n)} ≤ C` 夹逼；
3. 前缀和与块前缀和之差 `≤ B·C`（`abs_sum_sub_blockSum_le`）⇒ 除以 `n` 后 `→ 0`；
   再与第 1、2 条拼成 `(∑_{m<n} S_m)/n → lim`。 -/
theorem tendsto_prefixAvg_of_tendsto_blockAvg
    {S M : ℕ → Ω → ℝ} {L : ℕ → Ω → ℕ} {B lim : ℝ} {C : ℕ}
    (hL1 : ∀ j ω, 1 ≤ L j ω) (hC : ∀ j ω, L j ω ≤ C)
    (hw : ∀ m ω, |S m ω| ≤ B)
    (hS : ∀ k ω, ∑ m ∈ Finset.range (cumSites L k ω), S m ω = ∑ j ∈ Finset.range k, M j ω)
    (ω : Ω)
    (hblock : Tendsto (fun k : ℕ => (∑ j ∈ Finset.range k, M j ω) /
        (∑ j ∈ Finset.range k, (L j ω : ℝ))) atTop (𝓝 lim)) :
    Tendsto (fun n : ℕ => (∑ m ∈ Finset.range n, S m ω) / (n : ℝ)) atTop (𝓝 lim) := by
  -- 1. 块平均沿 `k(n)` 收敛
  have hPK : Tendsto (fun n : ℕ => (∑ j ∈ Finset.range (treesCovered L n ω), M j ω) /
      (∑ j ∈ Finset.range (treesCovered L n ω), (L j ω : ℝ))) atTop (𝓝 lim) :=
    hblock.comp (treesCovered_tendsto_atTop L ω)
  -- 2. 换指标比的偏差：`(n - N_{k(n)})/n → 0`
  have hQ1 : Tendsto (fun n : ℕ =>
      ((n : ℝ) - (cumSites L (treesCovered L n ω) ω : ℝ)) / (n : ℝ)) atTop (𝓝 0) := by
    apply squeeze_zero
    · intro n
      exact div_nonneg (sub_nonneg.mpr (by exact_mod_cast cumSites_treesCovered_le L n ω))
        (Nat.cast_nonneg n)
    · intro n
      have hNle : cumSites L (treesCovered L n ω) ω ≤ n := cumSites_treesCovered_le L n ω
      have hgapR : (n : ℝ) - (cumSites L (treesCovered L n ω) ω : ℝ) ≤ (C : ℝ) := by
        have h1 : ((n - cumSites L (treesCovered L n ω) ω : ℕ) : ℝ) ≤ (C : ℝ) := by
          exact_mod_cast sub_cumSites_treesCovered_le L C hL1 hC n ω
        rwa [Nat.cast_sub hNle] at h1
      exact div_le_div_of_nonneg_right hgapR (Nat.cast_nonneg n)
    · have hc : Tendsto (fun _ : ℕ => (C : ℝ)) atTop (𝓝 (C : ℝ)) := tendsto_const_nhds
      exact hc.div_atTop tendsto_natCast_atTop_atTop
  have hQ2 : Tendsto (fun n : ℕ =>
      (1 : ℝ) - ((n : ℝ) - (cumSites L (treesCovered L n ω) ω : ℝ)) / (n : ℝ))
      atTop (𝓝 (1 - 0)) := tendsto_const_nhds.sub hQ1
  rw [sub_zero] at hQ2
  -- 3. 换指标分母比 `N_{k(n)} / n → 1`
  have hQ : Tendsto (fun n : ℕ => (∑ j ∈ Finset.range (treesCovered L n ω), (L j ω : ℝ)) /
      (n : ℝ)) atTop (𝓝 1) := by
    refine hQ2.congr' ?_
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.one_le_iff_ne_zero.mp hn)
    rw [sum_cast_eq_cumSites]
    field_simp
    ring
  -- 4. 块前缀和除以 `n` 也收敛到 `lim`
  have hQ0P0 : ∀ n : ℕ, (∑ j ∈ Finset.range (treesCovered L n ω), (L j ω : ℝ)) = 0 →
      (∑ j ∈ Finset.range (treesCovered L n ω), M j ω) = 0 := by
    intro n hQn
    have h1 : (cumSites L (treesCovered L n ω) ω : ℝ) = 0 := by
      rw [← sum_cast_eq_cumSites]; exact hQn
    have h2 : cumSites L (treesCovered L n ω) ω = 0 := Nat.cast_eq_zero.mp h1
    have h3 : treesCovered L n ω = 0 := (cumSites_eq_zero_iff L hL1 _ ω).mp h2
    rw [h3, Finset.sum_range_zero]
  have hdivmul : ∀ n : ℕ,
      (∑ j ∈ Finset.range (treesCovered L n ω), M j ω) /
        (∑ j ∈ Finset.range (treesCovered L n ω), (L j ω : ℝ)) *
        ((∑ j ∈ Finset.range (treesCovered L n ω), (L j ω : ℝ)) / (n : ℝ))
      = (∑ j ∈ Finset.range (treesCovered L n ω), M j ω) / (n : ℝ) := by
    intro n
    by_cases hQ0 : (∑ j ∈ Finset.range (treesCovered L n ω), (L j ω : ℝ)) = 0
    · rw [hQ0, hQ0P0 n hQ0]; simp
    · by_cases hn : n = 0
      · subst hn; simp
      · have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
        field_simp
  have hP : Tendsto (fun n : ℕ => (∑ j ∈ Finset.range (treesCovered L n ω), M j ω) /
      (n : ℝ)) atTop (𝓝 lim) := by
    have hprod := hPK.mul hQ
    rw [mul_one] at hprod
    exact hprod.congr' (Eventually.of_forall hdivmul)
  -- 5. 真正的前缀和与块前缀和之差 `≤ B·C` ⇒ 除以 `n` 后 `→ 0`
  have hbound : ∀ n : ℕ, |((∑ m ∈ Finset.range n, S m ω) -
      ∑ j ∈ Finset.range (treesCovered L n ω), M j ω) / (n : ℝ)|
      ≤ B * (C : ℝ) / (n : ℝ) := by
    intro n
    have hnn : |(n : ℝ)| = (n : ℝ) := abs_of_nonneg (Nat.cast_nonneg n)
    rw [abs_div, hnn]
    exact div_le_div_of_nonneg_right
      (abs_sum_sub_blockSum_le hL1 hC hw hS n ω) (Nat.cast_nonneg n)
  have hdiff : Tendsto (fun n : ℕ => ((∑ m ∈ Finset.range n, S m ω) -
      ∑ j ∈ Finset.range (treesCovered L n ω), M j ω) / (n : ℝ)) atTop (𝓝 0) := by
    have hhigh : Tendsto (fun n : ℕ => B * (C : ℝ) / (n : ℝ)) atTop (𝓝 0) := by
      have hc : Tendsto (fun _ : ℕ => B * (C : ℝ)) atTop (𝓝 (B * (C : ℝ))) :=
        tendsto_const_nhds
      exact hc.div_atTop tendsto_natCast_atTop_atTop
    have hlow : Tendsto (fun n : ℕ => -((B * (C : ℝ)) / (n : ℝ))) atTop (𝓝 0) := by
      have hc : Tendsto (fun _ : ℕ => -(B * (C : ℝ))) atTop (𝓝 (-(B * (C : ℝ)))) :=
        tendsto_const_nhds
      simpa [neg_div] using hc.div_atTop tendsto_natCast_atTop_atTop
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlow hhigh
      (fun n => (abs_le.mp (hbound n)).1) (fun n => (abs_le.mp (hbound n)).2)
  -- 6. 拼装：`(块前缀和)/n + (真前缀和 - 块前缀和)/n = (真前缀和)/n`
  have hsum2 := hP.add hdiff
  rw [add_zero] at hsum2
  refine hsum2.congr' (Eventually.of_forall fun n => ?_)
  have hnum : (∑ j ∈ Finset.range (treesCovered L n ω), M j ω) +
      ((∑ m ∈ Finset.range n, S m ω) - ∑ j ∈ Finset.range (treesCovered L n ω), M j ω)
      = ∑ m ∈ Finset.range n, S m ω := by ring
  rw [← add_div, hnum]

/-! ## 5. 逐指标 a.e. 版（吃 `BlockSLLNIdx` 的结论） -/

/-- **换指标引理（逐指标 a.e.）**：假设与 `tendsto_prefixAvg_of_tendsto_blockAvg` 相同，
但「块平均 → `lim i`」是**逐指标 a.e.** 给出的 —— 这正是 `BlockSLLNIdx` 的**结论形状**。
⇒ 结论：「前 `n` 个位点的平均 → `lim i`」在同一个 a.e. 事件上对**所有** `i` 同时成立。 -/
theorem prefixAvg_tendsto_of_blockAvg_tendsto
    {ι : Type*} [Fintype ι] {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {S M : ι → ℕ → Ω → ℝ} {L : ι → ℕ → Ω → ℕ} {lim : ι → ℝ} {B : ℝ} {C : ℕ}
    (hL1 : ∀ i j ω, 1 ≤ L i j ω) (hC : ∀ i j ω, L i j ω ≤ C)
    (hw : ∀ i m ω, |S i m ω| ≤ B)
    (hS : ∀ i k ω, ∑ m ∈ Finset.range (cumSites (L i) k ω), S i m ω
      = ∑ j ∈ Finset.range k, M i j ω)
    (hblock : ∀ᵐ ω ∂μ, ∀ i : ι, Tendsto (fun k : ℕ => (∑ j ∈ Finset.range k, M i j ω) /
        (∑ j ∈ Finset.range k, (L i j ω : ℝ))) atTop (𝓝 (lim i))) :
    ∀ᵐ ω ∂μ, ∀ i : ι, Tendsto (fun n : ℕ => (∑ m ∈ Finset.range n, S i m ω) / (n : ℝ))
      atTop (𝓝 (lim i)) := by
  filter_upwards [hblock] with ω hω i
  exact tendsto_prefixAvg_of_tendsto_blockAvg (S := S i) (M := M i) (L := L i) (B := B)
    (C := C) (lim := lim i) (fun j ω' => hL1 i j ω') (fun j ω' => hC i j ω')
    (fun m ω' => hw i m ω') (fun k ω' => hS i k ω') ω (hω i)

/-- **端到端可组合版**：由 `BlockSLLNIdx` 的**假设**直接得到「前 `n` 个位点的平均 → `lim i`」
（内部调用 `BlockSLLNIdx` 得到块平均的 a.e. 收敛，再经
`prefixAvg_tendsto_of_blockAvg_tendsto` 换指标）。

与 `BlockSLLNIdx` 的唯一区别：块长是 `ℕ`-值的 `L`（换指标要数位点），
以及多出的位点层接口 `hw` / `hS`。 -/
theorem prefixAvg_tendsto_ae
    {ι : Type*} [Fintype ι] {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    {S M : ι → ℕ → Ω → ℝ} {L : ι → ℕ → Ω → ℕ} {lim : ι → ℝ} {B : ℝ} {C : ℕ}
    (hL1 : ∀ i j ω, 1 ≤ L i j ω) (hC : ∀ i j ω, L i j ω ≤ C)
    (hw : ∀ i m ω, |S i m ω| ≤ B)
    (hS : ∀ i k ω, ∑ m ∈ Finset.range (cumSites (L i) k ω), S i m ω
      = ∑ j ∈ Finset.range k, M i j ω)
    (hjoint : ∀ i, iIndepFun (fun j ω => (M i j ω, (L i j ω : ℝ))) μ)
    (hident : ∀ i j, IdentDistrib (fun ω => (M i j ω, (L i j ω : ℝ)))
      (fun ω => (M i 0 ω, (L i 0 ω : ℝ))) μ μ)
    (hintM : ∀ i, Integrable (fun ω => M i 0 ω) μ)
    (hintL : ∀ i, Integrable (fun ω => (L i 0 ω : ℝ)) μ)
    (hlim : ∀ i, (∫ ω, M i 0 ω ∂μ) / (∫ ω, (L i 0 ω : ℝ) ∂μ) = lim i) :
    ∀ᵐ ω ∂μ, ∀ i : ι, Tendsto (fun n : ℕ => (∑ m ∈ Finset.range n, S i m ω) / (n : ℝ))
      atTop (𝓝 (lim i)) := by
  have hblock := BlockSLLNIdx (μ := μ) (Mf := M) (Lf := fun i j ω => (L i j ω : ℝ))
    (lim := lim) hjoint hident (fun i j ω => by exact_mod_cast hL1 i j ω) hintM hintL hlim
  exact prefixAvg_tendsto_of_blockAvg_tendsto hL1 hC hw hS hblock

/-! ## 6. 退化一致性与反空洞 -/

theorem cumSites_const_one (k : ℕ) (ω : Ω) :
    cumSites (fun (_ : ℕ) (_ : Ω) => 1) k ω = k := by
  induction k with
  | zero => simp [cumSites]
  | succ k ih => rw [cumSites_succ, ih]

/-- **退化一致性**：`L ≡ 1`（每棵树恰好一个位点）时 `k(n) = n`
—— 换指标映射退化为恒等，尾块长度为 `0`（`n - N_{k(n)} = 0`）。 -/
theorem treesCovered_const_one (n : ℕ) (ω : Ω) :
    treesCovered (fun (_ : ℕ) (_ : Ω) => 1) n ω = n :=
  Nat.findGreatest_eq (P := fun k => cumSites (fun (_ : ℕ) (_ : Ω) => 1) k ω ≤ n)
    (by rw [cumSites_const_one])

/-- **反空洞 / 具体实例**：取 `L ≡ 1`、`M ≡ 0`、`S ≡ 0`（`B = 0`、`C = 1`），
`tendsto_prefixAvg_of_tendsto_blockAvg` 的假设**全部满足**，结论确实成立
（此时 `k(n) = n`、前缀平均与块平均都是 `0`）。 -/
theorem prefixAvg_concrete_instance :
    Tendsto (fun n : ℕ => (∑ _m ∈ Finset.range n, (0 : ℝ)) / (n : ℝ)) atTop (𝓝 0) :=
  tendsto_prefixAvg_of_tendsto_blockAvg (Ω := Unit) (S := fun _ _ => (0 : ℝ))
    (M := fun _ _ => (0 : ℝ)) (L := fun (_ : ℕ) (_ : Unit) => 1) (B := 0) (C := 1)
    (lim := 0) (fun _ _ => le_refl 1) (fun _ _ => le_refl 1) (fun _ _ => by simp)
    (fun _ _ => by simp) () (by simp)

end Phylo.Stat.BlockSLLNIndex
