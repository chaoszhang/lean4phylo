/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.Stat.EmpiricalConvergence

/-!
# `Phylo.Stat.AESampling` —— **有限指标集上的几乎必然大数定律**（通用核心）

W20 的任务 A 要把三条「公理化 SLLN」（`SiteSampling` · `USTARSampling` · `MLProblem`）
升级成真概率空间上的 a.e. 定理。三条的形状不同（位点支持表 / 相异度 / 似然目标），
但**概率层是同一件事**，本文件把它抽出来：

    ∀ i ∈ 有限指标集, (1/n) Σ_{k<n} f i k ω → ∫ f i 0 ∂μ   （a.e.，同一个零测集之外）

三件器材：

* ★★★ `empAvg`：`n` 个样本的平均 `(n:ℝ)⁻¹ * ∑_{k<n} f k ω`；
* ★★★ `empAvg_tendsto_ae`：**通用单点 SLLN**（Etemadi 版 `strong_law_ae`），
  均值 = **积分本身**（不预设真律 —— 与 `EmpiricalConvergence.empFreq_tendsto_ae` 的区别在此）；
* ★★★ `empAvg_tendsto_ae_all`：**整族同时** a.e.（有限交：`Filter.eventually_all_finset` ＋ `Filter.eventually_all`）；
* ★★★ `exists_uniform_N_of_finite`：把「每个指标各取自己的 `N`」合成**统一 `N`**
  （有限指标集上的 `Finset.sup'`）—— 这一步是三条升级里**共同的**技术核心。

## 诚实边界

| 条目 | 状态 |
|---|---|
| 「样本 iid ＋ 均值是给定的理论值」 | ⚠️ **假设**（`hint`／`hindep`／`hident` ／ 应用侧的 `hmean`） |
| 单点 a.e. 收敛 | ✅ **本文件**（`strong_law_ae`） |
| 整族同时 a.e. 收敛 | ✅ **本文件**（有限交；`X` 有限 ⇒ 指标集有限是关键） |
| 统一 `N` | ✅ **本文件**（`exists_uniform_N_of_finite`） |
-/

noncomputable section

open Filter MeasureTheory ProbabilityTheory

open scoped Topology ENNReal

namespace Phylo.Stat.AESampling

variable {Ω₀ : Type*} [MeasurableSpace Ω₀]

/-- ★★★ **`n` 个样本的平均**：`(n:ℝ)⁻¹ * ∑_{k<n} f k ω`。

⚠️ 与 `EmpiricalConvergence.empFreq` 的定义**逐字同形**（那里要求 `f k ω = ind (ω k) S hS q`）；
本定义对**任意**实值族 `f` 都可用，故三条升级（位点 / 相异度 / 似然）共用。 -/
noncomputable def empAvg (f : ℕ → (ℕ → Ω₀) → ℝ) (n : ℕ) (ω : ℕ → Ω₀) : ℝ :=
  (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, f k ω

omit [MeasurableSpace Ω₀] in
/-- 空样本：`empAvg 0 = 0`（约定 `(0 : ℝ)⁻¹ = 0`）。 -/
theorem empAvg_zero (f : ℕ → (ℕ → Ω₀) → ℝ) (ω : ℕ → Ω₀) : empAvg f 0 ω = 0 := by
  simp [empAvg]

/-- ★★★ **通用单点强大数定律**：iid 样本平均 a.e. 收敛到**它自己的均值**。

★ 与 `EmpiricalConvergence.empFreq_tendsto_ae` 的区别：那里均值被要求**等于某个 `MSCFreq` 的频率**
（`hmean : ∫ … = m.freq.p S hS q`）；本定理**不预设真律**，故可用于 `SiteSupport`（真律是 `MSCSite`）、
`Dissimilarity`（真律是 `NJstData`）、`MLProblem`（真律是 `θ₀`）三条线。
证明 = 同一步 `strong_law_ae`（Etemadi 版，只需**两两**独立 ＋ 同分布 ＋ `Integrable`）。 -/
theorem empAvg_tendsto_ae (f : ℕ → (ℕ → Ω₀) → ℝ) (μ : Measure (ℕ → Ω₀))
    [IsProbabilityMeasure μ]
    (hint : Integrable (f 0) μ)
    (hindep : iIndepFun f μ)
    (hident : ∀ i, IdentDistrib (f i) (f 0) μ μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => empAvg f n ω) atTop (𝓝 (∫ ω, f 0 ω ∂μ)) := by
  have h := strong_law_ae (μ := μ) (E := ℝ) f hint
    (fun i j hij => hindep.indepFun hij) hident
  filter_upwards [h] with ω hω
  simpa only [empAvg, smul_eq_mul] using hω

/-- ★★★ **整族同时 a.e. 收敛**（**有限**指标集 `ι` 上的交）。

`X` 有限 ⇒ 所有用到的指标集（4-元集 × split ／ 叶对 ／ 有限模型类）都有限 ⇒ 这一步总可用。 -/
theorem empAvg_tendsto_ae_all {ι : Type*} [Fintype ι]
    (F : ι → ℕ → (ℕ → Ω₀) → ℝ) (μ : Measure (ℕ → Ω₀)) [IsProbabilityMeasure μ]
    (hint : ∀ i, Integrable (F i 0) μ)
    (hindep : ∀ i, iIndepFun (F i) μ)
    (hident : ∀ i, ∀ k, IdentDistrib (F i k) (F i 0) μ μ) :
    ∀ᵐ ω ∂μ, ∀ i : ι, Tendsto (fun n => empAvg (F i) n ω) atTop
      (𝓝 (∫ ω, F i 0 ω ∂μ)) := by
  have key : ∀ᵐ ω ∂μ, ∀ i ∈ (Finset.univ : Finset ι),
      Tendsto (fun n => empAvg (F i) n ω) atTop (𝓝 (∫ ω, F i 0 ω ∂μ)) := by
    refine (Filter.eventually_all_finset _).mpr ?_
    intro i _
    exact empAvg_tendsto_ae (F i) μ (hint i) (hindep i) (hident i)
  filter_upwards [key] with ω hω i
  exact hω i (Finset.mem_univ i)

/-- ★★ 同一事实的「最终 `ε`-接近」形式（**每个**指标各取自己的 `N`）。 -/
theorem empAvg_eventually_close_ae_all {ι : Type*} [Fintype ι]
    (F : ι → ℕ → (ℕ → Ω₀) → ℝ) (μ : Measure (ℕ → Ω₀)) [IsProbabilityMeasure μ]
    (hint : ∀ i, Integrable (F i 0) μ)
    (hindep : ∀ i, iIndepFun (F i) μ)
    (hident : ∀ i, ∀ k, IdentDistrib (F i k) (F i 0) μ μ) :
    ∀ᵐ ω ∂μ, ∀ i : ι, ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ n ≥ N, |empAvg (F i) n ω - ∫ ω, F i 0 ω ∂μ| < ε := by
  filter_upwards [empAvg_tendsto_ae_all F μ hint hindep hident] with ω hω
  intro i ε hε
  exact Metric.tendsto_atTop.mp (hω i) ε hε

/-- ★★★ **有限指标集上的统一 `N`**：若每个指标 `i` 各有一个 `N i` 使 `P i n` 对 `n ≥ N i` 成立，
则存在**统一**的 `N`（取 `max (sup N) 1`，顺带保证 `N ≥ 1`）使
`∀ n ≥ N, ∀ i, P i n`。

这是三条 a.e. 升级里**共同的**技术核心：`FreqClose`／`SiteClose`／`DissClose` 都是
「对所有指标同时 `ε`-接近」，而 SLLN 只逐指标给 `N`。 -/
theorem exists_uniform_N_of_finite {ι : Type*} [Fintype ι] {P : ι → ℕ → Prop}
    (h : ∀ i, ∃ N : ℕ, ∀ n ≥ N, P i n) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ n ≥ N, ∀ i, P i n := by
  classical
  choose N hN using h
  refine ⟨max (Finset.univ.sup N) 1, le_max_right _ _, fun n hn i => ?_⟩
  exact hN i n (le_trans (le_trans (Finset.le_sup (Finset.mem_univ i)) (le_max_left _ 1)) hn)

end Phylo.Stat.AESampling
