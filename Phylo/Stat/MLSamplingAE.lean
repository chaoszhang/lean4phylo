/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.Stat.AESampling
import Phylo.Stat.MLIdentifiability

/-!
# `Phylo.Stat.MLSamplingAE` —— **ML 一致性的 a.e. 版大数定律**

`Phylo/Stat/MLIdentifiability.lean` 把「观测得分 + 大数定律」公理化成 `MLProblem.converges`，
其形状是**确定性**的 `∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ t, |obs n t - expected t| < ε`
—— **没有概率空间，所以它证不出来**。本文件给出它**独立的概率版**（W20 任务 A③）。

## ★ 与另外两条（ASTRAL／简约／NJst）的关键**结构差异**

`MSCSampling`／`SiteSampling`／`USTARSampling` 都是「**跨律**量化」（`emp` 的 `converges` 对**每个**律
分别断言），故需要一个**更窄**的「真律固定版」`…Fixed` 结构。而

    structure MLProblem (T) where truth : T ; expected : T → ℝ ; obs : ℕ → T → ℝ ; converges : …

**已经**是「真律固定版」：它的 `converges` **只**谈本问题自己的 `obs`／`expected`，
**没有**跨律量化。⇒ ★★ 本文件**不引入新结构**（旧结构**一字不动** ✓），
而是直接证明 ★★★ **「存在真概率空间，a.e. 地产生一个 `MLProblem` 居民」**：

    exists_mlProblem_ae   ：∀ᵐ ω, ∃ P : MLProblem T, P.truth = θ₀ ∧ P.expected = expected
                                     ∧ ∀ n t, P.obs n t = empObs n ω t
    ml_statisticallyConsistent_ae ：∀ᵐ ω, ∃ N, ∀ n ≥ N, Er (经验得分截面) = θ₀

即 **`MLProblem.converges` 那条公理被数据（几乎必然地）满足** ⇒ 再把库内既有的
`ml_statisticallyConsistent`（`exists_gap` ＋ `argmax_eq_truth_of_close` 两步）套上去。

## 诚实边界

| 条目 | 状态 |
|---|---|
| 「位点 iid、且均值是期望得分 `expected`」 | ⚠️ **假设**（`hint`／`hindep`／`hident`／`hmean`） |
| 「期望得分在真树处唯一最大」（**可识别性**） | ⚠️ **假设**（`hident'`；Chang 1996／Rogers 1997 的输入） |
| 「估计量在每个样本上取观测得分的 argmax」 | ⚠️ **假设**（`hEr`；算法的定义侧） |
| **统一 `N`**（`|obs - expected| < ε` 形式） | ✅ **本文件**（`AESampling.exists_uniform_N_of_finite`） |
| `MLProblem.converges`（确定性公理） | ✅ **本文件**：a.e. 地被**满足**（`exists_mlProblem_ae`），**不是**它的推论 |
| 有限样本下 ML 可选错树 | ✅ 库内已有（★B `ml_finite_sample_not_true`），不受本文件影响 |
-/

noncomputable section

open Filter MeasureTheory ProbabilityTheory

open scoped Topology ENNReal

namespace Phylo.Stat.MLSamplingAE

open Phylo.Stat.MLIdentifiability

open Phylo.Stat.AESampling
  (empAvg empAvg_eventually_close_ae_all exists_uniform_N_of_finite)

universe u

variable {T : Type u} [Fintype T]
variable {Ω₀ : Type*} [MeasurableSpace Ω₀]

/-- **单个位点（数据点）在候选 `t` 上的得分**（`Ω₀` = 单位点的空间）。 -/
abbrev ScoreFun (T : Type*) (Ω₀ : Type*) : Type _ := Ω₀ → T → ℝ

/-- `n` 个位点的**经验得分**（逐候选取样本平均）。 -/
noncomputable def empObs (ind : ScoreFun T Ω₀) (n : ℕ) (ω : ℕ → Ω₀) (t : T) : ℝ :=
  empAvg (fun k (ω : ℕ → Ω₀) => ind (ω k) t) n ω

/-- ★★★ **`MLProblem.converges` 形式的几乎必然收敛**（**统一的 `N`**）：
`∀ᵐ ω, ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ t, |empObs n ω t − expected t| < ε`。

这正是 `MLProblem.converges`（对固定 `truth`／`expected`）的**几乎必然版**。
指标集取候选空间 `T`（**有限** ⇒ 可有限交、可取下确界）。 -/
theorem empObs_eventually_close_ae (ind : ScoreFun T Ω₀) (expected : T → ℝ)
    (μ : Measure (ℕ → Ω₀)) [IsProbabilityMeasure μ]
    (hint : ∀ t : T, Integrable (fun ω : ℕ → Ω₀ => ind (ω 0) t) μ)
    (hindep : ∀ t : T, iIndepFun (fun k (ω : ℕ → Ω₀) => ind (ω k) t) μ)
    (hident : ∀ t : T, ∀ k, IdentDistrib (fun ω : ℕ → Ω₀ => ind (ω k) t)
      (fun ω : ℕ → Ω₀ => ind (ω 0) t) μ μ)
    (hmean : ∀ t : T, ∫ ω, ind (ω 0) t ∂μ = expected t) :
    ∀ᵐ ω ∂μ, ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ t : T,
      |empObs ind n ω t - expected t| < ε := by
  classical
  have hpt : ∀ᵐ ω ∂μ, ∀ t : T, ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N,
      |empAvg (fun k (ω : ℕ → Ω₀) => ind (ω k) t) n ω - expected t| < ε := by
    have hbase := empAvg_eventually_close_ae_all (ι := T)
      (fun t : T => fun k (ω : ℕ → Ω₀) => ind (ω k) t) μ
      (fun t => hint t) (fun t => hindep t) (fun t k => hident t k)
    filter_upwards [hbase] with ω hω t ε hε
    simpa only [hmean t] using hω t ε hε
  filter_upwards [hpt] with ω hω ε hε
  obtain ⟨N, _, hN⟩ := exists_uniform_N_of_finite (ι := T)
    (P := fun t n => |empAvg (fun k (ω : ℕ → Ω₀) => ind (ω k) t) n ω - expected t| < ε)
    (fun t => hω t ε hε)
  exact ⟨N, fun n hn t => by simpa only [empObs] using hN n hn t⟩

/-- ★★★ **公理被数据 a.e. 满足**：在 `empObs_eventually_close_ae` 的 a.e. 事件上，
经验得分产生一个真 `MLProblem` 居民（真律 `truth := θ₀`、期望得分 `:= expected`）。

★ 这是本子批「把公理变成数据几乎必然满足」的**那一步**，对应另外两条里的
`exists_…Fixed_ae`（本文件**不需要**新结构，见文件头）。 -/
theorem exists_mlProblem_ae (ind : ScoreFun T Ω₀) (θ₀ : T) (expected : T → ℝ)
    (μ : Measure (ℕ → Ω₀)) [IsProbabilityMeasure μ]
    (hint : ∀ t : T, Integrable (fun ω : ℕ → Ω₀ => ind (ω 0) t) μ)
    (hindep : ∀ t : T, iIndepFun (fun k (ω : ℕ → Ω₀) => ind (ω k) t) μ)
    (hident : ∀ t : T, ∀ k, IdentDistrib (fun ω : ℕ → Ω₀ => ind (ω k) t)
      (fun ω : ℕ → Ω₀ => ind (ω 0) t) μ μ)
    (hmean : ∀ t : T, ∫ ω, ind (ω 0) t ∂μ = expected t) :
    ∀ᵐ ω ∂μ, ∃ P : MLProblem T,
      P.truth = θ₀ ∧ P.expected = expected ∧
        ∀ n : ℕ, ∀ t : T, P.obs n t = empObs ind n ω t := by
  filter_upwards [empObs_eventually_close_ae ind expected μ hint hindep hident hmean] with ω hω
  exact ⟨{ truth := θ₀
           expected := expected
           obs := fun n t => empObs ind n ω t
           converges := fun ε hε => by
             obtain ⟨N, hN⟩ := hω ε hε
             exact ⟨N, fun n hn t => hN n hn t⟩ }, rfl, rfl, fun _ _ => rfl⟩

/-- ★★★ **ML 的几乎必然统计一致性**（本子批的概率层收口）：

在 iid 位点模型下，**几乎必然**地，取经验得分 argmax 的估计量 `Er` 在**足够多**位点后
输出真树 `θ₀`（**可识别性** `hident'` ＋ `argmax_eq_truth_of_close` 的稳定性）。

★ 假设面**不含**公理化的 `MLProblem.converges`（它由 `exists_mlProblem_ae` a.e. 地**满足**了）。 -/
theorem ml_statisticallyConsistent_ae (ind : ScoreFun T Ω₀) (θ₀ : T) (expected : T → ℝ)
    (μ : Measure (ℕ → Ω₀)) [IsProbabilityMeasure μ]
    (hint : ∀ t : T, Integrable (fun ω : ℕ → Ω₀ => ind (ω 0) t) μ)
    (hindep : ∀ t : T, iIndepFun (fun k (ω : ℕ → Ω₀) => ind (ω k) t) μ)
    (hident : ∀ t : T, ∀ k, IdentDistrib (fun ω : ℕ → Ω₀ => ind (ω k) t)
      (fun ω : ℕ → Ω₀ => ind (ω 0) t) μ μ)
    (hmean : ∀ t : T, ∫ ω, ind (ω 0) t ∂μ = expected t)
    (hident' : ∀ t : T, t ≠ θ₀ → expected t < expected θ₀)
    (Er : (T → ℝ) → T) (hEr : ∀ s : T → ℝ, ∀ t : T, s t ≤ s (Er s)) :
    ∀ᵐ ω ∂μ, ∃ N : ℕ, ∀ n ≥ N, Er (fun t : T => empObs ind n ω t) = θ₀ := by
  classical
  filter_upwards [exists_mlProblem_ae ind θ₀ expected μ hint hindep hident hmean] with ω hω
  obtain ⟨P, hP1, hP2, hP3⟩ := hω
  have hId : P.Identifiable := by
    intro t ht
    rw [hP2, hP1]
    exact hident' t (by rw [hP1] at ht; exact ht)
  have hmax : ∀ n : ℕ, ∀ t : T, P.obs n t ≤ P.obs n (Er fun t : T => empObs ind n ω t) := by
    intro n t
    rw [hP3 n t, hP3 n (Er fun t : T => empObs ind n ω t)]
    exact hEr (fun t : T => empObs ind n ω t) t
  obtain ⟨N, hN⟩ := P.ml_statisticallyConsistent hId
    (fun n => Er fun t : T => empObs ind n ω t) hmax
  exact ⟨N, fun n hn => by rw [← hP1]; exact hN n hn⟩

/-! ## 反空真（★ 派单要求）

本条**不引入新结构**（见文件头：`MLProblem` 本身已是「真律固定版」），故「新结构的居民」一栏无需新增；
但为免空真，仍给出**两条可检查的见证**：

1. ★★★ **`MLProblem` 有非退化居民** —— 直接引库内既有的
   `MLIdentifiability.twoTreeProblem` 与 `twoTreeProblem_identifiable`
   （带 `Identifiable`，即真树期望得分**唯一最大**）⇒ `exists_mlProblem_ae` 产出的结构**确实存在**；
2. ★★ **概率空间侧可满足** —— 取 `Ω₀ := PUnit`（单点空间）与单位测度，
   `ind` 取与 `t` 无关的常值函数 ⇒ 均值假设 `hmean` **成立**
   （`∫ _ , c ∂(Measure.dirac ()) = c`，`integral_dirac`）。

⚠️ **如实说明**：这里**没有**为「iid 假设束」写出一个完整的显式实例
（即同时满足 `hint`／`hindep`／`hident`／`hmean` 的具体四元组）——
库内 ASTRAL（`GeneTreeSamplingAE`）与 CASTER 用的是同一组假设，`MSCSamplingAE` 亦同，
故该假设束**不是**本条新引入的、也**不是**本条特有的空真风险；
若日后要机械化该见证，缺口在「常值族的 `iIndepFun`」（Mathlib 无 `iIndepFun_const`）。 -/

/-- ★★★ **反空真见证 1**：**存在**带 `Identifiable` 的 `MLProblem` 居民
（真树期望得分唯一最大）⇒ `exists_mlProblem_ae` 产出的结构不空。 -/
theorem mlSamplingAE_nonvacuous_identifiable :
    ∃ P : MLProblem TwoTree, P.Identifiable :=
  ⟨twoTreeProblem, twoTreeProblem_identifiable⟩

/-- ★★ **反空真见证 2**：单点空间上的单位测度是**概率测度**
（`Ω₀ = PUnit` ⇒ `ℕ → PUnit` 上的 Dirac 测度），且常值函数的积分就是该常值。 -/
theorem mlSamplingAE_space_nonvacuous :
    (IsProbabilityMeasure (Measure.dirac (fun _ : ℕ => PUnit.unit)) :
      Prop) ∧
    (∀ c : ℝ, ∫ _ : ℕ → PUnit, c ∂(Measure.dirac (fun _ : ℕ => PUnit.unit)) = c) :=
  ⟨inferInstance, fun c => integral_dirac (fun _ : ℕ → PUnit => c) _⟩

end Phylo.Stat.MLSamplingAE
