/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.Stat.EmpiricalConvergence
import Phylo.Stat.Parsimony
import Phylo.Stat.QuartetDecides

/-!
# `Phylo.Stat.SiteSamplingAE` —— **位点支持表层**的几乎必然大数定律（parsimony 的 a.e. 升级）

`Phylo/Stat/Parsimony.lean` 把「ISM 位点采样 + 大数定律」公理化成 `SiteSampling.converges`，
其形状是**确定性**的 `∀ M ε > 0, ∃ N, ∀ n ≥ N, SiteClose (emp M n) M.toSiteSupport ε`
—— **没有概率空间，所以它证不出来**。本文件给出它**独立的概率版**（W20 任务 A①，模板 = `Phylo/Stat/MSCSamplingAE.lean`）：

    SiteSampling                    （公理化，本文件**不动**）
      ↓ 换成「真律固定版」
    SiteSamplingFixed               （`converges` 只对**一条真律** `law` 断言）
      ↓ 由真概率空间上的强大数定律 ＋ 有限交 ＋ 有限上确界**实现**
    exists_siteSamplingFixed_ae     （★ 公理被数据**几乎必然**满足）
      ↓ 叠加库内既有的算法稳定性（`stable_argmax_site`）
    parsimony_statisticallyConsistent_ae ／ parsimony_iso_ae   （端到端 a.e.）

## 与 ASTRAL 那条链的关系（★ 层次差异，协调侧已提醒）

`MSCSamplingAE.SiteTable`／`empTable` 是 **quartet 频率表**层（要求「每个位点本身是一张频率表」：
非负 ＋ 求和为 1 ＋ 换向不变）。简约要的是 **`SiteSupport`** 层（只有 `cnt` 非负 ＋ 换向不变，
**没有**「求和为 1」）。故本文件**不是照抄**，而是**类比造**：

| 层 | ASTRAL（`MSCSamplingAE`） | 简约（本文件） |
|---|---|---|
| 位点函数 | `SiteFun` ＋ `SiteTable`（3 条） | `SiteFun` ＋ `SupportTable`（2 条，**去掉求和为 1**） |
| 真律 | `MSCFreq`（频率表） | `MSCSite`（支持表 ＋ 真树） |
| 经验表 | `empTable : QuartetFreq` | `empSupport : SiteSupport` |
| 收敛谓词 | `FreqClose` | `SiteClose` |

★ **可复用的关键**：`SiteSupport.cnt : (S) → hS → Split ↥S → ℝ` 与 `SiteFun` 的逐点形状**完全相同**
⇒ §1 的通用 SLLN 直接吃 `ind := fun ω S hS q => (D (ω)).cnt S hS q`。

## 本文件交付

* ★★★ `empFreq_tendsto_ae_integral`：**通用单点 SLLN**（均值 = 积分本身，**不预设真律**）——
  `EmpiricalConvergence.empFreq_tendsto_ae` 要求均值等于某个 `MSCFreq` 的频率，本文件把它解放出来；
* ★★★ `empFreq_tendsto_ae_all_integral`：**整张表同时** a.e. 收敛（有限交）；
* ★★ `empSupport`：第 `n` 个样本的**经验支持表**（真正的 `SiteSupport`）；
* ★★★ `empSupport_eventually_close_ae`：**统一的 `N`** —— `SiteSampling.converges` 那条确定性公理的
  **几乎必然版**（共同 `N` 由有限指标集上的 `sup'` 取到）。

## 诚实边界（逐条）

| 条目 | 状态 |
|---|---|
| 「位点 iid、且均值是真支持表 `M.cnt`」 | ⚠️ **仍然是假设**（`hint`／`hindep`／`hident`／`hmean`） |
| 「每个位点的 `cnt` 非负 ＋ 换向不变」 | ⚠️ **假设**（`SupportTable`） |
| **整张表同时** a.e. 收敛 | ✅ **本文件**（有限交） |
| **统一的 `N`**（`SiteClose` 形式） | ✅ **本文件**（有限指标集上取 `sup'`） |
| `SiteSampling.converges`（确定性公理） | ⚠️ **仍是公理化的**；本文件给的是**真律固定版** `SiteSamplingFixed` 的 a.e. 实现，**不是**它的推论 |
-/

noncomputable section

open Filter MeasureTheory ProbabilityTheory

open scoped Topology ENNReal

namespace Phylo.Stat.SiteSamplingAE

open Phylo.Stat.EmpiricalConvergence (SiteFun empFreq)

universe u v

variable {X : Type*} [Fintype X] [DecidableEq X]
variable {Ω₀ : Type*} [MeasurableSpace Ω₀]

/-- 4-元集与 split 的**指标集**（`X` 有限 ⇒ 有限）。 -/
abbrev QuartetIndex (X : Type*) [Fintype X] [DecidableEq X] : Type _ :=
  Σ S : {S : Finset X // S.card = 4}, Split ↥(S : Finset X)

variable (ind : SiteFun X Ω₀)

/-! ## 1. ★★★ 通用单点 SLLN（均值 = 积分本身） -/

/-- ★★★ **通用单点强大数定律**：`ind` 的 iid 样本平均 a.e. 收敛到**它自己的均值** `∫ ω, ind (ω 0) …`。

★ 与 `EmpiricalConvergence.empFreq_tendsto_ae` 的区别：那里均值被要求**等于某个 `MSCFreq` 的频率**
（`hmean : ∫ … = m.freq.p S hS q`）；本定理**不预设真律**，故可直接用于 `SiteSupport` 层
（真律是 `MSCSite`，不是 `MSCFreq`）。证明 = 与那里**同一步**（`strong_law_ae`），只是不再改写目标。 -/
theorem empFreq_tendsto_ae_integral (μ : Measure (ℕ → Ω₀)) [IsProbabilityMeasure μ]
    (S : Finset X) (hS : S.card = 4) (q : Split ↥S)
    (hint : Integrable (fun ω : ℕ → Ω₀ => ind (ω 0) S hS q) μ)
    (hindep : iIndepFun (fun i (ω : ℕ → Ω₀) => ind (ω i) S hS q) μ)
    (hident : ∀ i, IdentDistrib (fun ω : ℕ → Ω₀ => ind (ω i) S hS q)
      (fun ω : ℕ → Ω₀ => ind (ω 0) S hS q) μ μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => empFreq ind n ω S hS q) atTop
      (𝓝 (∫ ω, ind (ω 0) S hS q ∂μ)) := by
  have h := strong_law_ae (μ := μ) (E := ℝ)
    (fun i (ω : ℕ → Ω₀) => ind (ω i) S hS q) hint
    (fun i j hij => hindep.indepFun hij) hident
  filter_upwards [h] with ω hω
  simpa only [empFreq, smul_eq_mul] using hω

/-! ## 2. ★★★ 整张表的几乎必然收敛（有限交） -/

/-- ★★★ **整张表同时 a.e. 收敛**：对**所有** 4-元集 `S` 与**所有**有向 split `q`，
**同时**（同一个零测集之外）收敛到各自的均值。

证明 = §1 的单点结果在**有限**指标集上取交（`Filter.eventually_all_finset` ＋ `Filter.eventually_all`）。 -/
theorem empFreq_tendsto_ae_all_integral (μ : Measure (ℕ → Ω₀)) [IsProbabilityMeasure μ]
    (hint : ∀ (S : Finset X) (hS : S.card = 4) (q : Split ↥S),
      Integrable (fun ω : ℕ → Ω₀ => ind (ω 0) S hS q) μ)
    (hindep : ∀ (S : Finset X) (hS : S.card = 4) (q : Split ↥S),
      iIndepFun (fun i (ω : ℕ → Ω₀) => ind (ω i) S hS q) μ)
    (hident : ∀ (S : Finset X) (hS : S.card = 4) (q : Split ↥S), ∀ i,
      IdentDistrib (fun ω : ℕ → Ω₀ => ind (ω i) S hS q)
        (fun ω : ℕ → Ω₀ => ind (ω 0) S hS q) μ μ) :
    ∀ᵐ ω ∂μ, ∀ (S : Finset X) (hS : S.card = 4) (q : Split ↥S),
      Tendsto (fun n => empFreq ind n ω S hS q) atTop (𝓝 (∫ ω, ind (ω 0) S hS q ∂μ)) := by
  have key : ∀ᵐ ω ∂μ, ∀ S ∈ (Finset.univ.filter (fun S : Finset X => S.card = 4)),
      ∀ (hS : S.card = 4) (q : Split ↥S),
        Tendsto (fun n => empFreq ind n ω S hS q) atTop (𝓝 (∫ ω, ind (ω 0) S hS q ∂μ)) := by
    refine (Filter.eventually_all_finset _).mpr ?_
    intro S _
    refine (Filter.eventually_all).mpr ?_
    intro hS4
    refine (Filter.eventually_all).mpr ?_
    intro q
    exact empFreq_tendsto_ae_integral ind μ S hS4 q
      (hint S hS4 q) (hindep S hS4 q) (hident S hS4 q)
  filter_upwards [key] with ω hω S hS q
  exact hω S (Finset.mem_filter.mpr ⟨Finset.mem_univ S, hS⟩) hS q

/-- ★★ 同一事实的「最终 `ε`-接近」形式（**每个** `(S,q)` 各取自己的 `N`）。 -/
theorem empFreq_eventually_close_ae_all_integral (μ : Measure (ℕ → Ω₀))
    [IsProbabilityMeasure μ]
    (hint : ∀ (S : Finset X) (hS : S.card = 4) (q : Split ↥S),
      Integrable (fun ω : ℕ → Ω₀ => ind (ω 0) S hS q) μ)
    (hindep : ∀ (S : Finset X) (hS : S.card = 4) (q : Split ↥S),
      iIndepFun (fun i (ω : ℕ → Ω₀) => ind (ω i) S hS q) μ)
    (hident : ∀ (S : Finset X) (hS : S.card = 4) (q : Split ↥S), ∀ i,
      IdentDistrib (fun ω : ℕ → Ω₀ => ind (ω i) S hS q)
        (fun ω : ℕ → Ω₀ => ind (ω 0) S hS q) μ μ) :
    ∀ᵐ ω ∂μ, ∀ (S : Finset X) (hS : S.card = 4) (q : Split ↥S), ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ n ≥ N, |empFreq ind n ω S hS q - ∫ ω, ind (ω 0) S hS q ∂μ| < ε := by
  filter_upwards [empFreq_tendsto_ae_all_integral ind μ hint hindep hident] with ω hω
  intro S hS q ε hε
  exact Metric.tendsto_atTop.mp (hω S hS q) ε hε

/-! ## 3. ★★ 位点支持层的假设面（**比 ASTRAL 的 `SiteTable` 少一条**：无「求和为 1」） -/

/-- **每个位点的支持计数是非负且换向不变的**（`SiteSupport` 的两条字段对**样本**成立）。

★ 比 `MSCSamplingAE.SiteTable` **少一条** `sum_one` —— 因为 `SiteSupport` 没有「求和为 1」这条字段
（支持计数不是频率表）。 -/
structure SupportTable (ind : SiteFun X Ω₀) : Prop where
  nonneg : ∀ (x : Ω₀) (S : Finset X) (hS : S.card = 4) (q : Split ↥S), 0 ≤ ind x S hS q
  swap : ∀ (x : Ω₀) (S : Finset X) (hS : S.card = 4) (q : Split ↥S),
    ind x S hS q.swap = ind x S hS q

/-- ★★ 第 `n` 个样本的**经验支持表**。两条字段由 `SupportTable` 推出。

⚠️ **技术性说明**（同 `MSCSamplingAE.empTable`）：对 `n = 0` **退化**（取真值 `M.toSiteSupport`），
因为 `empFreq 0 = 0`。数学上 `n = 0` 从不用到（`N ≥ 1` 由 `max · 1` 保证），
这样定义的好处是 `empSupport` **是全函数**。

★ `info` 字段取真值 `M.info`：`SiteClose` **只比较 `cnt`**，故 `info` 的取值不影响任何结论。 -/
noncomputable def empSupport {X : Type u} [Fintype X] [DecidableEq X] {Ω₀ : Type*}
    [MeasurableSpace Ω₀] (ind : SiteFun X Ω₀) (h : SupportTable ind) (M : MSCSite.{u, v} X)
    (n : ℕ) (ω : ℕ → Ω₀) : SiteSupport X where
  info S hS := M.info S hS
  cnt S hS q := if n = 0 then M.cnt S hS q else empFreq ind n ω S hS q
  cnt_nonneg S hS q := by
    by_cases hn : n = 0
    · simp only [hn, ↓reduceIte]
      exact M.cnt_nonneg S hS q
    · simp only [hn, ↓reduceIte, empFreq]
      exact mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => h.nonneg (ω i) S hS q)
  cnt_swap S hS q := by
    by_cases hn : n = 0
    · simp only [hn, ↓reduceIte]
      exact M.cnt_swap S hS q
    · simp only [hn, ↓reduceIte, empFreq]
      congr 1
      exact Finset.sum_congr rfl fun i _ => h.swap (ω i) S hS q

/-! ## 4. ★★★ **统一的 `N`**：`SiteSampling.converges` 的几乎必然版 -/

/-- ★★★ **`SiteClose` 形式的几乎必然收敛**（**统一的 `N`**）：
`∀ᵐ ω, ∀ ε > 0, ∃ N, ∀ n ≥ N, SiteClose (empSupport n ω) M.toSiteSupport ε`。

这正是 `Parsimony.lean` 里那条**确定性**公理 `SiteSampling.converges`（对固定真律 `M`）的
**几乎必然版**：区别只在于多了一个 `ω`（概率空间）与「共同 `N` 由有限指标集上的 `sup'` 取得」。

⚠️ 本定理**不是** `SiteSampling.converges` 的推论（后者是确定性的 `∃ N`，没有概率空间）。 -/
theorem empSupport_eventually_close_ae {X : Type u} [Fintype X] [DecidableEq X]
    {Ω₀ : Type*} [MeasurableSpace Ω₀] (ind : SiteFun X Ω₀) (h : SupportTable ind)
    (M : MSCSite.{u, v} X) (μ : Measure (ℕ → Ω₀)) [IsProbabilityMeasure μ]
    (hint : ∀ (S : Finset X) (hS : S.card = 4) (q : Split ↥S),
      Integrable (fun ω : ℕ → Ω₀ => ind (ω 0) S hS q) μ)
    (hindep : ∀ (S : Finset X) (hS : S.card = 4) (q : Split ↥S),
      iIndepFun (fun i (ω : ℕ → Ω₀) => ind (ω i) S hS q) μ)
    (hident : ∀ (S : Finset X) (hS : S.card = 4) (q : Split ↥S), ∀ i,
      IdentDistrib (fun ω : ℕ → Ω₀ => ind (ω i) S hS q)
        (fun ω : ℕ → Ω₀ => ind (ω 0) S hS q) μ μ)
    (hmean : ∀ (S : Finset X) (hS : S.card = 4) (q : Split ↥S),
      ∫ ω, ind (ω 0) S hS q ∂μ = M.cnt S hS q) :
    ∀ᵐ ω ∂μ, ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N,
      SiteClose (empSupport ind h M n ω) M.toSiteSupport ε := by
  classical
  -- 先把目标改写成「逐 `(S,q)` 各取自己的 `N`」的形式（均值换成 `M.cnt`）
  have hpt : ∀ᵐ ω ∂μ, ∀ (S : Finset X) (hS : S.card = 4) (q : Split ↥S), ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ n ≥ N, |empFreq ind n ω S hS q - M.cnt S hS q| < ε := by
    filter_upwards [empFreq_eventually_close_ae_all_integral ind μ hint hindep hident]
      with ω hω
    intro S hS q ε hε
    simpa only [hmean S hS q] using hω S hS q ε hε
  filter_upwards [hpt] with ω hω
  intro ε hε
  let N : QuartetIndex X → ℕ := fun i => Classical.choose (hω i.1.1 i.1.2 i.2 ε hε)
  refine ⟨max (Finset.univ.sup N) 1, fun n hn S hS q => ?_⟩
  have hN := Classical.choose_spec (hω S hS q ε hε)
  have hle : N ⟨⟨S, hS⟩, q⟩ ≤ max (Finset.univ.sup N) 1 :=
    le_trans (Finset.le_sup (Finset.mem_univ _)) (le_max_left _ 1)
  have hn0 : n ≠ 0 := by
    have : 1 ≤ n := le_trans (le_max_right (Finset.univ.sup N) 1) hn
    omega
  have := hN n (le_trans hle hn)
  simpa only [SiteClose, empSupport, hn0, ↓reduceIte] using this

/-! ## 5. ★★★ 把公理化的采样**在几乎必然意义下实现**

`Parsimony.lean` 的 `SiteSampling.emp` 依赖真律 `M`（2026-10-09 已修正，并给出居民
`siteSampling_nonempty`），但 `converges` 仍是**确定性公理**、对**每个**律分别断言。
本节给的是**更窄**的一条路子：把**真律固定下来**（与 `MSCSamplingAE.MSCSamplingFixed` 同构）：

    structure SiteSamplingFixed (X) where
      law : MSCSite X
      emp : ℕ → SiteSupport X
      converges : ∀ ε > 0, ∃ N, ∀ n ≥ N, SiteClose (emp n) law.toSiteSupport ε

本节的 ★★★ `exists_siteSamplingFixed_ae` 证明：**在 §4 的 a.e. 事件上，经验支持表**正是这样一个
结构的居民 —— 即**那条公理被数据本身（几乎必然地）满足**。再叠加库内既有的算法稳定性
（`stable_argmax_site`），得到 ★★★ **parsimony 的几乎必然统计一致性**。 -/

/-- ★★★ **真律固定版的一致性结构**：`emp` 与 `converges` 都**只对该律**断言
（与 `SiteSampling` 的区别：那里 `emp` 对**每个**律分别给出数据，这里只固定**一条**真律）。 -/
structure SiteSamplingFixed (X : Type u) [Fintype X] [DecidableEq X] where
  /-- **真实模型**。 -/
  law : MSCSite.{u, v} X
  /-- 经验支持表序列。 -/
  emp : ℕ → SiteSupport X
  /-- ★ **大数定律**（只对 `law`）。 -/
  converges : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, SiteClose (emp n) law.toSiteSupport ε

/-- ★ 反空真见证：`SiteSamplingFixed` **非空**（理想样本 `emp n := law.toSiteSupport`）。
★ 与 `Parsimony.siteSampling_nonempty` 同一构造，故本节的 a.e. 定理**不是空真的**。 -/
theorem siteSamplingFixed_nonempty (X : Type u) [Fintype X] [DecidableEq X]
    (M : MSCSite.{u, v} X) : Nonempty (SiteSamplingFixed.{u, v} X) :=
  ⟨{ law := M
     emp := fun _ => M.toSiteSupport
     converges := fun ε hε =>
       ⟨0, fun _ _ S hS q => by
         show |M.toSiteSupport.cnt S hS q - M.toSiteSupport.cnt S hS q| < ε
         rw [sub_self, abs_zero]
         exact hε⟩ }⟩

/-- ★★★ **公理化的采样结构被数据 a.e. 实现**：在 `empSupport_eventually_close_ae` 的
a.e. 事件上，经验支持表构成一个 `SiteSamplingFixed`（真律 `= M`）。 -/
theorem exists_siteSamplingFixed_ae {X : Type u} [Fintype X] [DecidableEq X]
    {Ω₀ : Type*} [MeasurableSpace Ω₀] (ind : SiteFun X Ω₀) (h : SupportTable ind)
    (M : MSCSite.{u, v} X) (μ : Measure (ℕ → Ω₀)) [IsProbabilityMeasure μ]
    (hint : ∀ (S : Finset X) (hS : S.card = 4) (q : Split ↥S),
      Integrable (fun ω : ℕ → Ω₀ => ind (ω 0) S hS q) μ)
    (hindep : ∀ (S : Finset X) (hS : S.card = 4) (q : Split ↥S),
      iIndepFun (fun i (ω : ℕ → Ω₀) => ind (ω i) S hS q) μ)
    (hident : ∀ (S : Finset X) (hS : S.card = 4) (q : Split ↥S), ∀ i,
      IdentDistrib (fun ω : ℕ → Ω₀ => ind (ω i) S hS q)
        (fun ω : ℕ → Ω₀ => ind (ω 0) S hS q) μ μ)
    (hmean : ∀ (S : Finset X) (hS : S.card = 4) (q : Split ↥S),
      ∫ ω, ind (ω 0) S hS q ∂μ = M.cnt S hS q) :
    ∀ᵐ ω ∂μ, ∃ sm : SiteSamplingFixed.{u, v} X,
      sm.law = M ∧ ∀ n : ℕ, sm.emp n = empSupport ind h M n ω := by
  filter_upwards [empSupport_eventually_close_ae ind h M μ hint hindep hident hmean] with ω hω
  exact ⟨{ law := M, emp := fun n => empSupport ind h M n ω, converges := hω }, rfl, fun _ => rfl⟩

/-- ★★★ **parsimony 统计一致性（真律固定版）**：把 `Parsimony.parsimony_statisticallyConsistent`
里的 `sm : SiteSampling X` 换成 `SiteSamplingFixed X`，其余**逐字相同**。 -/
theorem parsimony_statisticallyConsistent_fixed {X : Type u} [Fintype X] [DecidableEq X]
    (sm : SiteSamplingFixed.{u, v} X)
    {E : SiteSupport X → QuartetTree.{u, v} X} (hE : ∀ D, IsParsimony D (E D))
    (hNE : ∃ q : QuartetChoice X, ¬ AgreesWith sm.law.q q) :
    ∃ N : ℕ, ∀ n ≥ N, AgreesWith sm.law.q (E (sm.emp n)).q := by
  classical
  obtain ⟨δ, hδ, hgap⟩ := sm.law.exists_gap hNE
  set M' : ℝ := 2 * (Fintype.card {S : Finset X // S.card = 4} : ℝ) + 1 with hMdef
  have hMpos : 0 < M' := by
    rw [hMdef]
    have : (0 : ℝ) ≤ (Fintype.card {S : Finset X // S.card = 4} : ℝ) := Nat.cast_nonneg _
    linarith
  obtain ⟨N, hN⟩ := sm.converges (δ / M') (div_pos hδ hMpos)
  refine ⟨N, fun n hn => ?_⟩
  refine stable_argmax_site (D := sm.emp n) sm.law hδ hgap ?_ ?_
  · simpa [hMdef] using hN n hn
  · exact (isParsimony_iff_supportMax (sm.emp n)).mp (hE (sm.emp n)) sm.law.asQuartetTree

/-- ★★★ **parsimony 的几乎必然统计一致性**（本子批的概率层收口）：

在 iid 位点模型下（§1–§3 的那组假设），**几乎必然**地，最简树型估计量 `E` 在**足够多的位点**后
逐 quartet 与真树一致 —— 即 **`SiteSampling.converges` 那条公理所承载的结论，在概率空间里
由强大数定律 ＋ 算法稳定性真正推出**。 -/
theorem parsimony_statisticallyConsistent_ae {X : Type u} [Fintype X] [DecidableEq X]
    {Ω₀ : Type*} [MeasurableSpace Ω₀] (ind : SiteFun X Ω₀) (h : SupportTable ind)
    (M : MSCSite.{u, v} X) (μ : Measure (ℕ → Ω₀)) [IsProbabilityMeasure μ]
    (hint : ∀ (S : Finset X) (hS : S.card = 4) (q : Split ↥S),
      Integrable (fun ω : ℕ → Ω₀ => ind (ω 0) S hS q) μ)
    (hindep : ∀ (S : Finset X) (hS : S.card = 4) (q : Split ↥S),
      iIndepFun (fun i (ω : ℕ → Ω₀) => ind (ω i) S hS q) μ)
    (hident : ∀ (S : Finset X) (hS : S.card = 4) (q : Split ↥S), ∀ i,
      IdentDistrib (fun ω : ℕ → Ω₀ => ind (ω i) S hS q)
        (fun ω : ℕ → Ω₀ => ind (ω 0) S hS q) μ μ)
    (hmean : ∀ (S : Finset X) (hS : S.card = 4) (q : Split ↥S),
      ∫ ω, ind (ω 0) S hS q ∂μ = M.cnt S hS q)
    {E : SiteSupport X → QuartetTree.{u, v} X} (hE : ∀ D, IsParsimony D (E D))
    (hNE : ∃ q : QuartetChoice X, ¬ AgreesWith M.q q) :
    ∀ᵐ ω ∂μ, ∃ N : ℕ, ∀ n ≥ N, AgreesWith M.q (E (empSupport ind h M n ω)).q := by
  filter_upwards [empSupport_eventually_close_ae ind h M μ hint hindep hident hmean] with ω hω
  exact parsimony_statisticallyConsistent_fixed
    ⟨M, fun n => empSupport ind h M n ω, hω⟩ hE hNE

/-- ★★★ **parsimony 的几乎必然**树层**统计一致性**（把 quartet 层升到**树同构**）：

把 `QuartetDecides.parsimony_iso` 的 `sm : SiteSampling X` 换成 a.e. 形态，
收口方式相同（`parsimony_statisticallyConsistent` ＋ ★★★ `QuartetDecidesTree`）。 -/
theorem parsimony_iso_ae {X : Type u} [Fintype X] [DecidableEq X]
    {Ω₀ : Type*} [MeasurableSpace Ω₀] (ind : SiteFun X Ω₀) (h : SupportTable ind)
    (M : MSCSite.{u, v} X) (hT : M.tree.IsBinary) (μ : Measure (ℕ → Ω₀))
    [IsProbabilityMeasure μ]
    (hint : ∀ (S : Finset X) (hS : S.card = 4) (q : Split ↥S),
      Integrable (fun ω : ℕ → Ω₀ => ind (ω 0) S hS q) μ)
    (hindep : ∀ (S : Finset X) (hS : S.card = 4) (q : Split ↥S),
      iIndepFun (fun i (ω : ℕ → Ω₀) => ind (ω i) S hS q) μ)
    (hident : ∀ (S : Finset X) (hS : S.card = 4) (q : Split ↥S), ∀ i,
      IdentDistrib (fun ω : ℕ → Ω₀ => ind (ω i) S hS q)
        (fun ω : ℕ → Ω₀ => ind (ω 0) S hS q) μ μ)
    (hmean : ∀ (S : Finset X) (hS : S.card = 4) (q : Split ↥S),
      ∫ ω, ind (ω 0) S hS q ∂μ = M.cnt S hS q)
    {E : SiteSupport X → QuartetTree.{u, v} X} (hE : ∀ D, IsParsimony D (E D))
    (hEbin : ∀ D, (E D).tree.IsBinary)
    (hNE : ∃ q : QuartetChoice X, ¬ AgreesWith M.q q) :
    ∀ᵐ ω ∂μ, ∃ N : ℕ, ∀ n ≥ N,
      Nonempty (Iso (E (empSupport ind h M n ω)).tree M.tree) := by
  filter_upwards [parsimony_statisticallyConsistent_ae ind h M μ hint hindep hident hmean hE hNE]
    with ω hω
  obtain ⟨N, hN⟩ := hω
  exact ⟨N, fun n hn =>
    QuartetDecidesTree X (E (empSupport ind h M n ω)) M.asQuartetTree (hEbin _) hT (hN n hn)⟩

end Phylo.Stat.SiteSamplingAE
