/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.Stat.EmpiricalConvergence
import Phylo.Stat.MSC
import Phylo.Stat.Stability

/-!
# `Phylo.Stat.MSCSamplingAE` —— **整张**经验 quartet 频率表的**几乎必然**收敛

`Phylo/Stat/MSC.lean` 第 **159–175** 行把「MSC 采样 + 大数定律」公理化成
`MSCSampling.converges`，其形状是**确定性**的
`∀ m ε > 0, ∃ N, ∀ n ≥ N, FreqClose (emp n) m.freq ε`
—— **没有概率空间，所以它证不出来**（W10d 也一字未改它）。

`Phylo/Stat/EmpiricalConvergence.lean`（W10d）已在**真概率空间**上给出**单个** `(S, q)` 的
几乎必然收敛。**本文件把它升到「整张表」**：对**所有** 4-元集 `S` 与**所有** split `q`
**同时**成立 —— 这一步只需**有限交**（`X` 有限 ⇒ 指标集有限），
是「统计一致性」在**概率空间**里的自然形态。

## 本文件交付

* ★★★ `empFreq_tendsto_ae_all`：`∀ᵐ ω ∂μ`，**对所有** `(S, hS, q)` 同时
  `empFreq n ω S hS q → m.freq.p S hS q`；
* ★★ `empFreq_eventually_close_ae_all`：同一事实的「最终 `ε`-接近」形式（每个 `(S,q)` 各取自己的 `N`）；
* ★★ `empTable`：第 `n` 个样本的**经验频率表**作为真正的 `QuartetFreq`（`n ≥ 1`；
  三条字段由「每个位点本身是一张频率表」这一**显式假设** `hind`/`hsum`/`hswap` 推出）；
* ★★★ `empTable_eventually_close_ae`：**统一的 `N`** ——
  `∀ᵐ ω, ∀ ε > 0, ∃ N, ∀ n ≥ N, FreqClose (empTable n ω) m.freq ε`，
  即 `MSCSampling.converges` 那条**确定性公理**的**几乎必然版**（共同 `N` 由有限指标集上的
  `Finset.sup'` 取到）。

## 诚实边界（逐条）

| 条目 | 状态 |
|---|---|
| 「单位点 iid、且其分布是 MSC 理论分布」 | ⚠️ **仍然是假设**（`hint`/`hindep`/`hident`/`hmean`，见 W10d 的缺口 K） |
| 「每个位点本身是一张 quartet 频率表」 | ⚠️ **假设**（`hind` 非负 / `hsum` 求和为 1 / `hswap` 换向不变） |
| **整张表同时** a.e. 收敛 | ✅ **本文件**（有限交） |
| **统一的 `N`**（`FreqClose` 形式） | ✅ **本文件**（有限指标集上取 `sup'`） |
| **公理化的采样结构被 a.e. 实现** | ✅ **本文件**（§4：`exists_mscSamplingFixed_ae`，真律固定版） |
| **ASTRAL 的 a.e. 统计一致性** | ✅ **本文件**（§4：由 SLLN ＋ 库内 `stable_argmax` 推出） |
| `MSCSampling.converges`（**旧**确定性公理） | ⚠️ **未改动**；本文件给出的是**真律固定版** `MSCSamplingFixed` 的 a.e. 实现，**不是**旧谓词的推论 |
| 一般 `n` 的方差、iid 空间的存在性 | ❌ 未做（W10d 的缺口 V / K） |
-/

noncomputable section

open Filter MeasureTheory ProbabilityTheory

open scoped Topology ENNReal

namespace Phylo.Stat.MSCSamplingAE

open Phylo.Stat.EmpiricalConvergence (SiteFun empFreq empFreq_tendsto_ae empFreq_eventually_close_ae)

variable {X : Type*} [Fintype X] [DecidableEq X]
variable {Ω₀ : Type*} [MeasurableSpace Ω₀]

/-- 4-元集与 split 的**指标集**（`X` 有限 ⇒ 有限）。 -/
abbrev QuartetIndex (X : Type*) [Fintype X] [DecidableEq X] : Type _ :=
  Σ S : {S : Finset X // S.card = 4}, Split ↥(S : Finset X)

variable (ind : SiteFun X Ω₀)

/-! ## 1. ★★★ 整张表的几乎必然收敛（有限交） -/

/-- ★★★ **整张经验 quartet 频率表的几乎必然收敛**：对**所有** 4-元集 `S` 与**所有**
有向 split `q`，**同时**（同一个零测集之外）收敛到 MSC 理论频率。

证明 = 把 W10d 的单点结果在**有限**指标集上取交（`Filter.eventually_all_finset` +
`Filter.eventually_all`）：`X` 有限 ⇒ 4-元集有限 ⇒ 每个 `↥S` 上的 `Split` 有限。 -/
theorem empFreq_tendsto_ae_all (m : MSCFreq X) (μ : Measure (ℕ → Ω₀)) [IsProbabilityMeasure μ]
    (hint : ∀ (S : Finset X) (hS : S.card = 4) (q : Split ↥S),
      Integrable (fun ω : ℕ → Ω₀ => ind (ω 0) S hS q) μ)
    (hindep : ∀ (S : Finset X) (hS : S.card = 4) (q : Split ↥S),
      iIndepFun (fun i (ω : ℕ → Ω₀) => ind (ω i) S hS q) μ)
    (hident : ∀ (S : Finset X) (hS : S.card = 4) (q : Split ↥S), ∀ i,
      IdentDistrib (fun ω : ℕ → Ω₀ => ind (ω i) S hS q)
        (fun ω : ℕ → Ω₀ => ind (ω 0) S hS q) μ μ)
    (hmean : ∀ (S : Finset X) (hS : S.card = 4) (q : Split ↥S),
      ∫ ω, ind (ω 0) S hS q ∂μ = m.freq.p S hS q) :
    ∀ᵐ ω ∂μ, ∀ (S : Finset X) (hS : S.card = 4) (q : Split ↥S),
      Tendsto (fun n => empFreq ind n ω S hS q) atTop (𝓝 (m.freq.p S hS q)) := by
  have key : ∀ᵐ ω ∂μ, ∀ S ∈ (Finset.univ.filter (fun S : Finset X => S.card = 4)),
      ∀ (hS : S.card = 4) (q : Split ↥S),
        Tendsto (fun n => empFreq ind n ω S hS q) atTop (𝓝 (m.freq.p S hS q)) := by
    refine (Filter.eventually_all_finset _).mpr ?_
    intro S hS
    refine (Filter.eventually_all).mpr ?_
    intro hS4
    refine (Filter.eventually_all).mpr ?_
    intro q
    exact empFreq_tendsto_ae ind m μ S hS4 q
      (hint S hS4 q) (hindep S hS4 q) (hident S hS4 q) (hmean S hS4 q)
  filter_upwards [key] with ω hω S hS q
  exact hω S (Finset.mem_filter.mpr ⟨Finset.mem_univ S, hS⟩) hS q

/-- ★★ 同一事实的「最终 `ε`-接近」形式（**每个** `(S,q)` 各取自己的 `N`）。 -/
theorem empFreq_eventually_close_ae_all (m : MSCFreq X) (μ : Measure (ℕ → Ω₀))
    [IsProbabilityMeasure μ]
    (hint : ∀ (S : Finset X) (hS : S.card = 4) (q : Split ↥S),
      Integrable (fun ω : ℕ → Ω₀ => ind (ω 0) S hS q) μ)
    (hindep : ∀ (S : Finset X) (hS : S.card = 4) (q : Split ↥S),
      iIndepFun (fun i (ω : ℕ → Ω₀) => ind (ω i) S hS q) μ)
    (hident : ∀ (S : Finset X) (hS : S.card = 4) (q : Split ↥S), ∀ i,
      IdentDistrib (fun ω : ℕ → Ω₀ => ind (ω i) S hS q)
        (fun ω : ℕ → Ω₀ => ind (ω 0) S hS q) μ μ)
    (hmean : ∀ (S : Finset X) (hS : S.card = 4) (q : Split ↥S),
      ∫ ω, ind (ω 0) S hS q ∂μ = m.freq.p S hS q) :
    ∀ᵐ ω ∂μ, ∀ (S : Finset X) (hS : S.card = 4) (q : Split ↥S), ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ n ≥ N, |empFreq ind n ω S hS q - m.freq.p S hS q| < ε := by
  filter_upwards [empFreq_tendsto_ae_all ind m μ hint hindep hident hmean] with ω hω
  intro S hS q ε hε
  exact Metric.tendsto_atTop.mp (hω S hS q) ε hε

/-! ## 2. ★★ 经验频率**表**（每个位点本身是一张频率表） -/

/-- **每个位点的观测本身就是一张 quartet 频率表**（概率性的三个条件，**显式假设**）。 -/
structure SiteTable (ind : SiteFun X Ω₀) : Prop where
  nonneg : ∀ (x : Ω₀) (S : Finset X) (hS : S.card = 4) (q : Split ↥S), 0 ≤ ind x S hS q
  sum_one : ∀ (x : Ω₀) (S : Finset X) (hS : S.card = 4), ∑ q : Split ↥S, ind x S hS q = 1
  swap : ∀ (x : Ω₀) (S : Finset X) (hS : S.card = 4) (q : Split ↥S),
    ind x S hS q.swap = ind x S hS q

/-- ★★ 第 `n` 个样本的**经验频率表**。三条字段由 `SiteTable` 推出。

⚠️ **技术性说明**：本定义对 `n = 0` **退化**（取先验 `m.freq`），
因为 `empFreq 0 = 0` 不是频率表（其 `∑_q = 0 ≠ 1`）。
数学上 `n = 0` 从不用到（`FreqClose` 形式里 `N ≥ 1` 由 `max · 1` 保证）；
这样定义的好处是 **`empTable` 是全函数**，陈述里不必传 `1 ≤ n` 的证明项。 -/
noncomputable def empTable (h : SiteTable ind) (m : MSCFreq X) (n : ℕ) (ω : ℕ → Ω₀) :
    QuartetFreq X where
  p S hS q := if n = 0 then m.freq.p S hS q else empFreq ind n ω S hS q
  p_nonneg S hS q := by
    by_cases hn : n = 0
    · simp only [hn, ↓reduceIte]
      exact m.freq.p_nonneg S hS q
    · simp only [hn, ↓reduceIte, empFreq]
      exact mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => h.nonneg (ω i) S hS q)
  p_sum_one S hS := by
    by_cases hn : n = 0
    · simp only [hn, ↓reduceIte]
      exact m.freq.p_sum_one S hS
    · have hn1 : 1 ≤ n := Nat.pos_of_ne_zero hn
      have hn0 : (n : ℝ) ≠ 0 := by
        have : (0 : ℝ) < n := by exact_mod_cast hn1
        exact ne_of_gt this
      simp only [hn, ↓reduceIte]
      show ∑ q : Split ↥S, empFreq ind n ω S hS q = 1
      simp only [empFreq]
      rw [← Finset.mul_sum, Finset.sum_comm]
      simp only [h.sum_one, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
      exact inv_mul_cancel₀ hn0
  p_swap S hS q := by
    by_cases hn : n = 0
    · simp only [hn, ↓reduceIte]
      exact m.freq.p_swap S hS q
    · simp only [hn, ↓reduceIte, empFreq]
      congr 1
      exact Finset.sum_congr rfl fun i _ => h.swap (ω i) S hS q

/-! ## 3. ★★★ **统一的 `N`**：`MSCSampling.converges` 的几乎必然版 -/

/-- ★★★ **`FreqClose` 形式的几乎必然收敛**（**统一的 `N`**）：
`∀ᵐ ω, ∀ ε > 0, ∃ N, ∀ n ≥ N, FreqClose (empTable n ω) m.freq ε`。

这正是 `MSC.lean` 里那条**确定性**公理 `MSCSampling.converges` 的**几乎必然版**：
区别只在于多了一个 `ω`（概率空间）与「共同 `N` 由有限指标集上的 `sup'` 取得」这一步。

⚠️ 本定理**不是** `MSCSampling.converges` 的推论，后者也**未改动**。 -/
theorem empTable_eventually_close_ae (h : SiteTable ind) (m : MSCFreq X)
    (μ : Measure (ℕ → Ω₀)) [IsProbabilityMeasure μ]
    (hint : ∀ (S : Finset X) (hS : S.card = 4) (q : Split ↥S),
      Integrable (fun ω : ℕ → Ω₀ => ind (ω 0) S hS q) μ)
    (hindep : ∀ (S : Finset X) (hS : S.card = 4) (q : Split ↥S),
      iIndepFun (fun i (ω : ℕ → Ω₀) => ind (ω i) S hS q) μ)
    (hident : ∀ (S : Finset X) (hS : S.card = 4) (q : Split ↥S), ∀ i,
      IdentDistrib (fun ω : ℕ → Ω₀ => ind (ω i) S hS q)
        (fun ω : ℕ → Ω₀ => ind (ω 0) S hS q) μ μ)
    (hmean : ∀ (S : Finset X) (hS : S.card = 4) (q : Split ↥S),
      ∫ ω, ind (ω 0) S hS q ∂μ = m.freq.p S hS q) :
    ∀ᵐ ω ∂μ, ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N,
      FreqClose (empTable ind h m n ω) m.freq ε := by
  classical
  -- 逐指标取 `N`，再用有限指标集上的 `sup'` 合成一个共同 `N`
  have hpt := empFreq_eventually_close_ae_all ind m μ hint hindep hident hmean
  filter_upwards [hpt] with ω hω
  intro ε hε
  -- 对每个指标 `i`，`Classical.choose` 出一个 `N i`
  let N : QuartetIndex X → ℕ := fun i =>
    Classical.choose (hω i.1.1 i.1.2 i.2 ε hε)
  refine ⟨max (Finset.univ.sup N) 1, fun n hn S hS q => ?_⟩
  have hN := Classical.choose_spec (hω S hS q ε hε)
  have hle : N ⟨⟨S, hS⟩, q⟩ ≤ max (Finset.univ.sup N) 1 :=
    le_trans (Finset.le_sup (Finset.mem_univ _)) (le_max_left _ 1)
  have hn0 : n ≠ 0 := by
    have : 1 ≤ n := le_trans (le_max_right (Finset.univ.sup N) 1) hn
    omega
  have := hN n (le_trans hle hn)
  simpa only [empTable, hn0, ↓reduceIte, FreqClose] using this

/-! ## 4. ★★★ 把公理化的采样**在几乎必然意义下实现**

`Phylo/Stat/SamplingAxiomVacuity.lean` 指出：`MSCSampling.converges` 的形状
（`emp` 不依赖真实律、却对**所有**律断言）使该结构**空**。修正的办法是把**真律固定下来**：

    structure MSCSamplingFixed (X) where
      law : MSCFreq X
      emp : ℕ → QuartetFreq X
      converges : ∀ ε > 0, ∃ N, ∀ n ≥ N, FreqClose (emp n) law.freq ε

本节的 ★★★ `exists_mscSamplingFixed_ae` 证明：**在 §3 的 a.e. 事件上，经验频率表**正是这样一个
结构的居民 —— 即**那条公理被数据本身（几乎必然地）满足**。再叠加库内既有的算法稳定性
（`Stability.stable_argmax`），得到 ★★★ **ASTRAL 的几乎必然统计一致性**。 -/

universe u v

/-- ★★★ **真律固定版的一致性结构**：`emp` 与 `converges` 都**只对该律**断言
（与 `SamplingAxiomVacuity.MSCSamplingLaw` 的区别：那里 `emp` 对**每个**律分别给出数据，
这里只固定**一条**真律）。 -/
structure MSCSamplingFixed (X : Type u) [Fintype X] [DecidableEq X] where
  /-- **真实律**。 -/
  law : MSCFreq.{u, v} X
  /-- 经验频率表序列。 -/
  emp : ℕ → QuartetFreq X
  /-- ★ **大数定律**（只对 `law`）。 -/
  converges : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, FreqClose (emp n) law.freq ε

/-- ★★★ **公理化的采样结构被数据 a.e. 实现**：在 `empTable_eventually_close_ae` 的
a.e. 事件上，经验频率表构成一个 `MSCSamplingFixed`（真律 `= m`）。 -/
theorem exists_mscSamplingFixed_ae {X : Type u} [Fintype X] [DecidableEq X]
    {Ω₀ : Type*} [MeasurableSpace Ω₀] (ind : SiteFun X Ω₀) (h : SiteTable ind)
    (m : MSCFreq.{u, v} X) (μ : Measure (ℕ → Ω₀)) [IsProbabilityMeasure μ]
    (hint : ∀ (S : Finset X) (hS : S.card = 4) (q : Split ↥S),
      Integrable (fun ω : ℕ → Ω₀ => ind (ω 0) S hS q) μ)
    (hindep : ∀ (S : Finset X) (hS : S.card = 4) (q : Split ↥S),
      iIndepFun (fun i (ω : ℕ → Ω₀) => ind (ω i) S hS q) μ)
    (hident : ∀ (S : Finset X) (hS : S.card = 4) (q : Split ↥S), ∀ i,
      IdentDistrib (fun ω : ℕ → Ω₀ => ind (ω i) S hS q)
        (fun ω : ℕ → Ω₀ => ind (ω 0) S hS q) μ μ)
    (hmean : ∀ (S : Finset X) (hS : S.card = 4) (q : Split ↥S),
      ∫ ω, ind (ω 0) S hS q ∂μ = m.freq.p S hS q) :
    ∀ᵐ ω ∂μ, ∃ sm : MSCSamplingFixed.{u, v} X,
      sm.law = m ∧ ∀ n : ℕ, sm.emp n = empTable ind h m n ω := by
  filter_upwards [empTable_eventually_close_ae ind h m μ hint hindep hident hmean] with ω hω
  exact ⟨{ law := m, emp := fun n => empTable ind h m n ω, converges := hω }, rfl, fun _ => rfl⟩

/-- ★★★ **ASTRAL 统计一致性（真律固定版）**：把 `Stability.astral_statisticallyConsistent`
里的 `sm : MSCSampling X` 换成 `MSCSamplingFixed X`，其余**逐字相同**。 -/
theorem astral_statisticallyConsistent_fixed {X : Type u} [Fintype X] [DecidableEq X]
    (sm : MSCSamplingFixed.{u, v} X)
    {E : QuartetFreq X → QuartetTree.{u, v} X} (hE : ∀ D, IsASTRAL D (E D))
    (hNE : ∃ q : QuartetChoice X, ¬ IsTrueChoice sm.law q) :
    ∃ N : ℕ, ∀ n ≥ N, IsTrueChoice sm.law (E (sm.emp n)).q := by
  classical
  obtain ⟨δ, hδ, hgap⟩ := exists_gap sm.law hNE
  set M : ℝ := 2 * (Fintype.card {S : Finset X // S.card = 4} : ℝ) + 1 with hMdef
  have hMpos : 0 < M := by
    rw [hMdef]
    have : (0 : ℝ) ≤ (Fintype.card {S : Finset X // S.card = 4} : ℝ) := Nat.cast_nonneg _
    linarith
  obtain ⟨N, hN⟩ := sm.converges (δ / M) (div_pos hδ hMpos)
  refine ⟨N, fun n hn => ?_⟩
  refine stable_argmax (D := sm.emp n) sm.law hδ hgap ?_ ?_
  · simpa [hMdef] using hN n hn
  · exact hE (sm.emp n) sm.law.toQuartetTree

/-- ★★★ **ASTRAL 的几乎必然统计一致性**（本子批的概率层收口）：

在 iid 位点模型下（W10d 的那组假设），**几乎必然**地，ASTRAL 型估计量 `E` 在**足够多的位点**后
逐 quartet 恢复真树的选择 —— 即 **`MSCSampling.converges` 那条公理所承载的结论，在概率空间里
由强大数定律 ＋ 算法稳定性真正推出**。 -/
theorem astral_statisticallyConsistent_ae {X : Type u} [Fintype X] [DecidableEq X]
    {Ω₀ : Type*} [MeasurableSpace Ω₀] (ind : SiteFun X Ω₀) (h : SiteTable ind)
    (m : MSCFreq.{u, v} X) (μ : Measure (ℕ → Ω₀)) [IsProbabilityMeasure μ]
    (hint : ∀ (S : Finset X) (hS : S.card = 4) (q : Split ↥S),
      Integrable (fun ω : ℕ → Ω₀ => ind (ω 0) S hS q) μ)
    (hindep : ∀ (S : Finset X) (hS : S.card = 4) (q : Split ↥S),
      iIndepFun (fun i (ω : ℕ → Ω₀) => ind (ω i) S hS q) μ)
    (hident : ∀ (S : Finset X) (hS : S.card = 4) (q : Split ↥S), ∀ i,
      IdentDistrib (fun ω : ℕ → Ω₀ => ind (ω i) S hS q)
        (fun ω : ℕ → Ω₀ => ind (ω 0) S hS q) μ μ)
    (hmean : ∀ (S : Finset X) (hS : S.card = 4) (q : Split ↥S),
      ∫ ω, ind (ω 0) S hS q ∂μ = m.freq.p S hS q)
    {E : QuartetFreq X → QuartetTree.{u, v} X} (hE : ∀ D, IsASTRAL D (E D))
    (hNE : ∃ q : QuartetChoice X, ¬ IsTrueChoice m q) :
    ∀ᵐ ω ∂μ, ∃ N : ℕ, ∀ n ≥ N, IsTrueChoice m (E (empTable ind h m n ω)).q := by
  filter_upwards [empTable_eventually_close_ae ind h m μ hint hindep hident hmean] with ω hω
  exact astral_statisticallyConsistent_fixed
    ⟨m, fun n => empTable ind h m n ω, hω⟩ hE hNE

end Phylo.Stat.MSCSamplingAE
