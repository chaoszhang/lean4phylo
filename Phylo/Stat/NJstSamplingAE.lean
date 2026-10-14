/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.Stat.AESampling
import Phylo.Stat.NJst

/-!
# `Phylo.Stat.NJstSamplingAE` —— **NJst（USTAR）的 a.e. 版大数定律**

`Phylo/Stat/NJst.lean` 把「USTAR 相异度的采样 + 大数定律」公理化成 `USTARSampling.converges`，
其形状是**确定性**的 `∀ M ε > 0, ∃ N, ∀ n ≥ N, DissClose (emp M n) M.δ ε`
—— **没有概率空间，所以它证不出来**。本文件给出它**独立的概率版**（W20 任务 A②）：

    USTARSampling                    （公理化，本文件**不动**）
      ↓ 换成「真律固定版」
    USTARSamplingFixed               （`converges` 只对**一条真律** `law` 断言）
      ↓ 由真概率空间上的强大数定律 ＋ 有限交 ＋ 有限上确界**实现**
    exists_ustarSamplingFixed_ae     （★ 公理被数据**几乎必然**满足）
      ↓ 套用 ADR Thm 4.1 的两步证明（SLLN ＋ 条件 (1)(2)）
    njst_statisticallyConsistent_ae  （端到端 a.e.）

## ★ 本文件**只**升级 SLLN；ADR 的条件 (1)(2) **仍是文献假设**（如实分开报告）

`njst_statisticallyConsistent` 的证明（照抄 ADR `:754–763`）只有两步：**SLLN** ＋「条件 (1)(2)」。
本文件把**第一步**的 `sm : USTARSampling` 换成 `USTARSamplingFixed`，而

* `ReturnsFittingTree E`（ADR Thm 4.1 条件 **(1)**）；
* `ContinuousAtBinaryTreeMetrics E`（ADR Thm 4.1 条件 **(2)**）

**原样保留为假设**（它们是**文献假设**，不是公理化的 SLLN）。⇒ 升级后本文件的定理假设面**不含**
`USTARSampling.converges`，但仍然**含** ADR 的条件 (1)(2) —— 这一点在报告里单独列出。

## 本文件交付

* ★★ `empDiss`：经验 USTAR 相异度（真正的 `Dissimilarity`；`n = 0` 退化取真值以保全函数）；
* ★★★ `empDiss_eventually_close_ae`：**统一的 `N`** —— `USTARSampling.converges` 那条确定性公理的 a.e. 版；
* ★★ `USTARSamplingFixed` ＋ ★ `ustarSamplingFixed_nonempty`（反空真见证）；
* ★★★ `exists_ustarSamplingFixed_ae`（公理被数据 a.e. 满足）；
* ★★★ `njst_statisticallyConsistent_fixed` ＋ `njst_statisticallyConsistent_ae`（端到端）。

## 诚实边界

| 条目 | 状态 |
|---|---|
| 「基因树 iid、且均值是真相异度 `M.δ`」 | ⚠️ **假设**（`hint`／`hindep`／`hident`／`hmean`） |
| 「样本相异度对称、零对角」 | ⚠️ **假设**（`DissTable`） |
| **统一 `N`**（`DissClose` 形式） | ✅ **本文件**（`AESampling.exists_uniform_N_of_finite`） |
| `USTARSampling.converges`（确定性公理） | ⚠️ **仍是公理化的**；本文件给的是**真律固定版**的 a.e. 实现，**不是**它的推论 |
| ADR 条件 (1)(2) | ⚠️ **仍是文献假设**（未 discharge；如实分开报告） |
-/

noncomputable section

open Filter MeasureTheory ProbabilityTheory

open scoped Topology ENNReal

open NJ

namespace Phylo.Stat.NJstSamplingAE

open Phylo.Stat.AESampling
  (empAvg empAvg_eventually_close_ae_all exists_uniform_N_of_finite)

universe u v

variable {X : Type u} [Fintype X] [DecidableEq X]
variable {Ω₀ : Type*} [MeasurableSpace Ω₀]

/-- **单棵基因树给出的 USTAR 相异度**（`Ω₀` = 单棵基因树的空间）。 -/
abbrev DissFun (X : Type*) (Ω₀ : Type*) : Type _ := Ω₀ → X → X → ℝ

/-- **样本相异度对称、零对角**（⇒ 平均之后仍是 `Dissimilarity`）。 -/
structure DissTable (ind : DissFun X Ω₀) : Prop where
  symm : ∀ (s : Ω₀) (x y : X), ind s x y = ind s y x
  diag : ∀ (s : Ω₀) (x : X), ind s x x = 0

/-- ★★ 第 `n` 棵基因树给出的**经验 USTAR 相异度**（逐叶对取样本平均）。

⚠️ **技术性说明**（同 `MSCSamplingAE.empTable`）：对 `n = 0` **退化**（取真值 `M.δ`），
因为 `empAvg 0 = 0` 在 `diag` 上虽无害、但不利于「全函数」；数学上 `n = 0` 从不用到
（`N ≥ 1` 由 `exists_uniform_N_of_finite` 保证）。 -/
noncomputable def empDiss (ind : DissFun X Ω₀) (h : DissTable ind) (M : NJstData.{u, v} X)
    (n : ℕ) (ω : ℕ → Ω₀) : Dissimilarity X where
  val x y := if n = 0 then M.δ.val x y else empAvg (fun k (ω : ℕ → Ω₀) => ind (ω k) x y) n ω
  symm x y := by
    by_cases hn : n = 0
    · simp only [hn, ↓reduceIte]
      exact M.δ.symm x y
    · simp only [hn, ↓reduceIte, empAvg]
      congr 1
      exact Finset.sum_congr rfl fun k _ => h.symm (ω k) x y
  diag x := by
    by_cases hn : n = 0
    · simp only [hn, ↓reduceIte]
      exact M.δ.diag x
    · simp only [hn, ↓reduceIte, empAvg]
      rw [Finset.sum_eq_zero (fun k _ => h.diag (ω k) x), mul_zero]

/-- ★★★ **`DissClose` 形式的几乎必然收敛**（**统一的 `N`**）：
`∀ᵐ ω, ∀ ε > 0, ∃ N, ∀ n ≥ N, DissClose (empDiss n ω) M.δ ε`。

这正是 `NJst.lean` 里那条**确定性**公理 `USTARSampling.converges`（对固定真律 `M`）的**几乎必然版**。
指标集取 `X × X`（**有限** ⇒ 可有限交、可取下确界）。 -/
theorem empDiss_eventually_close_ae (ind : DissFun X Ω₀) (h : DissTable ind)
    (M : NJstData.{u, v} X) (μ : Measure (ℕ → Ω₀)) [IsProbabilityMeasure μ]
    (hint : ∀ x y : X, Integrable (fun ω : ℕ → Ω₀ => ind (ω 0) x y) μ)
    (hindep : ∀ x y : X, iIndepFun (fun k (ω : ℕ → Ω₀) => ind (ω k) x y) μ)
    (hident : ∀ x y : X, ∀ k, IdentDistrib (fun ω : ℕ → Ω₀ => ind (ω k) x y)
      (fun ω : ℕ → Ω₀ => ind (ω 0) x y) μ μ)
    (hmean : ∀ x y : X, ∫ ω, ind (ω 0) x y ∂μ = M.δ.val x y) :
    ∀ᵐ ω ∂μ, ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N,
      DissClose (empDiss ind h M n ω) M.δ ε := by
  classical
  have hpt : ∀ᵐ ω ∂μ, ∀ i : X × X, ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N,
      |empAvg (fun k (ω : ℕ → Ω₀) => ind (ω k) i.1 i.2) n ω - M.δ.val i.1 i.2| < ε := by
    have hbase := empAvg_eventually_close_ae_all (ι := X × X)
      (fun i : X × X => fun k (ω : ℕ → Ω₀) => ind (ω k) i.1 i.2) μ
      (fun i => hint i.1 i.2) (fun i => hindep i.1 i.2) (fun i k => hident i.1 i.2 k)
    filter_upwards [hbase] with ω hω i ε hε
    simpa only [hmean i.1 i.2] using hω i ε hε
  filter_upwards [hpt] with ω hω
  intro ε hε
  obtain ⟨N, _, hN⟩ := exists_uniform_N_of_finite (ι := X × X)
    (P := fun i n => |empAvg (fun k (ω : ℕ → Ω₀) => ind (ω k) i.1 i.2) n ω
      - M.δ.val i.1 i.2| < ε) (fun i => hω i ε hε)
  refine ⟨N, fun n hn x y => ?_⟩
  have hn0 : n ≠ 0 := by omega
  have := hN n hn (x, y)
  simpa only [DissClose, empDiss, hn0, ↓reduceIte] using this

/-! ## 把公理化的采样在几乎必然意义下实现 -/

/-- ★★ **真律固定版的一致性结构**：`emp` 与 `converges` 都**只对该律**断言。 -/
structure USTARSamplingFixed (X : Type u) [Fintype X] [DecidableEq X] where
  /-- **真实模型**。 -/
  law : NJstData.{u, v} X
  /-- 经验相异度序列。 -/
  emp : ℕ → Dissimilarity X
  /-- ★ **大数定律**（只对 `law`）。 -/
  converges : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, DissClose (emp n) law.δ ε

/-- ★ 反空真见证：`USTARSamplingFixed` **非空**（理想样本 `emp n := law.δ`）。
★ 与 `NJst.ustarSampling_nonempty` 同一构造，故本文件的 a.e. 定理**不是空真的**。 -/
theorem ustarSamplingFixed_nonempty (X : Type u) [Fintype X] [DecidableEq X]
    (M : NJstData.{u, v} X) : Nonempty (USTARSamplingFixed.{u, v} X) :=
  ⟨{ law := M
     emp := fun _ => M.δ
     converges := fun ε hε =>
       ⟨0, fun _ _ x y => by
         show |M.δ.val x y - M.δ.val x y| < ε
         rw [sub_self, abs_zero]
         exact hε⟩ }⟩

/-- ★★★ **公理化的采样结构被数据 a.e. 实现**：在 `empDiss_eventually_close_ae` 的
a.e. 事件上，经验相异度构成一个 `USTARSamplingFixed`（真律 `= M`）。 -/
theorem exists_ustarSamplingFixed_ae (ind : DissFun X Ω₀) (h : DissTable ind)
    (M : NJstData.{u, v} X) (μ : Measure (ℕ → Ω₀)) [IsProbabilityMeasure μ]
    (hint : ∀ x y : X, Integrable (fun ω : ℕ → Ω₀ => ind (ω 0) x y) μ)
    (hindep : ∀ x y : X, iIndepFun (fun k (ω : ℕ → Ω₀) => ind (ω k) x y) μ)
    (hident : ∀ x y : X, ∀ k, IdentDistrib (fun ω : ℕ → Ω₀ => ind (ω k) x y)
      (fun ω : ℕ → Ω₀ => ind (ω 0) x y) μ μ)
    (hmean : ∀ x y : X, ∫ ω, ind (ω 0) x y ∂μ = M.δ.val x y) :
    ∀ᵐ ω ∂μ, ∃ sm : USTARSamplingFixed.{u, v} X,
      sm.law = M ∧ ∀ n : ℕ, sm.emp n = empDiss ind h M n ω := by
  filter_upwards [empDiss_eventually_close_ae ind h M μ hint hindep hident hmean] with ω hω
  exact ⟨{ law := M, emp := fun n => empDiss ind h M n ω, converges := hω }, rfl, fun _ => rfl⟩

/-- ★★★ **ADR 2016 Thm 4.1（NJst / USTAR-NJ 统计一致性，真律固定版）**：
把 `NJst.njst_statisticallyConsistent` 里的 `sm : USTARSampling X` 换成 `USTARSamplingFixed X`，
其余**逐字相同**（证明仍是「SLLN ＋ 条件 (1)(2)」两步）。

⚠️ 条件 (1)(2)（`ReturnsFittingTree` / `ContinuousAtBinaryTreeMetrics`）**仍在假设面里** ——
它们是**文献假设**，本文件**只**升级 SLLN。 -/
theorem njst_statisticallyConsistent_fixed (sm : USTARSamplingFixed.{u, v} X)
    (E : Dissimilarity X → Cladogram.{u, v} X)
    (h1 : ReturnsFittingTree E) (h2 : ContinuousAtBinaryTreeMetrics E) :
    ∃ N : ℕ, ∀ n ≥ N, Nonempty (Iso (E (sm.emp n)) sm.law.tree) := by
  obtain ⟨ε, hε, hcont⟩ := h2 sm.law.T sm.law.δ sm.law.hT_binary sm.law.hT_pos sm.law.hT_dist
  obtain ⟨N, hN⟩ := sm.converges ε hε
  have hδ : Nonempty (Iso (E sm.law.δ) sm.law.tree) := h1 sm.law.δ sm.law.T sm.law.hT_dist
  refine ⟨N, fun n hn => ?_⟩
  have hn' : Nonempty (Iso (E (sm.emp n)) (E sm.law.δ)) := hcont (sm.emp n) (hN n hn)
  exact ⟨hn'.some.trans hδ.some⟩

/-- ★★★ **NJst 的几乎必然统计一致性**（本子批的概率层收口）：

在 iid 基因树模型下，**几乎必然**地，满足 ADR 条件 (1)(2) 的树选择方法 `E` 在**足够多**基因树后
输出与真物种树同构的树 —— 即 **`USTARSampling.converges` 那条公理所承载的结论，在概率空间里
由强大数定律 ＋ ADR 的两步论证真正推出**。 -/
theorem njst_statisticallyConsistent_ae (ind : DissFun X Ω₀) (h : DissTable ind)
    (M : NJstData.{u, v} X) (μ : Measure (ℕ → Ω₀)) [IsProbabilityMeasure μ]
    (hint : ∀ x y : X, Integrable (fun ω : ℕ → Ω₀ => ind (ω 0) x y) μ)
    (hindep : ∀ x y : X, iIndepFun (fun k (ω : ℕ → Ω₀) => ind (ω k) x y) μ)
    (hident : ∀ x y : X, ∀ k, IdentDistrib (fun ω : ℕ → Ω₀ => ind (ω k) x y)
      (fun ω : ℕ → Ω₀ => ind (ω 0) x y) μ μ)
    (hmean : ∀ x y : X, ∫ ω, ind (ω 0) x y ∂μ = M.δ.val x y)
    (E : Dissimilarity X → Cladogram.{u, v} X)
    (h1 : ReturnsFittingTree E) (h2 : ContinuousAtBinaryTreeMetrics E) :
    ∀ᵐ ω ∂μ, ∃ N : ℕ, ∀ n ≥ N,
      Nonempty (Iso (E (empDiss ind h M n ω)) M.tree) := by
  filter_upwards [empDiss_eventually_close_ae ind h M μ hint hindep hident hmean] with ω hω
  exact njst_statisticallyConsistent_fixed
    ⟨M, fun n => empDiss ind h M n ω, hω⟩ E h1 h2

end Phylo.Stat.NJstSamplingAE
