/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.Stat.MSCKingmanMeasure

/-!
# `Phylo.Stat.MSCBayes` —— 贝叶斯 MSC（W11d / X6）

## 0. 文献（**在手**，不是缺口）

* **Heled & Drummond (2010)**, *Bayesian Inference of Species Trees from Multilocus Data*,
  *Mol. Biol. Evol.* **27**(3):570–580 ——
  `references/md/HeledDrummond2010_BayesianSpeciesTreesMultilocus.md`：

  * **496–510** 行 Eq. (1)：`P(S|D) ∝ ∫_G ∏ᵢ P(dᵢ|gᵢ) P(gᵢ|S) P(S) dG`
    —— **后验 ∝ 先验 × 似然**，且基因树 `G` 被**边缘化（积分）掉**；
  * **523–525** 行：`P(dᵢ|gᵢ)` = Felsenstein 似然、`P(gᵢ|S)` = 多物种溯祖、`P(S)` = 物种树**先验**；
  * **615–637** 行：`P(S) = fBD(S)·PN(S)`（(4) 式）；发散时间先验 `fBD` 是
    **reconstructed birth–death process**（Gernhard 2008，参数 `λ` / `μ`，(5) 式给出密度）；
    拓扑先验在 ranked labeled trees 上**均匀**；
  * **510–520** 行：直接算该积分**不可能** —— 用 MCMC 近似。
* **Rannala & Yang (2003)**, *Genetics* **164**:1645–1656 ——
  `references/md/RannalaYang2003_BayesSpeciesDivergenceTimesAncestralPopulationSizes.md`
  **355–370** 行 (4)(5) 式：`f(Θ,G|D) ∝ f(D|G) f(G|Θ) f(Θ)`、`f(Θ|D) = ∫ f(Θ,G|D) dG`。

⇒ **形态判定：实现**。有限/离散层（§1、§3）与**已有** ★★★ `kingmanMSCMeasure` 的
测度层边缘化（§2）都承载得了「后验 ∝ 先验 × 似然 ＋ 归一」。
**只有「一般连续先验 `ρ` 下的 MCMC / 后验一致性」超范围 ⇒ 落显式 `def … : Prop` 缺口（§5）**，
不硬编。

## 1. 交付结构

| 节 | 内容 |
|---|---|
| §1 | **有限树空间上的贝叶斯后验**：`FiniteBayesModel`（先验 `ρ` ＋ 似然 `L`）、`evidence = ∑ᵢ ρᵢLᵢ`、`posterior i = ρᵢLᵢ/Z`；证 **后验 ∝ 先验 × 似然**（**无除法**形式）、**归一到 `1`**、非负、**支撑 = 先验支撑 ∩ 似然支撑** |
| §2 | **用已有 `kingmanMSCMeasure` 做边缘化**：深合并似然 `deepLik u = e^{−a}e^{−b}`；`ν(DeepSet) = ∫⁻ deepLik ∂ρ`；**边缘似然恒正**；**后验测度** `posteriorDeep ρ = ρ.withDensity (deepLik/Z)`（归一 / **后验×证据 = 先验×似然** / **≪ ρ**）；**加性**（多棵树先验加权和） |
| §3 | ★C **端到端最小例**：4 taxon、2 棵候选树、具体先验；**两棵树先验加权和** `(c, 1−c)`；`dirac` 与有限层的**对接定理** |
| §4 | ★B **反例检查**（支撑收缩 / 零似然 / `Z>0` 的必要性） |
| §5 | **显式缺口**（`def … : Prop`） |

## 2. 与既有器材的关系（**复用、不重造**）

* `Phylo.Stat.MSCKingmanMeasure.kingmanMSCMeasure`（★★★ 真测度）、
  `kingmanMSCMeasure_deep`（★★★ `e^{−a}e^{−b}` 赋权的准确内容）、
  `kingmanMSCMeasure_dirac_deep`（确定物种树的闭式）、
  `measurableSet_kingmanMSCTopoSym_deep`（`deep` 可测）、
  `DeepSet`、`toKingmanΘ` —— **逐条复用**，本文件**不重造**测度；
* `Phylo.Stat.MSCProof.mscConcordant` / `mscDiscordant`（MSC 权重 `1−⅔e^{−t}` / `⅓e^{−t}`）
  及其不等式 `mscDiscordant_lt_mscConcordant` —— §3 的似然**直接取它们**。
-/

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal BigOperators Topology

namespace Phylo.Stat.MSCBayes

/-! ## 1. 有限树空间上的贝叶斯后验：`后验 ∝ 先验 × 似然` -/

/-- **有限候选树空间上的贝叶斯 MSC 模型**（Heled–Drummond Eq. (1) 的**有限/离散**化身）：
`prior` 是候选物种树上的先验 `ρ`（非负、和为 `1`），`lik` 是候选物种树给出**观测数据**的
MSC 似然 `L`（非负；具体取法见 §3）。 -/
structure FiniteBayesModel (ι : Type*) [Fintype ι] where
  /-- 先验 `ρ`。 -/
  prior : ι → ℝ
  /-- 先验非负。 -/
  prior_nonneg : ∀ i, 0 ≤ prior i
  /-- 先验归一。 -/
  prior_sum_one : ∑ i, prior i = 1
  /-- 似然 `L`。 -/
  lik : ι → ℝ
  /-- 似然非负。 -/
  lik_nonneg : ∀ i, 0 ≤ lik i

namespace FiniteBayesModel

variable {ι : Type*} [Fintype ι]

/-- **证据（边缘似然）** `Z = ∑ᵢ ρᵢ Lᵢ` —— 后验的归一化常数。 -/
def evidence (M : FiniteBayesModel ι) : ℝ := ∑ i, M.prior i * M.lik i

/-- ★★ **贝叶斯后验** `ρᵢ Lᵢ / Z`：**后验 ∝ 先验 × 似然**。 -/
def posterior (M : FiniteBayesModel ι) (i : ι) : ℝ := M.prior i * M.lik i / M.evidence

theorem evidence_nonneg (M : FiniteBayesModel ι) : 0 ≤ M.evidence :=
  Finset.sum_nonneg fun i _ => mul_nonneg (M.prior_nonneg i) (M.lik_nonneg i)

/-- ★★ **后验 ∝ 先验 × 似然** —— 用**无除法**的交叉相乘形式陈述，
故在 `Z = 0` 的病态下**仍然成立**（此时两边同为零）。 -/
theorem posterior_mul_eq (M : FiniteBayesModel ι) (i j : ι) :
    M.posterior i * (M.prior j * M.lik j) = M.posterior j * (M.prior i * M.lik i) := by
  simp only [posterior, div_eq_mul_inv]
  ring

/-- ★★★ **后验归一到 `1`**（`Z ≠ 0` 时）—— 「`∝`」里那个常数的准确内容。 -/
theorem posterior_sum_one (M : FiniteBayesModel ι) (hZ : M.evidence ≠ 0) :
    ∑ i, M.posterior i = 1 := by
  have h : ∑ i, M.posterior i = M.evidence * M.evidence⁻¹ := by
    have h1 : ∑ i, M.posterior i = (∑ i, M.prior i * M.lik i) * M.evidence⁻¹ := by
      rw [show (∑ i, M.posterior i) = ∑ i, M.prior i * M.lik i * M.evidence⁻¹ from
        Finset.sum_congr rfl fun i _ => by rw [posterior, div_eq_mul_inv]]
      rw [← Finset.sum_mul]
    rw [h1]
    simp only [evidence]
  rw [h, mul_inv_cancel₀ hZ]

theorem posterior_nonneg (M : FiniteBayesModel ι) (i : ι) : 0 ≤ M.posterior i :=
  div_nonneg (mul_nonneg (M.prior_nonneg i) (M.lik_nonneg i)) M.evidence_nonneg

/-- **后验的支撑 ⊆ 先验的支撑**（先验为 `0` 的候选树，似然再大也是 `0`）。 -/
theorem posterior_eq_zero_of_prior_eq_zero (M : FiniteBayesModel ι) {i : ι}
    (h : M.prior i = 0) : M.posterior i = 0 := by
  simp [posterior, h]

/-- **后验的支撑 ⊆ 似然的支撑**（似然为 `0` 的候选树，先验再大也是 `0`）。 -/
theorem posterior_eq_zero_of_lik_eq_zero (M : FiniteBayesModel ι) {i : ι}
    (h : M.lik i = 0) : M.posterior i = 0 := by
  simp [posterior, h]

/-- ★★ **后验的支撑恰是「先验支撑 ∩ 似然支撑」**（`Z > 0` 时）。 -/
theorem posterior_pos_iff (M : FiniteBayesModel ι) (hZ : 0 < M.evidence) (i : ι) :
    0 < M.posterior i ↔ 0 < M.prior i ∧ 0 < M.lik i := by
  constructor
  · intro h
    have hnum : 0 < M.prior i * M.lik i := by
      by_contra hc
      rw [not_lt] at hc
      exact absurd h (not_lt.mpr (div_nonpos_of_nonpos_of_nonneg hc hZ.le))
    constructor
    · by_contra hp
      rw [not_lt] at hp
      have := mul_nonpos_of_nonpos_of_nonneg hp (M.lik_nonneg i)
      linarith
    · by_contra hl
      rw [not_lt] at hl
      have := mul_nonpos_of_nonneg_of_nonpos (M.prior_nonneg i) hl
      linarith
  · rintro ⟨h1, h2⟩
    exact div_pos (mul_pos h1 h2) hZ

/-- ★★ **证据为正的充分条件**：某个候选树先验与似然**同时**为正。 -/
theorem evidence_pos_of_pos (M : FiniteBayesModel ι) {i : ι}
    (h : 0 < M.prior i ∧ 0 < M.lik i) : 0 < M.evidence := by
  have hterm : 0 < M.prior i * M.lik i := mul_pos h.1 h.2
  have hle : M.prior i * M.lik i ≤ M.evidence :=
    Finset.single_le_sum (fun j _ => mul_nonneg (M.prior_nonneg j) (M.lik_nonneg j))
      (Finset.mem_univ i)
  exact lt_of_lt_of_le hterm hle

/-- ★★★ **非空（反空真）**：均匀先验 ＋ 常似然 `1` 给出一个居民
（`ι` 有限非空时）。 -/
theorem nonempty (ι : Type*) [Fintype ι] [Nonempty ι] : Nonempty (FiniteBayesModel ι) :=
  ⟨{ prior := fun _ => ((Fintype.card ι : ℝ))⁻¹
     prior_nonneg := fun _ => by positivity
     prior_sum_one := by
       rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
       exact mul_inv_cancel₀ (by exact_mod_cast Fintype.card_ne_zero)
     lik := fun _ => 1
     lik_nonneg := fun _ => zero_le_one }⟩

/-! ### 1.1 ★B 反例一：**后验的支撑可以严格小于先验的支撑**

`Fin 2`、先验均匀 `(½, ½)`、似然 `(1, 0)`：先验在**两棵**树上都正，
后验却把质量**全部**搬到第 `0` 棵（`posterior 1 = 0`）。

⇒ 直接回答「**后验一定与先验有相同支撑吗？**」—— **不一定**：
`支撑(后验) = 支撑(先验) ∩ 支撑(似然)`（`posterior_pos_iff`），
似然为零处**无论先验多大都被抹掉**；反方向（先验为零处后验为零）见
`posterior_eq_zero_of_prior_zero`。 -/

/-- ★B：均匀先验。 -/
def shrinkPrior : Fin 2 → ℝ := fun _ => 1 / 2

/-- ★B：把第二棵候选树完全排除的似然。 -/
def shrinkLik : Fin 2 → ℝ := fun i => if i = 0 then 1 else 0

/-- ★B：**支撑严格收缩**的最小模型。 -/
def shrinkModel : FiniteBayesModel (Fin 2) where
  prior := shrinkPrior
  prior_nonneg := by intro i; fin_cases i <;> norm_num [shrinkPrior]
  prior_sum_one := by rw [Fin.sum_univ_two]; norm_num [shrinkPrior]
  lik := shrinkLik
  lik_nonneg := by intro i; fin_cases i <;> norm_num [shrinkLik]

/-- ★B：先验在两棵树上**都**严格正。 -/
theorem shrinkModel_prior_pos (i : Fin 2) : 0 < shrinkModel.prior i := by
  fin_cases i <;> norm_num [shrinkModel, shrinkPrior]

/-- ★B：后验把第二棵树**抹成零**（支撑严格收缩）。 -/
theorem shrinkModel_posterior_one_eq_zero : shrinkModel.posterior 1 = 0 := by
  rw [posterior_eq_zero_of_lik_eq_zero]
  norm_num [shrinkModel, shrinkLik]

/-- ★B：**先验正而严格之下的后验为零** —— 支撑收缩的断言本体。 -/
theorem posterior_support_lt_prior_support :
    0 < shrinkModel.prior 1 ∧ shrinkModel.posterior 1 = 0 :=
  ⟨shrinkModel_prior_pos 1, shrinkModel_posterior_one_eq_zero⟩

/-- ★B：剩下那棵树拿到**全部**后验质量。 -/
theorem shrinkModel_posterior_zero_eq_one : shrinkModel.posterior 0 = 1 := by
  have hsum : ∑ i : Fin 2, shrinkModel.posterior i = 1 :=
    posterior_sum_one _ (by
      norm_num [evidence, shrinkModel, shrinkPrior, shrinkLik, Fin.sum_univ_two])
  rw [Fin.sum_univ_two, shrinkModel_posterior_one_eq_zero, add_zero] at hsum
  exact hsum

/-! ### 1.2 ★B 反例二：**似然恒为零时「后验」不是概率分布**

`Z = 0` 时 `ρᵢLᵢ/Z` 在 `ℝ` 里按 `_ / 0 = 0` 求值为 `0`，求和 `= 0 ≠ 1`。
⇒ `posterior_sum_one` 的假设 `Z ≠ 0` **是必需的**，不能省。
（**但**在 MSC 模型里 `Z > 0` **恒成立** —— 见 §2 的 `kingmanMSCMeasure_deep_pos`：
深合并似然 `e^{−a}e^{−b}` **处处严格正**，故「似然为 0」这一病态**在 MSC 里不会发生**。） -/

/-- ★B：似然恒为 `0` 的模型。 -/
def zeroLikModel : FiniteBayesModel (Fin 2) where
  prior := fun _ => 1 / 2
  prior_nonneg := fun _ => by norm_num
  prior_sum_one := by rw [Fin.sum_univ_two]; norm_num
  lik := fun _ => 0
  lik_nonneg := fun _ => le_rfl

/-- ★B：证据为零。 -/
theorem zeroLikModel_evidence : zeroLikModel.evidence = 0 := by
  simp [evidence, zeroLikModel]

/-- ★B：按 `ℝ` 的 `_ / 0 = 0` 约定，「后验」的**总和是 `0`**。 -/
theorem zeroLikModel_posterior_sum : ∑ i, zeroLikModel.posterior i = 0 := by
  simp [posterior, zeroLikModel]

/-- ★B：**它不是概率分布**（`0 ≠ 1`）—— `Z ≠ 0` 不可省。 -/
theorem zeroLikModel_posterior_not_prob : ∑ i, zeroLikModel.posterior i ≠ 1 := by
  rw [zeroLikModel_posterior_sum]
  norm_num

end FiniteBayesModel

/-! ## 2. 用已有 ★★★ `kingmanMSCMeasure` 做边缘化：物种树侧的后验测度 -/

open Phylo.Stat.MSCKingmanMeasure

/-- **物种树侧参数空间**：叶长 `Fin 4 → ℝ` × 根以下两段内枝长 `(a, b)`。
（= `MSCKingmanMeasure` 里 `kingmanMSCMeasure` 的**先验空间**。） -/
abbrev SpeciesParam : Type := (Fin 4 → ℝ) × ℝ≥0 × ℝ≥0

/-- ★★★ **深合并的似然**（观测到「两侧在根以下都未合并」的概率）：
`deepLik u = e^{−a(u)} · e^{−b(u)}` —— 逐点等于
`MSCKingmanMeasure.kingmanMSCMeasure_deep` 的**被积函数**。

⚠️ 它在 `SpeciesParam` 上**处处严格正**（`deepLik_pos`）——
这正是 §4 里「似然为零」的病态在 MSC 下**不会发生**的原因。 -/
def deepLik (u : SpeciesParam) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-(u.2.1 : ℝ))) * ENNReal.ofReal (Real.exp (-(u.2.2 : ℝ)))

theorem measurable_deepLik : Measurable deepLik := by
  have h1 : Measurable fun u : SpeciesParam => (u.2.1 : ℝ) :=
    measurable_subtype_coe.comp measurable_snd.fst
  have h2 : Measurable fun u : SpeciesParam => (u.2.2 : ℝ) :=
    measurable_subtype_coe.comp measurable_snd.snd
  unfold deepLik
  exact (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp h1.neg)).mul
    (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp h2.neg))

theorem deepLik_pos (u : SpeciesParam) : 0 < deepLik u := by
  unfold deepLik
  exact ENNReal.mul_pos (ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos _)))
    (ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos _)))

theorem deepLik_ne_top (u : SpeciesParam) : deepLik u ≠ ⊤ := by
  unfold deepLik
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top

/-- **`deepLik` 的支撑是全集**（处处严格正）。 -/
theorem support_deepLik : Function.support deepLik = Set.univ :=
  Set.eq_univ_of_forall fun u => by
    rw [Function.mem_support]
    exact ne_of_gt (deepLik_pos u)

/-- ★★★ **边缘似然 = 对先验的积分**（`kingmanMSCMeasure_deep` 的 `deepLik` 封装）：
`ν(deep) = ∫⁻ e^{−a}e^{−b} dρ`。 -/
theorem kingmanMSCMeasure_deep_lik (ρ : Measure SpeciesParam) :
    kingmanMSCMeasure ρ DeepSet = ∫⁻ u, deepLik u ∂ρ := by
  simpa only [deepLik] using kingmanMSCMeasure_deep ρ

/-- ★★★ **边缘似然处处严格正**（任意概率先验 `ρ`）：
`0 < ν(deep)` —— 「似然为零 ⇒ 后验无定义」这一病态在 MSC 下**永不发生**，
故 §1 的 `Z > 0` 前提在 MSC 模型里**自动满足**。 -/
theorem kingmanMSCMeasure_deep_pos (ρ : Measure SpeciesParam) [IsProbabilityMeasure ρ] :
    0 < kingmanMSCMeasure ρ DeepSet := by
  rw [kingmanMSCMeasure_deep_lik ρ, lintegral_pos_iff_support measurable_deepLik,
    support_deepLik, measure_univ]
  exact zero_lt_one

theorem kingmanMSCMeasure_deep_ne_top (ρ : Measure SpeciesParam) [IsProbabilityMeasure ρ] :
    kingmanMSCMeasure ρ DeepSet ≠ ⊤ := by
  refine ne_top_of_le_ne_top ENNReal.one_ne_top ?_
  rw [← measure_univ (μ := kingmanMSCMeasure ρ)]
  exact measure_mono (Set.subset_univ _)

/-- ★★★ **物种树侧的贝叶斯后验测度**（Heled–Drummond Eq. (1) 的测度层化身）：
先验 `ρ` **乘上**深合并似然 `deepLik`，再**除以证据** `ν(deep)` 归一。 -/
def posteriorDeep (ρ : Measure SpeciesParam) : Measure SpeciesParam :=
  ρ.withDensity fun u => deepLik u / kingmanMSCMeasure ρ DeepSet

/-- ★★★ **后验 × 证据 = 先验 × 似然**（在可测集 `A` 上）——
这是「`后验 ∝ 先验 × 似然`」在测度层的**准确内容**（无需求逆）。 -/
theorem posteriorDeep_mul_evidence (ρ : Measure SpeciesParam) {A : Set SpeciesParam}
    (hA : MeasurableSet A) (hZ : kingmanMSCMeasure ρ DeepSet ≠ 0)
    (hZt : kingmanMSCMeasure ρ DeepSet ≠ ⊤) :
    posteriorDeep ρ A * kingmanMSCMeasure ρ DeepSet = ∫⁻ u in A, deepLik u ∂ρ := by
  rw [posteriorDeep, withDensity_apply _ hA,
    show (∫⁻ u in A, deepLik u / kingmanMSCMeasure ρ DeepSet ∂ρ)
        = (∫⁻ u in A, deepLik u ∂ρ) / kingmanMSCMeasure ρ DeepSet from by
      rw [show (∫⁻ u in A, deepLik u / kingmanMSCMeasure ρ DeepSet ∂ρ)
          = ∫⁻ u in A, (kingmanMSCMeasure ρ DeepSet)⁻¹ * deepLik u ∂ρ from
        lintegral_congr fun u => ENNReal.div_eq_inv_mul,
        lintegral_const_mul _ measurable_deepLik, ENNReal.div_eq_inv_mul]]
  exact ENNReal.div_mul_cancel hZ hZt

/-- ★★ **后验测度的显式形式**：`posteriorDeep ρ A = (∫⁻_A deepLik ∂ρ) / ν(deep)`。 -/
theorem posteriorDeep_apply (ρ : Measure SpeciesParam) {A : Set SpeciesParam}
    (hA : MeasurableSet A) :
    posteriorDeep ρ A = (∫⁻ u in A, deepLik u ∂ρ) / kingmanMSCMeasure ρ DeepSet := by
  rw [posteriorDeep, withDensity_apply _ hA]
  rw [show (∫⁻ u in A, deepLik u / kingmanMSCMeasure ρ DeepSet ∂ρ)
      = ∫⁻ u in A, (kingmanMSCMeasure ρ DeepSet)⁻¹ * deepLik u ∂ρ from
    lintegral_congr fun u => ENNReal.div_eq_inv_mul]
  rw [lintegral_const_mul _ measurable_deepLik, ENNReal.div_eq_inv_mul]

/-- ★★★ **后验是概率测度**（归一到 `1`）—— 对**任意**概率先验 `ρ`，
**无需**任何额外假设（`Z > 0` 与 `Z ≠ ⊤` 都由 `kingmanMSCMeasure` 的白送给出）。 -/
theorem posteriorDeep_univ_eq_one (ρ : Measure SpeciesParam) [IsProbabilityMeasure ρ] :
    posteriorDeep ρ Set.univ = 1 := by
  rw [posteriorDeep_apply ρ MeasurableSet.univ, Measure.restrict_univ,
    ← kingmanMSCMeasure_deep_lik ρ]
  exact ENNReal.div_self (ne_of_gt (kingmanMSCMeasure_deep_pos ρ))
    (kingmanMSCMeasure_deep_ne_top ρ)

/-- ★★ **后验 ≪ 先验**（测度层的「后验支撑 ⊆ 先验支撑」：
先验为零测的集合，后验也为零测）。 -/
theorem posteriorDeep_absolutelyContinuous (ρ : Measure SpeciesParam) :
    posteriorDeep ρ ≪ ρ :=
  withDensity_absolutelyContinuous ρ _

/-- ★★ **测度层加性**：先验是**多棵候选树的加权和**时，MSC 边缘似然 `ν(deep)` 也**相加**
（⇒ 后验仍是「先验 × 似然 / 证据」的商，故仍归一到 `1`）。 -/
theorem kingmanMSCMeasure_deep_add (ρ₁ ρ₂ : Measure SpeciesParam) :
    kingmanMSCMeasure (ρ₁ + ρ₂) DeepSet
      = kingmanMSCMeasure ρ₁ DeepSet + kingmanMSCMeasure ρ₂ DeepSet := by
  rw [kingmanMSCMeasure_deep_lik, kingmanMSCMeasure_deep_lik, kingmanMSCMeasure_deep_lik]
  exact lintegral_add_measure deepLik ρ₁ ρ₂

/-! ## 3. ★C 端到端最小例：4 taxon、2 棵候选树、具体先验 -/

open Phylo.Stat.MSCProof (mscConcordant mscDiscordant mscConcordant_pos mscConcordant_nonneg
  mscDiscordant_pos mscDiscordant_lt_mscConcordant)

/-- ★★★ **`dirac` 先验下有限层与测度层的对接**：
确定的物种树 `(leaf, a, b)` 的**边缘似然**恰是 `deepLik (leaf, a, b) = e^{−a}e^{−b}`，
即 §1 里似然 `L` 的**具体取值**不是另设的，而是 `kingmanMSCMeasure` 的取值。 -/
theorem kingmanMSCMeasure_dirac_deepLik (leaf : Fin 4 → ℝ) (a b : ℝ≥0) :
    kingmanMSCMeasure (Measure.dirac (leaf, a, b)) DeepSet = deepLik (leaf, a, b) := by
  simpa only [deepLik] using kingmanMSCMeasure_dirac_deep leaf a b

/-- ★★★ **两棵树先验的加权和（测度层）**：`ρ = δ(u₁) + δ(u₂)` 时
`ν(deep) = e^{−a₁}e^{−b₁} + e^{−a₂}e^{−b₂}`（旧的 `kingmanMSCMeasure_deep` 的直接推论）。 -/
theorem kingmanMSCMeasure_dirac_add_deep (u₁ u₂ : SpeciesParam) :
    kingmanMSCMeasure (Measure.dirac u₁ + Measure.dirac u₂) DeepSet
      = deepLik u₁ + deepLik u₂ := by
  rw [kingmanMSCMeasure_deep_add, kingmanMSCMeasure_dirac_deepLik,
    kingmanMSCMeasure_dirac_deepLik]

/-- ★C **两棵树先验的加权和（有限层）**：`ρ = (c, 1−c)`，似然 `(x₁, x₂)`
（`xᵢ` 取 `e^{−aᵢ−bᵢ}`，见上一条对接定理）。 -/
def twoTreeMixtureModel (c x₁ x₂ : ℝ) (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1)
    (hx₁ : 0 ≤ x₁) (hx₂ : 0 ≤ x₂) : FiniteBayesModel (Fin 2) where
  prior := fun i => if i = 0 then c else 1 - c
  prior_nonneg := by
    intro i
    fin_cases i
    · simpa using hc₀
    · simpa using sub_nonneg.mpr hc₁
  prior_sum_one := by
    rw [Fin.sum_univ_two]
    norm_num
  lik := fun i => if i = 0 then x₁ else x₂
  lik_nonneg := by
    intro i
    fin_cases i
    · simpa using hx₁
    · simpa using hx₂

/-- ★★ **两棵树先验加权和的后验仍归一到 `1`**
（只要有一棵候选树**先验与似然同时为正**）。 -/
theorem twoTreeMixtureModel_posterior_sum_one (c x₁ x₂ : ℝ) (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1)
    (hx₁ : 0 ≤ x₁) (hx₂ : 0 ≤ x₂)
    (hx : (0 < c ∧ 0 < x₁) ∨ (c < 1 ∧ 0 < x₂)) :
    ∑ i, (twoTreeMixtureModel c x₁ x₂ hc₀ hc₁ hx₁ hx₂).posterior i = 1 := by
  refine FiniteBayesModel.posterior_sum_one _ (ne_of_gt ?_)
  rcases hx with ⟨hc, hx⟩ | ⟨hc, hx⟩
  · exact FiniteBayesModel.evidence_pos_of_pos _
      (i := 0) ⟨by simpa [twoTreeMixtureModel] using hc,
        by simpa [twoTreeMixtureModel] using hx⟩
  · refine FiniteBayesModel.evidence_pos_of_pos _ (i := 1) ⟨?_, ?_⟩
    · simp [twoTreeMixtureModel]
      linarith
    · simpa [twoTreeMixtureModel] using hx

/-- ★C **端到端最小例**：4 taxon、**2 棵候选树**（`ab|cd` 与 `ac|bd`）、
先验 `(½, ½)`、观测到的基因树拓扑**与候选树 1 一致**。
于是似然 = `(mscConcordant t₁, mscDiscordant t₂)`
（第 2 棵树上观测到该拓扑的概率是「不一致」概率 `⅓e^{−t₂}`）。 -/
def twoTreeMSCModel (t₁ t₂ : ℝ) (ht₁ : 0 ≤ t₁) : FiniteBayesModel (Fin 2) where
  prior := fun _ => 1 / 2
  prior_nonneg := fun _ => by norm_num
  prior_sum_one := by rw [Fin.sum_univ_two]; norm_num
  lik := fun i => if i = 0 then mscConcordant t₁ else mscDiscordant t₂
  lik_nonneg := by
    intro i
    fin_cases i
    · simpa using mscConcordant_nonneg ht₁
    · simpa using (mscDiscordant_pos t₂).le

/-- ★★ 该模型的证据**严格为正**（第 2 棵树的似然 `⅓e^{−t₂}` 恒正）。 -/
theorem twoTreeMSCModel_evidence_pos (t₁ t₂ : ℝ) (ht₁ : 0 ≤ t₁) :
    0 < (twoTreeMSCModel t₁ t₂ ht₁).evidence := by
  refine FiniteBayesModel.evidence_pos_of_pos _ (i := 1) ⟨?_, ?_⟩
  · simp [twoTreeMSCModel]
  · simpa [twoTreeMSCModel] using mscDiscordant_pos t₂

/-- ★★ **后验归一到 `1`**（端到端最小例）。 -/
theorem twoTreeMSCModel_posterior_sum_one (t₁ t₂ : ℝ) (ht₁ : 0 ≤ t₁) :
    ∑ i, (twoTreeMSCModel t₁ t₂ ht₁).posterior i = 1 :=
  FiniteBayesModel.posterior_sum_one _ (ne_of_gt (twoTreeMSCModel_evidence_pos t₁ t₂ ht₁))

/-- ★★★ **一致观测下后验严格偏向一致树**：`t > 0` 时
`posterior 0 > 1/2`（先验是 `1/2`，故这是**真正的贝叶斯更新方向**：
`mscDiscordant t < mscConcordant t`，见 `MSCProof`）。 -/
theorem twoTreeMSCModel_posterior_favors_concordant (t : ℝ) (ht : 0 < t) :
    (1 : ℝ) / 2 < (twoTreeMSCModel t t ht.le).posterior 0 := by
  have hlt : mscDiscordant t < mscConcordant t := mscDiscordant_lt_mscConcordant ht
  have hC : 0 < mscConcordant t := mscConcordant_pos ht
  have hD : 0 < mscDiscordant t := mscDiscordant_pos t
  have hZ : (twoTreeMSCModel t t ht.le).evidence
      = 1 / 2 * mscConcordant t + 1 / 2 * mscDiscordant t := by
    simp [FiniteBayesModel.evidence, twoTreeMSCModel, Fin.sum_univ_two]
  have hP : (twoTreeMSCModel t t ht.le).posterior 0
      = (1 / 2 * mscConcordant t)
        / (1 / 2 * mscConcordant t + 1 / 2 * mscDiscordant t) := by
    simp only [FiniteBayesModel.posterior]
    rw [hZ]
    simp [twoTreeMSCModel]
  have hY : (1 : ℝ) / 2 * mscConcordant t + 1 / 2 * mscDiscordant t ≠ 0 := by linarith
  have hsub : (1 / 2 * mscConcordant t)
        / (1 / 2 * mscConcordant t + 1 / 2 * mscDiscordant t) - 1 / 2
      = (1 / 2 * mscConcordant t - 1 / 2 * mscDiscordant t)
        / (2 * (1 / 2 * mscConcordant t + 1 / 2 * mscDiscordant t)) := by
    field_simp
    ring
  rw [hP, ← sub_pos, hsub]
  exact div_pos (by linarith) (by linarith)

/-- ★C **最小例的数值实例**（`t₁ = t₂ = 1`）：后验严格偏向一致树。 -/
theorem twoTreeMSCModel_posterior_favors_concordant_one :
    (1 : ℝ) / 2 < (twoTreeMSCModel 1 1 (by norm_num)).posterior 0 :=
  twoTreeMSCModel_posterior_favors_concordant 1 (by norm_num)

/-- 反空真（`example`）：有限贝叶斯 MSC 模型**有居民**，证据严格为正，
且 `t = 1` 时**两棵候选树的后验都严格为正**（**非退化**）。 -/
example : ∃ M : FiniteBayesModel (Fin 2),
    0 < M.evidence ∧ 0 < M.posterior 0 ∧ 0 < M.posterior 1 := by
  have hZ : 0 < (twoTreeMSCModel 1 1 (by norm_num)).evidence :=
    twoTreeMSCModel_evidence_pos 1 1 (by norm_num)
  refine ⟨twoTreeMSCModel 1 1 (by norm_num), hZ, ?_, ?_⟩
  · exact (FiniteBayesModel.posterior_pos_iff _ hZ 0).mpr
      ⟨by simp [twoTreeMSCModel],
        by simpa [twoTreeMSCModel] using mscConcordant_pos (by norm_num : (0 : ℝ) < 1)⟩
  · exact (FiniteBayesModel.posterior_pos_iff _ hZ 1).mpr
      ⟨by simp [twoTreeMSCModel], by simpa [twoTreeMSCModel] using mscDiscordant_pos 1⟩

/-! ## 4. ★B 反例检查（汇总结论）

| 问题 | 答案 | 依据 |
|---|---|---|
| **后验一定与先验有相同支撑吗？** | **不一定**，`支撑(后验) = 支撑(先验) ∩ 支撑(似然)` | §1.1 `posterior_support_lt_prior_support`（先验均匀、似然 `(1,0)` ⇒ 后验支撑严格收缩）＋ `posterior_pos_iff` ν `posterior_eq_zero_of_prior_eq_zero` |
| **似然为 `0` 时后验怎么定义？** | 抽象有限层：`Z = 0`，`ρᵢLᵢ/Z` 按 `ℝ` 的 `_/0 = 0` **不是**概率分布（和 `= 0 ≠ 1`）；**MSC 层：不会发生** | §1.2 `zeroLikModel_posterior_not_prob`；§2 `kingmanMSCMeasure_deep_pos`（`e^{−a}e^{−b} > 0` 处处） |
| **MSC 先验 `ρ` 需要额外正则性吗？** | **不需要**：`posteriorDeep` 对**任意**概率先验都归一到 `1` | `posteriorDeep_univ_eq_one` |
| **多棵树先验加权和会破坏归一吗？** | **不会** | §2 `kingmanMSCMeasure_add`；§3 `twoTreeMixtureModel_posterior_sum_one` | -/

/-! ## 5. 显式缺口（超范围项，**不硬编**） -/

/-- **缺口（X6-A）：一般连续先验下的后验一致性 / MCMC**。

Heled–Drummond (2010) Eq. (1)（**496–510** 行）与 Rannala–Yang (2003) (4)(5) 式
（**355–370** 行）给出的对象，是**连续**物种树空间上的后验，其计算靠
**Metropolis–Hastings MCMC**（Heled–Drummond **510–520** 行明言「直接算这个积分不可能」）。

本文件给出的是：**有限树空间层**（§1、§3）与**已在库内固定先验 `ρ` 的测度层**（§2）。
**缺的是**：
1. `ρ` 取**一般连续先验**（含 `fBD` 生灭过程先验、(5) 式的先验密度、种群大小先验 `PN`）时
   的**多位点**后验 —— 本库的 `MSCKingmanMeasure` 文件头 §2 明确把枝长先验留作**参数**；
2. 该后验的**一致性**（后验质量在真树邻域上 → `1`）；
3. MCMC 链的**平稳分布 = 该后验**这一正确性定理。

⇒ 落为显式 `Prop` 缺口（`references/` 有文献，但本库没有连续先验 / MCMC 核 / 后验一致性的器材）。 -/
def ContinuousPriorPosteriorConsistencyGap : Prop :=
  ∀ {Θ : Type*} [MeasurableSpace Θ] [TopologicalSpace Θ]
    (prior : Measure Θ) [IsProbabilityMeasure prior]
    (lik : ℕ → Θ → ℝ≥0∞) (trueθ : Θ),
    ∃ post : ℕ → Measure Θ,
      (∀ n, IsProbabilityMeasure (post n)) ∧
        (∀ n, post n = prior.withDensity fun θ => lik n θ / ∫⁻ θ', lik n θ' ∂prior) ∧
        ∀ U : Set Θ, IsOpen U → trueθ ∈ U →
          Tendsto (fun n : ℕ => post n U) atTop (𝓝 1)

/-- **缺口（X6-B）：多位点后验集中（有限树空间版）**。

§1 只做了**单**位点的 Bayes 层（`evidence = ∑ᵢ ρᵢLᵢ`）。
「`n` 个**独立**位点 ⇒ 似然取乘积 ⇒ 后验随 `n → ∞` 集中到真树」需要：
多位点独立性、乘积似然、以及似然比 `Lᵢ(n)/L_{i₀}(n)` 的指数衰减 ——
这三样本库**都没有**（`MSCSampling.converges` 在 `Phylo/Stat/MSC.lean` 里仍是**公理化**的
大数定律，且是**确定性**的 `ε`-接近形式）。

⇒ 落为显式 `Prop` 缺口：本文件**不**声称后验一致性。 -/
def MultiLocusPosteriorConcentrationGap : Prop :=
  ∀ {ι : Type*} [Fintype ι] [DecidableEq ι] (i₀ : ι) (prior : ι → ℝ),
    (∀ i, 0 ≤ prior i) → (∑ i, prior i = 1) → 0 < prior i₀ →
      ∀ perLocus : ι → ℕ → ℝ, (∀ i n, 0 ≤ perLocus i n) →
        (∀ i, i ≠ i₀ → ∃ c : ℝ, 0 < c ∧ ∀ᶠ n in atTop,
          perLocus i n ≤ Real.exp (-c * n) * perLocus i₀ n) →
          Tendsto (fun n : ℕ =>
            perLocus i₀ n * prior i₀ / ∑ i, perLocus i n * prior i) atTop (𝓝 1)

end Phylo.Stat.MSCBayes

end
