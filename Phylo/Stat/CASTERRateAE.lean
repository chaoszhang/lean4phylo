/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.Stat.SiteRateMixture
import Phylo.Stat.MSCKingmanMeasure

/-!
# `Phylo.Stat.CASTERRateAE` —— 端到端：把速率混合模型接进 CASTER 引擎（W13e）

文献：Zhang, Nielsen & Mirarab (2025), *Science* **387**(6737) eadk9688，
**Supplementary** `sm.tex` 的 `Proof of Theorem 1` 前置 remark（1269–1285 行）。

## 这一批在整条链里的位置

```
W13b+c（Phylo/Stat/SiteRateMixture.lean）
  速率混合层 Ã / f̃、命题 A 的保持、Ã 版 PropAData、a.e. 正性
        │
        ▼
本文件（W13e）
  §1  可测性器材（fun_prop 看不见 `Phylo.JC.e` 的那一层，显式展开）
  §2  ★★ 测度层缺口 B1/G2 的剩余部分：内枝长在 `¬ deep` 上 a.e. 正（对**任意**概率 ρ）
  §3  把 `hf_pos` 从 `fbar_pos` 推出来（不再当假设传）
  §4  ★★★ 用 `abarPropAData` 造 `TopoIdeal`（`propB` 由库内 `propB_of_bridge` **供给**）
  §5  ★★★ Kingman ＋ 确定物种树（ρ = dirac）下把 `hf_int` / `hpos` / `hint` **全部证掉**
  §6  ★★ 可组合收口：a.e. 收敛 ⇒ a.e. 一致（与 W13d 的接口）
  §7  ★ 退化一致性（规格 §8④）：`r ≡ 1, ρ ≡ 1` ⇒ 整条链退回 `jc69PropADataK`
  §8  反空洞：具体实例 ＋ `exists_gap` 的非空见证
```

## ★ 本批消掉了哪三个假设

`Phylo.Stat.CASTERTopo.TopoIdeal.ofModel` 的参数里有三个**解析**假设：

| 假设 | 旧状态 | 本批 |
|---|---|---|
| `hf_pos`（`¬deep ⇒ f > 0`，ν-a.e.） | 假设 | **定理**（§3 ＋ §2，只需「`¬deep` 时内枝长正」） |
| `hf_int`（幅度可积） | 假设 | **定理**（§5，确定物种树下 `f̃` 在像上取常值） |
| `hint`（正文条件 (2)「权重一致有界」） | 假设 | **定理**（§5，同上，用 `‖τd‖ ≤ 1`） |

`hdeep`（`deep` 可测）与 `hpos`（`¬deep` 有正质量）**库内早已是定理**
（`measurableSet_kingmanMSCTopoSym_deep` / `kingmanMSCMeasure_dirac_notDeep_pos`）✓。
剩下的**只有 `hconv`（大数定律）** —— 那是 W13d 的交付物，本文件给出接口（§6）。

## ★★ §2 的 ★D 结论（**与派单口径不同，请以本节为准**）

派单把缺口写成「`∀ᵐ θ ∂ν, 0 < θ.1.2`（内枝长 a.e. 严格正）」。**逐字读它是假的**：

* 取 `ρ = Measure.dirac (leaf, 0, 0)`（合法的**概率**测度），则
  `toKingmanΘ p` 的内枝长恒 `= 0 + 0 = 0` ⇒ `ν {θ | θ.1.2 ≤ 0} = 1`
  ⇒ `¬ ∀ᵐ θ ∂ν, 0 < θ.1.2`（完整证明见 `not_ae_pos_lx_dirac_zero`）。
* **正确的形态**是**条件式**：`∀ᵐ θ ∂ν, ¬ S.deep θ → 0 < θ.1.2`。
  它在**对任意概率 ρ、不加任何额外假设**时**可证**（`notDeep_lx_ae`）：
  原像里 `a + b ≤ 0` 逼出 `a = b = 0`，此时 `¬deep` 需要 `w₁ ≤ 0 ∨ w₂ ≤ 0`，
  而 `sojournLaw 2 (Iic 0) = 0`（指数律无原子）。
* 这**严格强于**「先假设 `ρ {a + b = 0} = 0`」那条路：本文件不需要它 ✓。
* 且这正是 `propB_of_bridge` 要的形状：`hf_pos` 的前件就是 `¬ S.deep θ` ✓。

## ⚠️ 诚实边界（逐条，不藏）

1. **`hf_int` / `hint` 只在「确定物种树」（`ρ = Measure.dirac (leaf, a, b)`）下被消掉**。
   一般 ρ 下 `Ã` 关于**叶长**无一致界（`Phylo.JC.e t = exp(−(4/3)t)` 在 `t → −∞` 时爆炸），
   所以 `hint` 需要「ρ-a.e. 叶长有界」这类**对物种树侧先验的条件**。
   本文件因此在一般 ρ 上只把 `hdeep` / `hf_pos` / `hpos` / `Θ` 层消掉（`abarTopoIdeal`），
   在确定物种树上把**全部**解析假设消掉（`abarTopoIdeal_kingman`）。
2. **`hconv` 仍是假设** —— 它是 W13d 的块级大数定律，本文件**不重新定义**它（规格 §9）。
   §6 给出的是**可组合收口**：吃 W13d 的输出形状，吐 a.e. 一致性。
3. **θ 的枝长口径**：沿用 `SiteRateMixture` 的 `scale`（逐基因树逐枝**常数**速率乘子），
   比「物种树各枝独立抽速率」粗一档 —— 完整交代见 `SiteRateMixture.lean` 文件头 §诚实边界 2。
4. **π / κ 仍只登记不使用**：本文件的 `abarPropAData` 是 JC69 端的（`π ≡ 1/4`、无 κ）；
   F84 / LM1 的 `Ã` 属 W13h 的另一条线。
5. **`set_option linter.style.haveILetI false`**：本文件与库内 `MSCKingmanMeasure.lean:89`、
   `KingmanCoalescent.lean:130` 采用同一处置 —— 若干证明需要在目标里登记
   `IsProbabilityMeasure` / `SFinite` 实例（`Measure.map_apply`、`measure_univ` 从实例取），
   该 linter 会因此报风格告警。这只关风格，**不改任何陈述**。
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

noncomputable section

universe u

open MeasureTheory
open scoped NNReal ENNReal

namespace Phylo.Stat.CASTERRateAE

open Phylo.Stat.CASTERWeights (Topo)
open Phylo.Stat.CASTEREngine
open Phylo.Stat.CASTERBridge
open Phylo.Stat.CASTERTopo
open Phylo.Stat.CASTERGeneTree
open Phylo.Stat.MSCKingman
open Phylo.Stat.MSCKingmanMeasure
open Phylo.Stat.KingmanCoalescent
open Phylo.Stat.SiteRateMixture

variable {X : Type u} [Fintype X] [DecidableEq X]

/-! ## 1. 可测性器材

`fun_prop` **看不见** `Phylo.JC.e`（它是普通 `def`，没有 `Measurable` 实例），
所以这里把所有相关定义**显式展开**后再交给 `fun_prop`。
展开集合用 `macro` 固定，避免各处口径不一致。 -/

/-- 展开 JC69 权重链上**全部**相关定义（`fun_prop` 的前置）。 -/
macro "jc_unfold" : tactic =>
  `(tactic|
    (simp only [Phylo.Stat.SiteRateMixture.SiteRateModel.Abar,
       Phylo.Stat.SiteRateMixture.SiteRateModel.fbar,
       Phylo.Stat.SiteRateMixture.SiteRateModel.ampScaled,
       Phylo.Stat.SiteRateMixture.SiteRateModel.scale,
       Phylo.Stat.CASTERGeneTree.jc69PropAData,
       Phylo.Stat.CASTERGeneTree.geneScore,
       Phylo.Stat.CASTERGeneTree.jc69Amp,
       Phylo.Stat.CASTERGeneTree.canonLen,
       Phylo.JC.patternProb, Phylo.JC.kernel, Phylo.JC.trans, Phylo.JC.off, Phylo.JC.ind,
       Phylo.JC.e]))

/-- ★ **`Ã θ T' T` 关于 θ 可测**（`M.r` / `M.ρ` / `M.w` 对 θ 都是常数，
故这只是一串有限和 ＋ `exp` 的复合）。 -/
theorem measurable_Abar (M : SiteRateModel) (T' T : Topo) :
    Measurable fun θ : KingmanΘ => M.Abar θ T' T := by
  jc_unfold
  fun_prop

/-- ★ **`f̃` 关于 θ 可测**。 -/
theorem measurable_fbar (M : SiteRateModel) :
    Measurable fun θ : KingmanΘ => M.fbar θ := by
  jc_unfold
  fun_prop

/-- ★ **`Kingmanτd θ T` 关于 θ 可测**（条件只依赖两个 `Bool` 分量）。 -/
theorem measurable_Kingmanτd (T : Topo) :
    Measurable fun θ : KingmanΘ => Kingmanτd θ T := by
  simp only [Phylo.Stat.MSCKingman.Kingmanτd, Phylo.Stat.MSCKingman.KingmanDeep]
  refine Measurable.ite ?_ measurable_const measurable_const
  exact MeasurableSet.inter ((measurable_fst.comp measurable_snd) (measurableSet_singleton true))
    ((measurable_snd.comp measurable_snd) (measurableSet_singleton true))

/-- ★ **`hint` 的被积函数可测**。 -/
theorem measurable_abarHint (M : SiteRateModel) (T : Topo) :
    Measurable fun θ : KingmanΘ =>
      ∑ T' : Topo, kingmanMSCTopoSym.τd θ T' * M.Abar θ T' T := by
  have hτd : ∀ T' : Topo, Measurable fun θ : KingmanΘ => kingmanMSCTopoSym.τd θ T' :=
    fun T' => measurable_Kingmanτd T'
  exact Finset.measurable_sum Finset.univ fun T' _ => (hτd T').mul (measurable_Abar M T' T)

/-! ## 2. ★★ 测度层缺口 B1/G2 的剩余部分：内枝长在 `¬ deep` 上 a.e. 正 -/

/-- ★★★ **（一般 ρ）`¬ deep` 时内枝长 a.e. 严格正** —— 缺口 B1/G2 的剩余部分。

`ν = kingmanMSCMeasure ρ` 的像点上 `θ.1.2 = a + b`、`deep = (a < w₁) ∧ (b < w₂)`
（`a b : ℝ≥0`）。故坏集的原像是

`{p | (w₁ ≤ a ∨ w₂ ≤ b) ∧ a + b ≤ 0} ⊆ {p | w₁ ≤ 0 ∨ w₂ ≤ 0}`

（`a, b ≥ 0` ⇒ `a + b ≤ 0` 逼出 `a = b = 0`），而 `sojournLaw 2 (Iic 0) = 0`
（指数律无原子）⇒ 该集零测。

★ 这条**不需要任何对 ρ 的额外假设**（ρ 只用来取 `measure_univ = 1`）——
它严格强于「先假设 `ρ {a + b = 0} = 0`」。 -/
theorem notDeep_lx_ae (ρ : Measure ((Fin 4 → ℝ) × ℝ≥0 × ℝ≥0)) [IsProbabilityMeasure ρ] :
    ∀ᵐ θ ∂(kingmanMSCMeasure ρ), ¬ kingmanMSCTopoSym.deep θ → 0 < Prod.snd (Prod.fst θ) := by
  rw [ae_iff]
  have hset : MeasurableSet {θ : KingmanΘ | ¬ kingmanMSCTopoSym.deep θ ∧
      Prod.snd (Prod.fst θ) ≤ 0} :=
    (measurableSet_notDeep).inter ((measurable_snd.comp measurable_fst) measurableSet_Iic)
  have hEq : {θ : KingmanΘ | ¬ (¬ kingmanMSCTopoSym.deep θ → 0 < Prod.snd (Prod.fst θ))}
      = {θ : KingmanΘ | ¬ kingmanMSCTopoSym.deep θ ∧ Prod.snd (Prod.fst θ) ≤ 0} := by
    ext θ
    simp only [Set.mem_ofPred_eq, not_imp, not_lt]
  rw [hEq, kingmanMSCMeasure, Measure.map_apply measurable_toKingmanΘ hset]
  have hγ : sojournLaw 2 (Set.Iic (0 : ℝ)) = 0 := by
    rw [sojournLaw, expMeasure_Iic_eq (Coalescent.kingmanRate_pos (by norm_num)) 0,
      ite_eq_left le_rfl]
    simp
  have hzero : (ρ.prod ((sojournLaw 2).prod (sojournLaw 2)))
      (((Set.univ : Set ((Fin 4 → ℝ) × ℝ≥0 × ℝ≥0)) ×ˢ
          (Set.Iic (0 : ℝ) ×ˢ (Set.univ : Set ℝ))) ∪
        ((Set.univ : Set ((Fin 4 → ℝ) × ℝ≥0 × ℝ≥0)) ×ˢ
          ((Set.univ : Set ℝ) ×ˢ (Set.Iic (0 : ℝ))))) = 0 := by
    haveI h1 : IsProbabilityMeasure (sojournLaw 2) := isProbabilityMeasure_sojournLaw (by norm_num)
    haveI h2 : IsProbabilityMeasure ((sojournLaw 2).prod (sojournLaw 2)) := inferInstance
    refine measure_union_null ?_ ?_
    · rw [Measure.prod_prod, Measure.prod_prod, measure_univ, measure_univ, hγ]
      simp
    · rw [Measure.prod_prod, Measure.prod_prod, measure_univ, measure_univ, hγ]
      simp
  refine measure_mono_null (fun p hp => ?_) hzero
  rcases p with ⟨⟨leaf, a, b⟩, w1, w2⟩
  have hlx : (a : ℝ) + (b : ℝ) ≤ 0 := hp.2
  have hnd : ¬ KingmanDeep (toKingmanΘ ((leaf, a, b), (w1, w2))) := hp.1
  have ha : (a : ℝ) = 0 := by
    have ha0 : (0 : ℝ) ≤ (a : ℝ) := a.coe_nonneg
    have hb0 : (0 : ℝ) ≤ (b : ℝ) := b.coe_nonneg
    linarith
  have hb : (b : ℝ) = 0 := by
    have ha0 : (0 : ℝ) ≤ (a : ℝ) := a.coe_nonneg
    have hb0 : (0 : ℝ) ≤ (b : ℝ) := b.coe_nonneg
    linarith
  have hw : w1 ≤ 0 ∨ w2 ≤ 0 := by
    by_contra h
    simp only [not_or, not_le] at h
    have hdec : decide ((a : ℝ) < w1) = true ∧ decide ((b : ℝ) < w2) = true := by
      rw [decide_eq_true_eq, decide_eq_true_eq]
      exact ⟨by linarith [h.1], by linarith [h.2]⟩
    exact hnd hdec
  rcases hw with hw | hw
  · exact Or.inl ⟨Set.mem_univ _, hw, Set.mem_univ _⟩
  · exact Or.inr ⟨Set.mem_univ _, Set.mem_univ _, hw⟩

/-- ★★★ **★D 反例（无条件的「内枝长 a.e. 正」是假命题）**：
取 `a = b = 0`，则 `toKingmanΘ` 的像上内枝长恒为 `0` ⇒ `{θ | ¬ 0 < θ.1.2}` 是**全空间**
⇒ 它在 ν 下的测度是 `1`。故「`∀ᵐ θ ∂ν, 0 < θ.1.2`」**不成立**。

（这正是派单口径需要更正之处；正确形态是上面的 `notDeep_lx_ae`。） -/
theorem not_ae_pos_lx_dirac_zero (leaf : Fin 4 → ℝ) :
    ¬ (∀ᵐ θ ∂(kingmanMSCMeasure (Measure.dirac (leaf, (0 : ℝ≥0), (0 : ℝ≥0)))),
        0 < Prod.snd (Prod.fst θ)) := by
  intro h
  have h0 : kingmanMSCMeasure (Measure.dirac (leaf, (0 : ℝ≥0), (0 : ℝ≥0)))
      {θ : KingmanΘ | ¬ (0 < Prod.snd (Prod.fst θ))} = 0 := ae_iff.mp h
  have hset : MeasurableSet {θ : KingmanΘ | ¬ (0 < Prod.snd (Prod.fst θ))} :=
    ((measurable_snd.comp measurable_fst) measurableSet_Ioi).compl
  have hg : Measurable (fun v : ℝ × ℝ => toKingmanΘ ((leaf, (0 : ℝ≥0), (0 : ℝ≥0)), v)) :=
    measurable_toKingmanΘ.comp (measurable_const.prodMk measurable_id)
  have hpre : (fun v : ℝ × ℝ => toKingmanΘ ((leaf, (0 : ℝ≥0), (0 : ℝ≥0)), v)) ⁻¹'
      {θ : KingmanΘ | ¬ (0 < Prod.snd (Prod.fst θ))} = Set.univ := by
    ext v
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_univ, iff_true, not_lt, toKingmanΘ]
    norm_num
  haveI h1 : IsProbabilityMeasure (sojournLaw 2) := isProbabilityMeasure_sojournLaw (by norm_num)
  haveI h2 : IsProbabilityMeasure ((sojournLaw 2).prod (sojournLaw 2)) := inferInstance
  have huniv : kingmanMSCMeasure (Measure.dirac (leaf, (0 : ℝ≥0), (0 : ℝ≥0)))
      {θ : KingmanΘ | ¬ (0 < Prod.snd (Prod.fst θ))} = 1 := by
    rw [kingmanMSCMeasure_dirac_eq_map, Measure.map_apply hg hset, hpre, measure_univ]
  rw [huniv] at h0
  exact one_ne_zero h0

/-- ★★ **确定物种树（`a + b > 0`）下内枝长 a.e. 严格正**。
`toKingmanΘ` 的像上内枝长恒为 `a + b > 0`，故与 `{θ.1.2 ≤ 0}` 不相交
（库内 `kingmanMSCMeasure_dirac_lx_nonpos` 正是这条）。 -/
theorem dirac_lx_pos_ae (leaf : Fin 4 → ℝ) (a b : ℝ≥0) (hab : 0 < (a : ℝ) + (b : ℝ)) :
    ∀ᵐ θ ∂(kingmanMSCMeasure (Measure.dirac (leaf, a, b))), 0 < Prod.snd (Prod.fst θ) := by
  rw [ae_iff]
  have hEq : {θ : KingmanΘ | ¬ (0 < Prod.snd (Prod.fst θ))}
      = {θ : KingmanΘ | Prod.snd (Prod.fst θ) ≤ 0} := by
    ext θ
    simp only [Set.mem_ofPred_eq, not_lt]
  rw [hEq]
  exact kingmanMSCMeasure_dirac_lx_nonpos leaf a b hab

/-- **确定物种树下 `KingmanΘ` 的代表点**（像点的叶长与内枝长：`(leaf, a + b)`；
`Bool` 分量任取 `false` —— `Ã` / `f̃` 与它们无关，见 `Abar_eq_of_fst_eq`）。 -/
def diracBase (leaf : Fin 4 → ℝ) (a b : ℝ≥0) : KingmanΘ :=
  ((leaf, ((a : ℝ) + (b : ℝ))), (false, false))

/-- ★ **确定物种树（`ρ = dirac (leaf, a, b)`）下 `θ` 的第一个分量 a.e. 是固定常数**
（像点的叶长与内枝长都不随机：`θ.1 = (leaf, a + b)`）。 -/
theorem dirac_fst_ae (leaf : Fin 4 → ℝ) (a b : ℝ≥0) :
    ∀ᵐ θ ∂(kingmanMSCMeasure (Measure.dirac (leaf, a, b))),
      Prod.fst θ = (leaf, ((a : ℝ) + (b : ℝ))) := by
  rw [ae_iff]
  have hset : MeasurableSet {θ : KingmanΘ | Prod.fst θ ≠ (leaf, ((a : ℝ) + (b : ℝ)))} :=
    (measurable_fst (measurableSet_singleton _)).compl
  have hg : Measurable (fun v : ℝ × ℝ => toKingmanΘ ((leaf, a, b), v)) :=
    measurable_toKingmanΘ.comp (measurable_const.prodMk measurable_id)
  rw [kingmanMSCMeasure_dirac_eq_map, Measure.map_apply hg hset]
  have hpre : (fun v : ℝ × ℝ => toKingmanΘ ((leaf, a, b), v)) ⁻¹'
      {θ : KingmanΘ | Prod.fst θ ≠ (leaf, ((a : ℝ) + (b : ℝ)))} = ∅ := by
    ext v
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_not,
      toKingmanΘ]
  rw [hpre, measure_empty]

/-- ★ **`Ã` 只依赖 θ 的第一个分量**（`scale` 只用到 `Prod.fst θ`）。 -/
theorem Abar_eq_of_fst_eq (M : SiteRateModel) {θ θ' : KingmanΘ}
    (h : Prod.fst θ = Prod.fst θ') (T' r : Topo) : M.Abar θ T' r = M.Abar θ' T' r := by
  simp only [Phylo.Stat.SiteRateMixture.SiteRateModel.Abar,
    Phylo.Stat.SiteRateMixture.SiteRateModel.scale]
  rw [h]

/-- ★ **`f̃` 只依赖 θ 的第一个分量**。 -/
theorem fbar_eq_of_fst_eq (M : SiteRateModel) {θ θ' : KingmanΘ}
    (h : Prod.fst θ = Prod.fst θ') : M.fbar θ = M.fbar θ' := by
  simp only [Phylo.Stat.SiteRateMixture.SiteRateModel.fbar,
    Phylo.Stat.SiteRateMixture.SiteRateModel.scale]
  rw [h]

/-- ★★ **确定物种树下 `f̃` 是常数**（用于 `hf_int`）。 -/
theorem fbar_ae_const_dirac (M : SiteRateModel) (leaf : Fin 4 → ℝ) (a b : ℝ≥0) :
    M.fbar =ᵐ[kingmanMSCMeasure (Measure.dirac (leaf, a, b))]
      (fun _ => M.fbar (diracBase leaf a b)) :=
  (dirac_fst_ae leaf a b).mono fun _ hθ =>
    fbar_eq_of_fst_eq M (θ' := diracBase leaf a b) hθ

/-- ★★ **确定物种树下 `Ã θ T' T` 对 θ 是常数**（用于 `hint`）。 -/
theorem abar_ae_const_dirac (M : SiteRateModel) (leaf : Fin 4 → ℝ) (a b : ℝ≥0) (T' T : Topo) :
    (fun θ : KingmanΘ => M.Abar θ T' T)
      =ᵐ[kingmanMSCMeasure (Measure.dirac (leaf, a, b))]
      (fun _ => M.Abar (diracBase leaf a b) T' T) :=
  (dirac_fst_ae leaf a b).mono fun _ hθ =>
    Abar_eq_of_fst_eq M (θ' := diracBase leaf a b) hθ T' T

/-! ## 3. `hf_pos`：从 `fbar_pos`（W13b+c）推出来 -/

/-- ★★★ **`propB_of_bridge` 要的 `hf_pos` 形状**：
`∀ᵐ θ ∂ν, ¬ S.deep θ → 0 < f̃ θ`，**条件只是「`¬deep` 时内枝长正」**。 -/
theorem fbar_hf_pos_ae (M : SiteRateModel) (S : MSCTopoSym KingmanΘ) (ν : Measure KingmanΘ)
    (hlx : ∀ᵐ θ ∂ν, ¬ S.deep θ → 0 < Prod.snd (Prod.fst θ)) :
    ∀ᵐ θ ∂ν, ¬ S.deep θ → 0 < M.abarPropAData.f θ :=
  hlx.mono fun θ hθ hnd => M.fbar_pos θ (hθ hnd)

/-! ## 4. ★★★ 用 `abarPropAData` 造 `TopoIdeal`（`propB` 由库内 `propB_of_bridge` 供给）

规格 §5.2 的「省下大量工作」落地：**不新增 `TopoIdeal` 定义**，
只把 `P.A` 换成 `Ã`、`P.f` 换成 `f̃` 再喂 `TopoIdeal.ofModel`。 -/

/-- ★★★ **速率混合模型的 `TopoIdeal`**：`W S hS T = expWeight (ν S hS) (M S hS).τd Ã T`。

唯一与 `ofModel` 不同的地方是 `hf_pos` **不再是参数**：它由 `fbar_hf_pos_ae` 供给，
故本定义只要求 `hlx`（`¬deep` 时内枝长正）、`hf_int`（幅度可积）、`hpos`、`hint`。
★ `propB` 字段由 ★★★ `Phylo.Stat.CASTERTopo.propB_of_bridge` 供给
（见 ★★ `abarTopoIdeal_propB_eq_propB_of_bridge` 的 `rfl` 见证）。 -/
noncomputable def abarTopoIdeal (M : SiteRateModel) (S : MSCTopoSym KingmanΘ)
    (ν : Measure KingmanΘ) [IsProbabilityMeasure ν]
    (hdeep : MeasurableSet {θ | S.deep θ})
    (hlx : ∀ᵐ θ ∂ν, ¬ S.deep θ → 0 < Prod.snd (Prod.fst θ))
    (hf_int : Integrable M.abarPropAData.f ν)
    (hpos : 0 < ν {θ | ¬ S.deep θ})
    (hint : ∀ T : Topo,
      Integrable (fun θ => ∑ T' : Topo, S.τd θ T' * M.abarPropAData.A θ T' T) ν) :
    TopoIdeal X :=
  TopoIdeal.ofModel S ν hdeep M.abarPropAData hf_int (fbar_hf_pos_ae M S ν hlx) hpos hint

/-- ★★★ **`propB` 字段确实由 `propB_of_bridge` 供给 —— 不是假设**。
这条 `rfl` 等式说明 `abarTopoIdeal` 的 `propB` 字段就是
`Phylo.Stat.CASTERTopo.propB_of_bridge` 在该参数上的取值
（规格 §7.8 的结论：间隙 δ 不需要 `f` 的一致下界，只要 `propB` 的**严格**不等式）。 -/
theorem abarTopoIdeal_propB_eq_propB_of_bridge (M : SiteRateModel) (S : MSCTopoSym KingmanΘ)
    (ν : Measure KingmanΘ) [IsProbabilityMeasure ν]
    (hdeep : MeasurableSet {θ | S.deep θ})
    (hlx : ∀ᵐ θ ∂ν, ¬ S.deep θ → 0 < Prod.snd (Prod.fst θ))
    (hf_int : Integrable M.abarPropAData.f ν)
    (hpos : 0 < ν {θ | ¬ S.deep θ})
    (hint : ∀ T : Topo,
      Integrable (fun θ => ∑ T' : Topo, S.τd θ T' * M.abarPropAData.A θ T' T) ν)
    (S₀ : Finset X) (hS₀ : S₀.card = 4) (T : Topo) (hT : T ≠ Topo.ab_cd) :
    (abarTopoIdeal M S ν hdeep hlx hf_int hpos hint).propB S₀ hS₀ T hT
      = propB_of_bridge S ν hdeep M.abarPropAData hf_int (fbar_hf_pos_ae M S ν hlx) hpos
          (hint .ab_cd) (hint .ac_bd) (hint .ad_bc) T hT := rfl

/-- ★★ **`W` 的定义展开**：`abarTopoIdeal` 的权重表就是 `expWeight ν S.τd Ã`（逐字）。 -/
theorem abarTopoIdeal_W (M : SiteRateModel) (S : MSCTopoSym KingmanΘ)
    (ν : Measure KingmanΘ) [IsProbabilityMeasure ν]
    (hdeep : MeasurableSet {θ | S.deep θ})
    (hlx : ∀ᵐ θ ∂ν, ¬ S.deep θ → 0 < Prod.snd (Prod.fst θ))
    (hf_int : Integrable M.abarPropAData.f ν)
    (hpos : 0 < ν {θ | ¬ S.deep θ})
    (hint : ∀ T : Topo,
      Integrable (fun θ => ∑ T' : Topo, S.τd θ T' * M.abarPropAData.A θ T' T) ν) :
    (abarTopoIdeal (X := X) M S ν hdeep hlx hf_int hpos hint).W
      = fun _ _ T => expWeight ν S.τd M.Abar T := rfl

/-! ## 5. ★★★ Kingman ＋ 确定物种树：`hf_int` / `hpos` / `hint` 全部证掉 -/

/-- ★ **`|Kingmanτd θ T| ≤ 1`**（取值只在 `{1/3, 1, 0}` 中）。 -/
theorem abs_Kingmanτd_le_one (θ : KingmanΘ) (T : Topo) : |Kingmanτd θ T| ≤ 1 := by
  by_cases h : KingmanDeep θ
  · rw [Kingmanτd, ite_eq_left h]
    norm_num
  · rw [Kingmanτd, ite_eq_right h]
    by_cases hT : T = Topo.ab_cd
    · rw [ite_eq_left hT]
      norm_num
    · rw [ite_eq_right hT]
      norm_num

/-- ★★★ **`f̃` 在确定物种树下可积**（`hf_int` 消掉）。

像点上 `f̃` 是**常数**（`dirac_fst_ae` ＋ `fbar_eq_of_fst_eq`），
故由 `Integrable.congr` 从 `integrable_const` 得到。 -/
theorem fbar_integrable_dirac (M : SiteRateModel) (leaf : Fin 4 → ℝ) (a b : ℝ≥0) :
    Integrable M.abarPropAData.f (kingmanMSCMeasure (Measure.dirac (leaf, a, b))) :=
  (integrable_const (M.fbar (diracBase leaf a b))).congr (fbar_ae_const_dirac M leaf a b).symm

/-- ★★★ **权重的一致有界积分（正文条件 (2)，`hint`）在确定物种树下可积**（`hint` 消掉）。

像点上 `Ã θ T' T` 是常数 `Ã (diracBase leaf a b) T' T`，而 `τd` 是概率权（`|τd| ≤ 1`）
⇒ 被积函数的 `‖·‖` 被常数 `∑_{T'} |Ã (diracBase leaf a b) T' T|` 控制
⇒ `Integrable.of_bound`。 -/
theorem abarHint_integrable_dirac (M : SiteRateModel) (leaf : Fin 4 → ℝ) (a b : ℝ≥0)
    (T : Topo) :
    Integrable (fun θ : KingmanΘ =>
      ∑ T' : Topo, kingmanMSCTopoSym.τd θ T' * M.abarPropAData.A θ T' T)
      (kingmanMSCMeasure (Measure.dirac (leaf, a, b))) := by
  refine Integrable.of_bound (measurable_abarHint M T).aestronglyMeasurable
    (∑ T' : Topo, |M.Abar (diracBase leaf a b) T' T|) ?_
  refine (dirac_fst_ae leaf a b).mono fun θ hθ => ?_
  have hA : ∀ T' : Topo, M.Abar θ T' T = M.Abar (diracBase leaf a b) T' T :=
    fun T' => Abar_eq_of_fst_eq M (θ' := diracBase leaf a b) hθ T' T
  calc ‖∑ T' : Topo, kingmanMSCTopoSym.τd θ T' * M.Abar θ T' T‖
      = ‖∑ T' : Topo, kingmanMSCTopoSym.τd θ T' * M.Abar (diracBase leaf a b) T' T‖ := by
        congr 1
        exact Finset.sum_congr rfl fun T' _ => by rw [hA T']
    _ ≤ ∑ T' : Topo,
          ‖kingmanMSCTopoSym.τd θ T' * M.Abar (diracBase leaf a b) T' T‖ := norm_sum_le _ _
    _ = ∑ T' : Topo,
          |kingmanMSCTopoSym.τd θ T'| * |M.Abar (diracBase leaf a b) T' T| :=
        Finset.sum_congr rfl fun T' _ => by rw [Real.norm_eq_abs, abs_mul]
    _ ≤ ∑ T' : Topo, 1 * |M.Abar (diracBase leaf a b) T' T| :=
        Finset.sum_le_sum fun T' _ =>
          mul_le_mul_of_nonneg_right (abs_Kingmanτd_le_one θ T') (abs_nonneg _)
    _ = ∑ T' : Topo, |M.Abar (diracBase leaf a b) T' T| := by
        simp

/-- ★★★ **旗舰实例（假设最少）：Kingman ＋ 确定物种树 ⇒ 完整的 `TopoIdeal`**。

与 `TopoIdeal.ofModel kingmanMSCTopoSym ν hdeep jc69PropADataK …` 的同族端点相比，
这里 `hf_int` / `hf_pos` / `hpos` **全部是定理**，`hdeep` 也是定理，
唯一剩余的参数是物种树侧的 `(leaf, a, b)` 与 `0 < a + b`。
ρ 取 `Measure.dirac (leaf, a, b)`（确定物种树）正是规格 §8④ 的退化检查口径。 -/
noncomputable def abarTopoIdeal_kingman (M : SiteRateModel) (leaf : Fin 4 → ℝ)
    (a b : ℝ≥0) (hab : 0 < (a : ℝ) + (b : ℝ)) : TopoIdeal (Fin 4) :=
  abarTopoIdeal (X := Fin 4) M kingmanMSCTopoSym
    (kingmanMSCMeasure (Measure.dirac (leaf, a, b)))
    measurableSet_kingmanMSCTopoSym_deep
    ((dirac_lx_pos_ae leaf a b hab).mono fun _ h _ => h)
    (fbar_integrable_dirac M leaf a b)
    (kingmanMSCMeasure_dirac_notDeep_pos leaf a b hab)
    (fun T => abarHint_integrable_dirac M leaf a b T)

/-- ★★★ **旗舰实例的 `W` 逐字展开**：`W S hS T = expWeight ν kingmanMSCTopoSym.τd Ã T`。 -/
theorem abarTopoIdeal_kingman_W (M : SiteRateModel) (leaf : Fin 4 → ℝ) (a b : ℝ≥0)
    (hab : 0 < (a : ℝ) + (b : ℝ)) :
    (abarTopoIdeal_kingman M leaf a b hab).W
      = fun _ _ T => expWeight (kingmanMSCMeasure (Measure.dirac (leaf, a, b)))
          kingmanMSCTopoSym.τd M.Abar T := rfl

/-- ★★★ **旗舰实例的 `propB` 逐字取出**：真拓扑 `ab|cd` 在每个 4-元集上严格最大
（内容与 `propB_of_bridge` 的输出一致，由 `abarTopoIdeal` 的定义免费得到）。 -/
theorem abarTopoIdeal_kingman_propB (M : SiteRateModel) (leaf : Fin 4 → ℝ) (a b : ℝ≥0)
    (hab : 0 < (a : ℝ) + (b : ℝ)) (S₀ : Finset (Fin 4)) (hS₀ : S₀.card = 4) (T : Topo)
    (hT : T ≠ Topo.ab_cd) :
    (abarTopoIdeal_kingman M leaf a b hab).W S₀ hS₀ T
      < (abarTopoIdeal_kingman M leaf a b hab).W S₀ hS₀ Topo.ab_cd :=
  (abarTopoIdeal_kingman M leaf a b hab).propB S₀ hS₀ T hT

/-! ## 6. ★★ 可组合收口：a.e. 收敛 ⇒ a.e. 一致（与 W13d 的接口）

⚠️ **接口形状以源码为准**：`Phylo/Stat/CASTERTopo.lean:197–199` 的大数定律假设字面是

```
hconv : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, TopoClose (emp n) M.W ε
```

注意是 **`M.W`**（`TopoIdeal` 的字段），**不是**裸的 `W`（规格 §0 的写法有出入）。

**与 W13d 的接口**：W13d（`Phylo/Stat/BlockSLLN.lean`）将给出

```
∀ᵐ ω ∂μ, ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, TopoClose (emp n ω) M.W ε
```

其中 `M` 就是本文件的 `M.abarTopoIdeal_kingman leaf a b hab`。把该形状喂给
`topo_statisticallyConsistent_ae`（或 `topo_stable_argmax_ae`）即得 a.e. 一致性。
本文件**不重复定义**块级 SLLN（规格 §9）。 -/

/-- ★★★ **a.e. 统计一致性（可组合收口）**：给定 a.e. 收敛 ＋ a.e. 逐点最大化，
得到 a.e. 最终判对。证明：在 a.e. 好的 ω 上对**确定序列** `emp · ω` 用库内
`Phylo.Stat.CASTERTopo.topo_statisticallyConsistent`（它内部走
`TopoIdeal.exists_gap` ＋ `Phylo.Stat.CASTERTopo.topo_stable_argmax`）。 -/
theorem topo_statisticallyConsistent_ae {Ω : Type*} [MeasurableSpace Ω]
    (M : TopoIdeal X) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (emp : ℕ → Ω → TopoWeight X)
    (hconv : ∀ᵐ ω ∂μ, ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, TopoClose (emp n ω) M.W ε)
    (hNE : ∃ q : TopoChoice X, ¬ IsTrueT M.qtrue q)
    {E : ℕ → Ω → TopoChoice X}
    (hE : ∀ᵐ ω ∂μ, ∀ (n : ℕ) (q : TopoChoice X),
      topoScore (emp n ω) q ≤ topoScore (emp n ω) (E n ω)) :
    ∀ᵐ ω ∂μ, ∃ N : ℕ, ∀ n ≥ N, IsTrueT M.qtrue (E n ω) :=
  (hconv.and hE).mono fun ω h =>
    topo_statisticallyConsistent M (fun n => emp n ω) h.1 hNE h.2

/-- ★★ **稳定性层的 a.e. 版本**：给定 `exists_gap` 的 δ 与 `ε < δ/(2N+1)` 的 a.e. 接近，
直接得 a.e. 一致（走库内 `Phylo.Stat.CASTERTopo.topo_stable_argmax`）。 -/
theorem topo_stable_argmax_ae {Ω : Type*} [MeasurableSpace Ω]
    (M : TopoIdeal X) (μ : Measure Ω) [IsProbabilityMeasure μ]
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : ∀ q : TopoChoice X, ¬ IsTrueT M.qtrue q →
      topoScore M.W q + δ ≤ topoScore M.W M.qtrue)
    (emp : ℕ → Ω → TopoWeight X) (n : ℕ)
    (hW : ∀ᵐ ω ∂μ, TopoClose (emp n ω) M.W
      (δ / (2 * (Fintype.card {S : Finset X // S.card = 4}) + 1)))
    {E : ℕ → Ω → TopoChoice X}
    (hmax : ∀ᵐ ω ∂μ, topoScore (emp n ω) M.qtrue ≤ topoScore (emp n ω) (E n ω)) :
    ∀ᵐ ω ∂μ, IsTrueT M.qtrue (E n ω) :=
  (hW.and hmax).mono fun _ h => topo_stable_argmax M hδ hgap h.1 h.2

/-! ## 7. ★ 退化一致性（规格 §8④）：`r ≡ 1`、`ρ ≡ 1` ⇒ 退回库内既有结果 -/

/-- ★★ **退化：`twoRate1` 的 `Ã` 版 `PropAData` 的 `A` 字段就是库内 `jc69PropADataK.A`**
（`r ≡ 1, ρ ≡ 1` ⇒ `scale θ k = θ` ⇒ `Ã` 的加权和退化成 `A`）。 -/
theorem twoRate1_abarPropAData_A_eq_jc69PropADataK (θ : KingmanΘ) (T' r : Topo) :
    SiteRateMixture.SiteRateModel.twoRate1.abarPropAData.A θ T' r
      = Phylo.Stat.MSCInstance.jc69PropADataK.A θ T' r :=
  SiteRateMixture.SiteRateModel.twoRate1_abarPropAData_A θ T' r

/-- ★★ **退化：`f̃` 就是库内 `jc69PropADataK.f`**。 -/
theorem twoRate1_abarPropAData_f_eq_jc69PropADataK (θ : KingmanΘ) :
    SiteRateMixture.SiteRateModel.twoRate1.abarPropAData.f θ
      = Phylo.Stat.MSCInstance.jc69PropADataK.f θ :=
  SiteRateMixture.SiteRateModel.twoRate1_abarPropAData_f θ

/-- ★★★ **退化一致性（识别等式层）**：`r ≡ 1, ρ ≡ 1` 时期望权重**逐字**退回
库内无速率层的 `expWeight ν τd jc69PropADataK.A`。 -/
theorem twoRate1_expWeight_eq (ν : Measure KingmanΘ) (τd : KingmanΘ → Topo → ℝ) (r : Topo) :
    expWeight ν τd SiteRateMixture.SiteRateModel.twoRate1.abarPropAData.A r
      = expWeight ν τd Phylo.Stat.MSCInstance.jc69PropADataK.A r := by
  unfold expWeight geneExpect
  refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
  exact Finset.sum_congr rfl fun T' _ => by
    simp only [twoRate1_abarPropAData_A_eq_jc69PropADataK]

/-- ★★★ **退化一致性（`TopoIdeal.W` 层，★最强探针）**：
取 `M := twoRate1`（`r ≡ 1`、`ρ ≡ 1`）时，本文件新造的 `TopoIdeal` 的权重表
**逐字等于** `TopoIdeal.ofModel … jc69PropADataK` 的权重表 ——
即整条链退回库内既有的 CASTER 端点。 -/
theorem twoRate1_W_eq (ν : Measure KingmanΘ) [IsProbabilityMeasure ν]
    (hdeep : MeasurableSet {θ | kingmanMSCTopoSym.deep θ})
    (hlx : ∀ᵐ θ ∂ν, ¬ kingmanMSCTopoSym.deep θ → 0 < Prod.snd (Prod.fst θ))
    (hf_int : Integrable SiteRateMixture.SiteRateModel.twoRate1.abarPropAData.f ν)
    (hpos : 0 < ν {θ | ¬ kingmanMSCTopoSym.deep θ})
    (hint : ∀ T : Topo, Integrable (fun θ => ∑ T' : Topo,
      kingmanMSCTopoSym.τd θ T' *
        SiteRateMixture.SiteRateModel.twoRate1.abarPropAData.A θ T' T) ν)
    (hf_intK : Integrable Phylo.Stat.MSCInstance.jc69PropADataK.f ν)
    (hf_posK : ∀ᵐ θ ∂ν, ¬ kingmanMSCTopoSym.deep θ →
      0 < Phylo.Stat.MSCInstance.jc69PropADataK.f θ)
    (hintK : ∀ T : Topo, Integrable (fun θ => ∑ T' : Topo,
      kingmanMSCTopoSym.τd θ T' * Phylo.Stat.MSCInstance.jc69PropADataK.A θ T' T) ν) :
    (abarTopoIdeal (X := Fin 4) SiteRateMixture.SiteRateModel.twoRate1 kingmanMSCTopoSym ν
        hdeep hlx hf_int hpos hint).W
      = (TopoIdeal.ofModel (X := Fin 4) kingmanMSCTopoSym ν hdeep
          Phylo.Stat.MSCInstance.jc69PropADataK hf_intK hf_posK hpos hintK).W := by
  funext S₀ hS₀ T
  exact twoRate1_expWeight_eq ν kingmanMSCTopoSym.τd T

/-! ## 8. 反空洞：具体实例 ＋ `exists_gap` 的非空见证 -/

/-- ★★ **反空洞见证**：`TopoIdeal (Fin 4)` 非空（用 `twoRate1` ＋ 确定物种树的具体实例）。 -/
theorem abarTopoIdeal_kingman_nonempty : Nonempty (TopoIdeal (Fin 4)) :=
  ⟨abarTopoIdeal_kingman SiteRateMixture.SiteRateModel.twoRate1 (0 : Fin 4 → ℝ) 1 1
    (by norm_num)⟩

/-- ★★ **反空洞（`hNE` 的可满足性）**：确实存在非真选择
（`q ≡ ac|bd` 与 `qtrue ≡ ab|cd` 在 `Finset.univ` 上不同）。 -/
theorem exists_not_true_topoChoice_fin4 :
    ∃ q : TopoChoice (Fin 4), ¬ IsTrueT (fun _ _ => Topo.ab_cd) q := by
  refine ⟨fun _ _ => Topo.ac_bd, ?_⟩
  intro h
  have hcard : (Finset.univ : Finset (Fin 4)).card = 4 := by
    rw [Finset.card_univ, Fintype.card_fin]
  exact (by decide : Topo.ac_bd ≠ Topo.ab_cd) (h Finset.univ hcard)

/-- ★★ **反空洞（间隙确实存在）**：对旗舰实例，`exists_gap` 给出真正的 `δ > 0`。 -/
theorem abarTopoIdeal_kingman_exists_gap (M : SiteRateModel) (leaf : Fin 4 → ℝ)
    (a b : ℝ≥0) (hab : 0 < (a : ℝ) + (b : ℝ)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ q : TopoChoice (Fin 4),
      ¬ IsTrueT (abarTopoIdeal_kingman M leaf a b hab).qtrue q →
        topoScore (abarTopoIdeal_kingman M leaf a b hab).W q + δ
          ≤ topoScore (abarTopoIdeal_kingman M leaf a b hab).W
              (abarTopoIdeal_kingman M leaf a b hab).qtrue :=
  (abarTopoIdeal_kingman M leaf a b hab).exists_gap exists_not_true_topoChoice_fin4

/-- ★★★ **端到端 a.e. 一致性（CASTER 侧，速率混合模型）**：
`hf_int` / `hf_pos` / `hpos` / `hint` **全部消掉**，剩下的唯一假设是 `hconv`
（a.e. 收敛 —— W13d 的块级 SLLN 供给）与「经验得分在 `emp n ω` 上最大化」。

对比 `Phylo.Stat.MSCKingmanMeasure.jc69_caster_statisticallyConsistent_kingman_measure_derived`
（JC69 端点，仍带 `hint` 与 `hconv`）：本定理把 `hint` 也消掉了（§5）。 -/
theorem abar_caster_statisticallyConsistent_kingman_ae {Ω : Type*} [MeasurableSpace Ω]
    (M : SiteRateModel) (leaf : Fin 4 → ℝ) (a b : ℝ≥0) (hab : 0 < (a : ℝ) + (b : ℝ))
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (emp : ℕ → Ω → TopoWeight (Fin 4))
    (hconv : ∀ᵐ ω ∂μ, ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N,
      TopoClose (emp n ω) (abarTopoIdeal_kingman M leaf a b hab).W ε)
    {E : ℕ → Ω → TopoChoice (Fin 4)}
    (hE : ∀ᵐ ω ∂μ, ∀ (n : ℕ) (q : TopoChoice (Fin 4)),
      topoScore (emp n ω) q ≤ topoScore (emp n ω) (E n ω)) :
    ∀ᵐ ω ∂μ, ∃ N : ℕ, ∀ n ≥ N,
      IsTrueT (fun _ _ => Topo.ab_cd) (E n ω) :=
  topo_statisticallyConsistent_ae (abarTopoIdeal_kingman M leaf a b hab) μ emp hconv
    exists_not_true_topoChoice_fin4 hE

end Phylo.Stat.CASTERRateAE

end
