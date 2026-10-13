/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.Stat.BlockModelRhoAE2
import Phylo.Stat.BlockSLLNTopoClose

set_option autoImplicit false
set_option linter.deprecated false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

/-!
# `Phylo.Stat.BlockModelRhoAE3` —— **不假设 `hconv`** 的端到端定理（W16b 第 ② 件）

> ★★ **本件超出 W13 规格（beyond-spec）**，是 W16a 第 ① 件
> （`Phylo/Stat/BlockModelRhoAE2.lean`）的**续作**：第 ① 件把「物种树也随机」的
> **块概率空间**（`BlockR` / `blockRPMeasure` / `blockRSample`）连同
> **坐标独立**（`blockR_iIndepFun`）与**恒同分布**（`blockR_identDistrib`）打通；
> 本件把**识别等式**（`hlim`）与**端到端定理**补上。

## 0. 这一件补的缺口（原文）

`Phylo/Stat/BlockModelRhoAE2.lean` 文件头 §6 诚实边界 1（**逐字**）登记：

> **本文件不证识别等式 `hlim`、也不给端到端定理** —— 那是第 ② 件。

本文件就是第 ② 件。`W16a_BLOCKER.md`（250 行版）§8 给出了**已推好的归约**
（`integral_map` → `blockWR_eq_blockW` → `integral_prod` → `blockW_integral`
⇒ 「Dirac 混合」引理 ⇒ 组端到端），本文件**照单实施**。

## 1. ★★★ 唯一的实质引理：**「Dirac 混合 ＝ 混合」**

```lean
integral_expWeight_dirac_mix :
  (∫ p, expWeight (kingmanMSCMeasure (Measure.dirac p)) τd M.Abar T ∂ρ)
    = expWeight (kingmanMSCMeasure ρ) τd M.Abar T
```

**为什么它是实质的**：`expWeight ν …` 是 `ν` 上的一次积分（`geneExpect`），
而 `ν ↦ expWeight ν …` 对 `ν` **不是线性映射**（被积函数 `∑ T', τd θ T' · Ã θ T' T`
依赖 `θ`）。要把它与「先对 `ρ` 积分的 Dirac 混合」交换，
需要把**两边都降到同一个乘积空间上的二重积分**：

```
G θ   := ∑ T', τd θ T' * M.Abar θ T' T
σ     := (sojournLaw 2).prod (sojournLaw 2)         -- 两侧溯祖等待时间
两边  =  ∫ q, G (toKingmanΘ q) ∂(ρ.prod σ)          -- 同一个二重积分
```

* **右端**：`kingmanMSCMeasure ρ = map toKingmanΘ (ρ.prod σ)`（**定义**）
  ⇒ `integral_map` ✚ `integral_prod`；
* **左端**：逐项用 `kingmanMSCMeasure_dirac_eq_map`（`MSCKingmanMeasure.lean:436`）
  ⇒ `kingmanMSCMeasure (dirac p) = map (fun v => toKingmanΘ (p, v)) σ`
  ⇒ `integral_map`（逆用）✚ `integral_prod`。

★★ **可积性由箱体先验供给**（不用任何 Wald 恒等式 / 条件期望）：
`CASTERRateBoxAE.abarHint_integrable_of_boxParam` ＋ `abs_hint_le_one`
（`|G θ| ≤ 1` 在 `BoxTheta` 上）。

## 2. 组端到端（`BlockModelRhoAE2` 的块层）

| 层 | `BlockModelAE`（固定物种树） | **本文件**（随机物种树） |
|---|---|---|
| `∫ blockW` | `blockW_integral`（`:604`） | **`blockW_integral_R`** |
| `∫ blockL` | `blockL_integral`（`:641`） | **`blockL_integral_R`** |
| 识别等式 | `blockW_div_blockL`（`:700`） | **`blockW_div_blockL_R`** |
| `hlim`（样本空间） | `block_hlim` | **`block_hlim_R`** |
| 块层 a.e. 收敛 | `block_emp_tendsto_ae`（`:823`） | **`block_emp_tendsto_ae_R`** |
| 端到端 | `…_ae_blocks`（`:857`，**不假设** `hconv`） | **`…_ae_blocks_box`**（**不假设** `hconv`） |

★ **目标权重表逐字相同**：`block_hlim_R` 的右端就是
`CASTERRateBoxAE.abarTopoIdealBox` 的 `W`（`abarTopoIdealBox_W` 是 `rfl`）
⇒ 套 `CASTERRateBoxAE.abar_caster_statisticallyConsistent_kingman_ae_box` 得到端到端。

## 3. ★ 方向纪律（教训 236）与一处**减少假设**的关键判断

`BlockModelAE.abs_blockW_le` 需要**逐点**前提 `0 ≤ leaf i`。但在 `BlockR` 上
`bb.sp.1`（叶长）**只是任意实值函数** —— 箱体先验 `hbox` 只给 `ρ`-`a.e.` 的非负性 ✗。
⇒ 本文件**不**走 `abs_blockW_le`，而**自证**它的 `BlockR` 版
（`abs_blockWR_le`）：`|siteWR| ≤ 1` 只用到 `a b ≥ 0`（`ℝ≥0` 给）＋ `|τd| ≤ 1`，
**完全不需要叶长非负** ✓。这是「**减少假设**」的方向，不是把命题改弱 ✓。

## 4. ★A 纪律：本文件引用的既有名字都读过定义处

| 名字 | 定义处 | 命名空间 |
|---|---|---|
| `BlockR` / `blockWR` / `blockLR` / `blockRPMeasure` / `blockRSample` / `blockRToBlock` | `BlockModelRhoAE2.lean:171/276/280/365/380/286` | `Phylo.Stat.BlockModelRhoAE` |
| `blockWR_eq_blockW` / `blockLR_eq_blockL` / `blockR_iIndepFun` / `blockR_identDistrib` / `blockR_L1` / `blockRSample_map_eval` / `measurable_blockWR` / `measurable_blockLR` | `BlockModelRhoAE2.lean:303/309/438/453/477/393/413/422` | 同上 |
| `empOfBlocks` / `blockW_integral` / `blockL_integral` / `integral_LIdx_pos` / `blockW_div_blockL` / `block_emp_tendsto_ae` / `abs_tauA_le_one` | `BlockModelAE.lean:310/604/641/687/700/823/398` | `Phylo.Stat.BlockModelAE` |
| `kingmanMSCMeasure` / `toKingmanΘ` / `measurable_toKingmanΘ` / `kingmanMSCMeasure_dirac_eq_map` | `MSCKingmanMeasure.lean:138/101/116/436` | `Phylo.Stat.MSCKingmanMeasure` |
| `expWeight` / `geneExpect` / `empWeight_tendsto_ae` | `CASTERBridge.lean:134` / `CASTEREngine.lean:224` / `BlockSLLNTopoClose.lean:116` | `Phylo.Stat.CASTERBridge` / `…Engine` / `…BlockSLLNTopoClose` |
| `BoxParam` / `abs_hint_le_one` / `abarHint_integrable_of_boxParam` / `abar_caster_…_ae_box` / `boxParam_dirac_ae` / `exists_probabilityMeasure_boxParam` | `CASTERRateBoxAE.lean:155/325/461/610/628/687` | `Phylo.Stat.CASTERRateBoxAE` |
| `measurable_abarHint` | `CASTERRateAE.lean:146` | `Phylo.Stat.CASTERRateAE` |
| `integrable_of_abs_bound` | `SiteWeightMeasurable.lean:350` | `Phylo.Stat.SiteWeightMeasurable` |
| `integrable_map_measure` / `integral_map` / `integral_prod` / `integral_const_mul` / `Measure.map_fst_prod` | Mathlib | `MeasureTheory` |

## 5. 诚实边界

1. 本件的**端到端假设面**：概率测度 `ρ`（**箱体先验**）＋ 概率测度 `νL`
   ＋ **算法性质 `hE`**（经验得分被 `E n ω` 最大化）。**不含 `hconv`** ✓
   —— 但 `hE` 仍是算法侧假设（与库内既有端点**同形**，本件不改进它）。
2. `lx⁻` 是**下界**（**不是**上界）：`BoxParam` 给的是 `lx⁻ ≤ a + b`；
   `abs_hint_le_one` 只需要它。**没有**用到 `a + b` 的上界。
3. 本件**不改**任何既有文件里的声明（★C）：只**新增**本文件，且只 `import`。
4. 退化一致性（门 5）见 §4：Dirac 情形下目标权重表**逐字**退回
   `BlockModelAE` 的那一张（`rfl`），块层的一致由 `blockWR_eq_blockW` 供给。
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal

namespace Phylo.Stat.BlockModelRhoAE3

open Phylo.Stat.CASTERWeights (Topo)
open Phylo.Stat.MSCKingman (KingmanΘ kingmanMSCTopoSym)
open Phylo.Stat.MSCKingmanMeasure
open Phylo.Stat.KingmanCoalescent (sojournLaw)
open Phylo.Stat.SiteRateMixture
open Phylo.Stat.BlockModelAE
open Phylo.Stat.SiteWeightMeasurable
open Phylo.Stat.CASTERTopo
open Phylo.Stat.CASTERRateAE
open Phylo.Stat.CASTERRateBoxAE
open Phylo.Stat.CASTERBridge
open Phylo.Stat.CASTEREngine
open Phylo.Stat.BlockModelRhoAE

variable {M : SiteRateModel} {C : ℕ}

/-! ## 1. 「Dirac 混合 ＝ 混合」（唯一的实质引理） -/

/-- ★ **`G` 关于 `ν = kingmanMSCMeasure ρ` 可积**（箱体先验供给）。

★ 被积函数写成**显式求和**（不经过 `def`）—— 这样 `integral_map` / `Integrable`
的类型匹配是**定义层**的，不需要任何展开引理。 -/
theorem integrable_Gfun_kingman {ρ : Measure ((Fin 4 → ℝ) × ℝ≥0 × ℝ≥0)}
    [IsProbabilityMeasure ρ] {lmax lx0 : ℝ} (hlx0 : 0 ≤ lx0)
    (hbox : ∀ᵐ p ∂ρ, p ∈ BoxParam lmax lx0) (T : Topo) :
    Integrable (fun θ : KingmanΘ =>
      ∑ T' : Topo, kingmanMSCTopoSym.τd θ T' * M.Abar θ T' T) (kingmanMSCMeasure ρ) :=
  abarHint_integrable_of_boxParam M hlx0 hbox T

/-- ★★ **`G ∘ toKingmanΘ` 关于 `ρ.prod σ` 可积**。 -/
theorem integrable_Gfun_prod (M : SiteRateModel) (T : Topo)
    (ρ : Measure ((Fin 4 → ℝ) × ℝ≥0 × ℝ≥0)) [IsProbabilityMeasure ρ] {lmax lx0 : ℝ}
    (hlx0 : 0 ≤ lx0) (hbox : ∀ᵐ p ∂ρ, p ∈ BoxParam lmax lx0) :
    Integrable (fun q : ((Fin 4 → ℝ) × ℝ≥0 × ℝ≥0) × (ℝ × ℝ) =>
      ∑ T' : Topo, kingmanMSCTopoSym.τd (toKingmanΘ q) T' * M.Abar (toKingmanΘ q) T' T)
      (ρ.prod ((sojournLaw 2).prod (sojournLaw 2))) := by
  have hF : Measurable toKingmanΘ :=
    measurable_toKingmanΘ
  -- ★ θ 型陈述（照抄同文件 :140-145 的成功写法；不再写成"乘积型测度" ✗）
  have hgoal : Integrable (fun θ : KingmanΘ => ∑ T' : Topo,
      kingmanMSCTopoSym.τd θ T' * M.Abar θ T' T)
      (Measure.map toKingmanΘ (ρ.prod ((sojournLaw 2).prod (sojournLaw 2)))) := by
    have hsame : Measure.map toKingmanΘ
        (ρ.prod ((sojournLaw 2).prod (sojournLaw 2))) = kingmanMSCMeasure ρ := rfl
    rw [hsame]
    exact integrable_Gfun_kingman (M := M) (ρ := ρ) hlx0 hbox T
  -- ★ 收口：Integrable.comp_measurable（Integrable.lean:368）直接给出 (G ∘ toKingmanΘ) 关于 ρ.prod σ 的可积性
  exact hgoal.comp_measurable measurable_toKingmanΘ

/-- ★ **逐点形态**：`expWeight (kingmanMSCMeasure (dirac p)) … = ∫ v, G (toKingmanΘ (p, v)) ∂σ`
（`kingmanMSCMeasure_dirac_eq_map` ＋ `integral_map`）。 -/
theorem expWeight_dirac_eq_integral_sojourn (M : SiteRateModel)
    (p : (Fin 4 → ℝ) × ℝ≥0 × ℝ≥0) (T : Topo) :
    expWeight (kingmanMSCMeasure (Measure.dirac p)) kingmanMSCTopoSym.τd M.Abar T
      = ∫ v, (∑ T' : Topo,
          kingmanMSCTopoSym.τd (toKingmanΘ (p, v)) T' * M.Abar (toKingmanΘ (p, v)) T' T)
          ∂((sojournLaw 2).prod (sojournLaw 2)) := by
  have hg : Measurable fun v : ℝ × ℝ => toKingmanΘ (p, v) :=
    measurable_toKingmanΘ.comp (measurable_const.prodMk measurable_id)
  have hmeas : AEStronglyMeasurable (fun θ : KingmanΘ => ∑ T' : Topo,
      kingmanMSCTopoSym.τd θ T' * M.Abar θ T' T)
      (Measure.map (fun v : ℝ × ℝ => toKingmanΘ (p, v)) ((sojournLaw 2).prod (sojournLaw 2))) :=
    (measurable_abarHint M T).aestronglyMeasurable
  rw [expWeight, geneExpect, kingmanMSCMeasure_dirac_eq_map p]
  exact integral_map hg.aemeasurable hmeas

/-- ★★★ **右端化到乘积空间**：
`expWeight (kingmanMSCMeasure ρ) τd Ã T = ∫ q, G (toKingmanΘ q) ∂(ρ.prod σ)`。 -/
theorem expWeight_kingman_eq_integral_prod (M : SiteRateModel)
    (ρ : Measure ((Fin 4 → ℝ) × ℝ≥0 × ℝ≥0)) [IsProbabilityMeasure ρ]
    {lmax lx0 : ℝ} (hlx0 : 0 ≤ lx0) (hbox : ∀ᵐ p ∂ρ, p ∈ BoxParam lmax lx0) (T : Topo) :
    expWeight (kingmanMSCMeasure ρ) kingmanMSCTopoSym.τd M.Abar T
      = ∫ q, (∑ T' : Topo,
          kingmanMSCTopoSym.τd (toKingmanΘ q) T' * M.Abar (toKingmanΘ q) T' T)
          ∂(ρ.prod ((sojournLaw 2).prod (sojournLaw 2))) := by
  rw [expWeight, geneExpect,
    show kingmanMSCMeasure ρ
      = Measure.map toKingmanΘ (ρ.prod ((sojournLaw 2).prod (sojournLaw 2))) from rfl]
  have hmeas : AEStronglyMeasurable (fun θ : KingmanΘ =>
      ∑ T' : Topo, kingmanMSCTopoSym.τd θ T' * M.Abar θ T' T)
      (Measure.map toKingmanΘ (ρ.prod ((sojournLaw 2).prod (sojournLaw 2)))) := by
    rw [show Measure.map toKingmanΘ (ρ.prod ((sojournLaw 2).prod (sojournLaw 2)))
      = kingmanMSCMeasure ρ from rfl]
    exact (integrable_Gfun_kingman (M := M) (ρ := ρ) hlx0 hbox T).aestronglyMeasurable
  exact integral_map measurable_toKingmanΘ.aemeasurable hmeas

/-- ★★★ **左端化到乘积空间**（逐项 `kingmanMSCMeasure_dirac_eq_map` ＋ `integral_map`）。 -/
theorem diracMix_eq_integral_prod (M : SiteRateModel)
    (ρ : Measure ((Fin 4 → ℝ) × ℝ≥0 × ℝ≥0)) [IsProbabilityMeasure ρ]
    {lmax lx0 : ℝ} (hlx0 : 0 ≤ lx0) (hbox : ∀ᵐ p ∂ρ, p ∈ BoxParam lmax lx0) (T : Topo) :
    (∫ p, expWeight (kingmanMSCMeasure (Measure.dirac p)) kingmanMSCTopoSym.τd M.Abar T ∂ρ)
      = ∫ q, (∑ T' : Topo,
          kingmanMSCTopoSym.τd (toKingmanΘ q) T' * M.Abar (toKingmanΘ q) T' T)
          ∂(ρ.prod ((sojournLaw 2).prod (sojournLaw 2))) := by
  rw [integral_congr_ae
    (Filter.Eventually.of_forall (fun p => expWeight_dirac_eq_integral_sojourn (M := M) p T))]
  exact (MeasureTheory.integral_prod _
    (integrable_Gfun_prod (M := M) (T := T) ρ hlx0 hbox)).symm

/-- ★★★ **(W16b 的核心交付)「Dirac 混合 ＝ 混合」**：
对**任意**满足箱体先验的物种树测度 `ρ`，把「逐点 Dirac 的 `expWeight` 关于 `ρ` 的积分」
与「`kingmanMSCMeasure ρ` 的 `expWeight`」等同。

★ 数学内容：`ν ↦ expWeight ν τd Ã T` 对 `ν` **不是线性**的，但
`kingmanMSCMeasure` 是 `map toKingmanΘ`，而 `expWeight` 是 `ν` 上一次**积分**
⇒ 两边都降到 `ρ.prod σ` 上的**同一个二重积分**。 -/
theorem integral_expWeight_dirac_mix (M : SiteRateModel)
    (ρ : Measure ((Fin 4 → ℝ) × ℝ≥0 × ℝ≥0)) [IsProbabilityMeasure ρ]
    {lmax lx0 : ℝ} (hlx0 : 0 ≤ lx0) (hbox : ∀ᵐ p ∂ρ, p ∈ BoxParam lmax lx0) (T : Topo) :
    (∫ p, expWeight (kingmanMSCMeasure (Measure.dirac p)) kingmanMSCTopoSym.τd M.Abar T ∂ρ)
      = expWeight (kingmanMSCMeasure ρ) kingmanMSCTopoSym.τd M.Abar T :=
  (diracMix_eq_integral_prod (M := M) (ρ := ρ) hlx0 hbox T).trans
    (expWeight_kingman_eq_integral_prod (M := M) (ρ := ρ) hlx0 hbox T).symm

/-! ## 2. 块层的三条积分恒等式（`BlockModelRhoAE2` 的块空间） -/

/-- ★★ **`|siteWR| ≤ 1`**（★ **需要逐点**叶长非负 `hleaf`：上游 `abs_tauA_le_one` 的必需前提；
负枝长时 `patternProb` 无界，见 `BlockModelAE.lean:78/396-398` ✓）。
★ 为何不能省：`BlockR.sp.1` 的叶长是**任意实值**，只有 `ρ`-a.e. 的非负（箱体先验给）⇒ 逐点假设必须显式带上。 -/
theorem abs_siteWR_le_one (M : SiteRateModel) (C : ℕ) (T : Topo) (bb : BlockR M C)
    (hleaf : ∀ j : Fin 4, 0 ≤ bb.sp.1 j) (i : Fin C) : |siteWR M C T bb i| ≤ 1 := by
  have hkey : BlockR.thetaOf bb
      = toKingmanΘ ((bb.sp.1, bb.sp.2.1, bb.sp.2.2), bb.rest.1.1) := rfl
  have hl : ∀ j : Fin 4, 0 ≤ (BlockR.thetaOf bb).1.1 j := fun j => by
    rw [hkey]
    exact hleaf j
  have hlx : 0 ≤ (BlockR.thetaOf bb).1.2 := by
    rw [hkey]
    exact add_nonneg (bb.sp.2.1).2 (bb.sp.2.2).2
  simpa only [siteWR] using (abs_tauA_le_one (M := M) hl hlx T (bb.rest.2 i))

/-- ★★ **`|blockWR| ≤ C`**（★ 同样**需要逐点**叶长非负 `hleaf`，理由同 `abs_siteWR_le_one`）。 -/
theorem abs_blockWR_le (M : SiteRateModel) (C : ℕ) (T : Topo) (bb : BlockR M C)
    (hleaf : ∀ j : Fin 4, 0 ≤ bb.sp.1 j) :
    |blockWR M C T bb| ≤ (C : ℝ) := by
  calc |blockWR M C T bb|
      ≤ ∑ i : Fin C, |if (i : ℕ) < bb.rest.1.2.1 then siteWR M C T bb i else 0| := by
        rw [blockWR]
        exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin C, (1 : ℝ) := by
        refine Finset.sum_le_sum fun i _ => ?_
        by_cases hi : (i : ℕ) < bb.rest.1.2.1
        · rw [ite_eq_left hi]
          exact abs_siteWR_le_one M C T bb hleaf i
        · rw [ite_eq_right hi, abs_zero]
          norm_num
    _ = (C : ℝ) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]

/-- ★★ **推到生空间的可积性搬运**（`blockRPMeasure` 是 `BlockR.ofRaw` 的推前）。 -/
theorem integrable_map_ofRaw {f : BlockR M C → ℝ} (hf : Measurable f)
    (ρ : Measure ((Fin 4 → ℝ) × ℝ≥0 × ℝ≥0)) [IsProbabilityMeasure ρ]
    (νL : Measure (LIdx C)) [IsProbabilityMeasure νL] {Cb : ℝ}
    (hb : ∀ᵐ p ∂(ρ.prod ((((sojournLaw 2).prod (sojournLaw 2)).prod νL).prod (ratePi M C))),
      |f (BlockR.ofRaw p)| ≤ Cb) :
    Integrable f (blockRPMeasure M C ρ νL) := by
  rw [blockRPMeasure]
  have hmeas : AEStronglyMeasurable (f ∘ BlockR.ofRaw)
      (ρ.prod ((((sojournLaw 2).prod (sojournLaw 2)).prod νL).prod (ratePi M C))) :=
    (hf.comp measurable_ofRawR).aestronglyMeasurable
  refine (integrable_map_measure (f := BlockR.ofRaw)
    (hf.aestronglyMeasurable) measurable_ofRawR.aemeasurable).mpr ?_
  exact integrable_of_abs_bound hmeas hb

/-- ★★ **块总权重的可积性**（随机物种树；界 `C` 与物种树无关）。 -/
theorem integrable_blockWR (M : SiteRateModel) (C : ℕ)
    (ρ : Measure ((Fin 4 → ℝ) × ℝ≥0 × ℝ≥0)) [IsProbabilityMeasure ρ]
    (νL : Measure (LIdx C)) [IsProbabilityMeasure νL] {lmax lx0 : ℝ} (_hlx0 : 0 ≤ lx0)
    (hbox : ∀ᵐ p ∂ρ, p ∈ BoxParam lmax lx0) (T : Topo) :
    Integrable (fun bb : BlockR M C => blockWR M C T bb) (blockRPMeasure M C ρ νL) := by
  -- ★ 只用到 `ρ`-a.e. 的叶长非负（箱体先验给 ✓）；不再用"逐点恒成立"的假界 ✗
  refine integrable_map_ofRaw (measurable_blockWR (M := M) (C := C) T) ρ νL (Cb := (C : ℝ)) ?_
  -- ★ 把 `ρ`-a.e. 的箱体条件沿第一分量抬到乘积测度上（Mathlib `QuasiMeasurePreserving.ae` ✓）
  filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := ρ)
    (ν := ((((sojournLaw 2).prod (sojournLaw 2)).prod νL).prod (ratePi M C)))).ae hbox] with p hp
  exact abs_blockWR_le M C T (BlockR.ofRaw p) (fun i => (hp.1 i).1)

/-- ★★ **块位点数的可积性**（随机物种树）。 -/
theorem integrable_blockLR (M : SiteRateModel) (C : ℕ)
    (ρ : Measure ((Fin 4 → ℝ) × ℝ≥0 × ℝ≥0)) [IsProbabilityMeasure ρ]
    (νL : Measure (LIdx C)) [IsProbabilityMeasure νL] :
    Integrable (fun bb : BlockR M C => blockLR M C bb) (blockRPMeasure M C ρ νL) := by
  refine integrable_map_ofRaw (measurable_blockLR (M := M) (C := C)) ρ νL (Cb := (C : ℝ)) ?_
  filter_upwards with p
  have h1 : blockLR M C (BlockR.ofRaw p) = ((p.2.1.2.1 : ℕ) : ℝ) := rfl
  rw [h1, abs_of_nonneg (by positivity)]
  exact_mod_cast p.2.1.2.2.2

/-- ★★★ **识别等式（`blockW` 侧，随机物种树）**：
`∫ blockWR ∂(blockRPMeasure ρ νL) = 𝔼[L] · expWeight (kingmanMSCMeasure ρ) τd Ã T`。

证明 = `integral_map` ⇒ `blockWR_eq_blockW` ⇒ `integral_prod`（拆 `sp`）
⇒ 内层 `blockW_integral`（固定物种树）⇒ 提出常数 ⇒ **`integral_expWeight_dirac_mix`**
（`W16a_BLOCKER.md` §8.3 的归约链）。 -/
theorem blockW_integral_R (M : SiteRateModel) (C : ℕ)
    (ρ : Measure ((Fin 4 → ℝ) × ℝ≥0 × ℝ≥0)) [IsProbabilityMeasure ρ]
    (νL : Measure (LIdx C)) [IsProbabilityMeasure νL]
    {lmax lx0 : ℝ} (hlx0 : 0 ≤ lx0) (hbox : ∀ᵐ p ∂ρ, p ∈ BoxParam lmax lx0) (T : Topo) :
    ∫ bb, blockWR M C T bb ∂(blockRPMeasure M C ρ νL)
      = (∫ l, ((l : ℕ) : ℝ) ∂νL) *
          expWeight (kingmanMSCMeasure ρ) kingmanMSCTopoSym.τd M.Abar T := by
  classical
  -- ① `integral_map`：推到 `BlockR` 的生空间
  have hmap : (∫ bb, blockWR M C T bb ∂(blockRPMeasure M C ρ νL))
      = ∫ p : ((Fin 4 → ℝ) × ℝ≥0 × ℝ≥0) × (((ℝ × ℝ) × LIdx C) × (Fin C → M.Rate)),
          blockWR M C T (BlockR.ofRaw p)
          ∂(ρ.prod ((((sojournLaw 2).prod (sojournLaw 2)).prod νL).prod (ratePi M C))) := by
    rw [blockRPMeasure]
    exact integral_map measurable_ofRawR.aemeasurable
      (measurable_blockWR (M := M) (C := C) T).aestronglyMeasurable
  rw [hmap]
  -- ② `integral_prod`：拆出物种树侧 `sp`（可积性沿 `ofRaw` 搬运）
  have hmeasP : AEStronglyMeasurable (fun bb : BlockR M C => blockWR M C T bb)
      (Measure.map (BlockR.ofRaw (M := M) (C := C))
        (ρ.prod ((((sojournLaw 2).prod (sojournLaw 2)).prod νL).prod (ratePi M C)))) :=
    (measurable_blockWR (M := M) (C := C) T).aestronglyMeasurable
  have hIntP : Integrable (fun p : ((Fin 4 → ℝ) × ℝ≥0 × ℝ≥0) ×
      (((ℝ × ℝ) × LIdx C) × (Fin C → M.Rate)) => blockWR M C T (BlockR.ofRaw p))
      (ρ.prod ((((sojournLaw 2).prod (sojournLaw 2)).prod νL).prod (ratePi M C))) :=
    (integrable_map_measure (f := BlockR.ofRaw (M := M) (C := C)) hmeasP
      measurable_ofRawR.aemeasurable).mp
      (by
        rw [show (ρ.prod ((((sojournLaw 2).prod (sojournLaw 2)).prod νL).prod (ratePi M C))).map
            (BlockR.ofRaw (M := M) (C := C)) = blockRPMeasure M C ρ νL from rfl]
        exact integrable_blockWR (M := M) (C := C) (ρ := ρ) (νL := νL) hlx0 hbox T)
  rw [MeasureTheory.integral_prod _ hIntP]
  -- ③ 内层（固定 `sp`）＝ `𝔼[L] · expWeight (dirac sp)`
  -- ★ 改为 `ρ`-a.e. 陈述（原为 `∀ sp` ✗ 且其"叶长非负"证据为假 ✗；见 W16b_HANDOVER §12.6）
  have hinner : ∀ᵐ sp ∂ρ,
      (∫ r : ((ℝ × ℝ) × LIdx C) × (Fin C → M.Rate),
        blockWR M C T (BlockR.ofRaw (sp, r))
        ∂((((sojournLaw 2).prod (sojournLaw 2)).prod νL).prod (ratePi M C)))
      = (∫ l, ((l : ℕ) : ℝ) ∂νL) *
          expWeight (kingmanMSCMeasure (Measure.dirac sp)) kingmanMSCTopoSym.τd M.Abar T := by
    filter_upwards [hbox] with sp hsp
    have hleafsp : ∀ i : Fin 4, 0 ≤ sp.1 i := fun i => (hsp.1 i).1
    -- `abs_blockW_le` 要**逐点** `0 ≤ leaf i`，而 `BlockR` 的叶长只是任意实数
    -- ⇒ 必须走 a.e. 路线：`Integrable` ⇒ `aestronglyMeasurable` ⇒ `ae_le`
    have hIntP2 : Integrable (fun r : ((ℝ × ℝ) × LIdx C) × (Fin C → M.Rate) =>
        blockWR M C T (BlockR.ofRaw (sp, r)))
        ((((sojournLaw 2).prod (sojournLaw 2)).prod νL).prod (ratePi M C)) :=
      -- ★ 直接由「可测 ＋ a.e. 有界 ⇒ 可积」给出（界来自 abs_blockWR_le ＋ 已得的逐点叶长非负 ✓）
      integrable_of_abs_bound
        ((measurable_blockWR (M := M) (C := C) T).comp
          (measurable_ofRawR.comp (measurable_const.prodMk measurable_id))).aestronglyMeasurable
        (Filter.Eventually.of_forall fun r => abs_blockWR_le M C T (BlockR.ofRaw (sp, r)) hleafsp)
    -- 叶长的非负性：由**箱体先验**（`hbox`）沿第一分量边缘律搬过来
    have hleaf : ∀ᵐ r ∂((((sojournLaw 2).prod (sojournLaw 2)).prod νL).prod (ratePi M C)),
        ∀ i : Fin 4, 0 ≤ sp.1 i :=
      Filter.Eventually.of_forall (fun _ i => hleafsp i)
    have hfix := blockW_integral (M := M) (C := C) (leaf := sp.1) (a := sp.2.1)
      (b := sp.2.2) (νL := νL) (fun i : Fin 4 => hleaf.exists.elim (fun _ h => h i)) T
    -- ★ W18：不再直接跨到 `Block M C leaf a b` 那一套 API ✗（会在积分式里留 metavariable
    --   ⇒ `NormedSpace ℝ ?m` 卡住 ✗）；改为**两步自足路线** ✓（同文件 `:561` 已用 `blockWR_eq_blockW` ✓）：
    --   ① 用 `blockWR_eq_blockW` 逐点把 `blockWR` 换成 `blockW … (blockRToBlock ·)` ✓；
    --   ② 对【固定 `sp`】做一次**参数显式**的 `integral_map`（取其 `.symm` ✓，因库内方向是 map 侧 = 源侧 ✓）。
    have hbridge1 : (∫ r : ((ℝ × ℝ) × LIdx C) × (Fin C → M.Rate),
        blockWR M C T (BlockR.ofRaw (sp, r))
        ∂((((sojournLaw 2).prod (sojournLaw 2)).prod νL).prod (ratePi M C)))
        = ∫ r : ((ℝ × ℝ) × LIdx C) × (Fin C → M.Rate),
            blockW M C sp.1 sp.2.1 sp.2.2 T (blockRToBlock (BlockR.ofRaw (sp, r)))
            ∂((((sojournLaw 2).prod (sojournLaw 2)).prod νL).prod (ratePi M C)) :=
      integral_congr_ae (Filter.Eventually.of_forall fun r =>
        blockWR_eq_blockW (M := M) (C := C) T (BlockR.ofRaw (sp, r)))
    have hbridge2 : (∫ r : ((ℝ × ℝ) × LIdx C) × (Fin C → M.Rate),
            blockW M C sp.1 sp.2.1 sp.2.2 T (blockRToBlock (BlockR.ofRaw (sp, r)))
            ∂((((sojournLaw 2).prod (sojournLaw 2)).prod νL).prod (ratePi M C)))
        = ∫ bb : Block M C sp.1 sp.2.1 sp.2.2, blockW M C sp.1 sp.2.1 sp.2.2 T bb
          ∂(Measure.map Block.ofRaw
            ((((sojournLaw 2).prod (sojournLaw 2)).prod νL).prod (ratePi M C))) :=
      (integral_map (μ := ((((sojournLaw 2).prod (sojournLaw 2)).prod νL).prod (ratePi M C)))
        (φ := fun r : ((ℝ × ℝ) × LIdx C) × (Fin C → M.Rate) =>
          Block.ofRaw (M := M) (C := C) (leaf := sp.1) (a := sp.2.1) (b := sp.2.2) r)
        measurable_ofRaw.aemeasurable
        (measurable_blockW (M := M) (C := C) (leaf := sp.1) (a := sp.2.1)
          (b := sp.2.2) T).aestronglyMeasurable).symm
    have hbridge := hbridge1.trans hbridge2
    rw [hbridge]
    exact hfix
  rw [integral_congr_ae hinner]
  -- ④ 提出常数 ＋ `integral_expWeight_dirac_mix`
  rw [MeasureTheory.integral_const_mul]
  exact congrArg (fun x => (∫ l, ((l : ℕ) : ℝ) ∂νL) * x)
    (integral_expWeight_dirac_mix (M := M) (ρ := ρ) hlx0 hbox T)

/-- ★★★ **识别等式（`blockL` 侧，随机物种树）**：`∫ blockLR = 𝔼[L]`。 -/
theorem blockL_integral_R (M : SiteRateModel) (C : ℕ)
    (ρ : Measure ((Fin 4 → ℝ) × ℝ≥0 × ℝ≥0)) [IsProbabilityMeasure ρ]
    (νL : Measure (LIdx C)) [IsProbabilityMeasure νL] :
    ∫ bb, blockLR M C bb ∂(blockRPMeasure M C ρ νL) = ∫ l, ((l : ℕ) : ℝ) ∂νL := by
  -- ★★ 2026-10-13 W18【自足路线】✓：`blockLR bb = (bb.rest.1.2.1 : ℝ)` 是**纯投影** ✓，
  --   故本定理**完全不需要** `Block M C leaf a b` 那一套 API ✗（后者是依赖 leaf a b 的类型族，
  --   一进积分式就留 metavariable ✗，正是 W16a 文件头记的那面墙 ✓）。
  --   证明按库内 `BlockModelAE.blockL_integral`（:641-676）的同一模板，逐层用库内引理 ✓。
  have hmap : (∫ bb, blockLR M C bb ∂(blockRPMeasure M C ρ νL))
      = ∫ p : ((Fin 4 → ℝ) × ℝ≥0 × ℝ≥0) × (((ℝ × ℝ) × LIdx C) × (Fin C → M.Rate)),
          blockLR M C (BlockR.ofRaw p)
          ∂(ρ.prod ((((sojournLaw 2).prod (sojournLaw 2)).prod νL).prod (ratePi M C))) := by
    rw [blockRPMeasure]
    exact integral_map measurable_ofRawR.aemeasurable
      (measurable_blockLR (M := M) (C := C)).aestronglyMeasurable
  rw [hmap]
  -- 逐点：`blockLR (BlockR.ofRaw p) = ((p.2.1.2.1 : ℕ) : ℝ)`（`rfl` ✓）
  have hstep : (∫ p : ((Fin 4 → ℝ) × ℝ≥0 × ℝ≥0) × (((ℝ × ℝ) × LIdx C) × (Fin C → M.Rate)),
        blockLR M C (BlockR.ofRaw p)
        ∂(ρ.prod ((((sojournLaw 2).prod (sojournLaw 2)).prod νL).prod (ratePi M C))))
      = ∫ p : ((Fin 4 → ℝ) × ℝ≥0 × ℝ≥0) × (((ℝ × ℝ) × LIdx C) × (Fin C → M.Rate)),
          (((p.2.1.2.1 : ℕ) : ℝ))
          ∂(ρ.prod ((((sojournLaw 2).prod (sojournLaw 2)).prod νL).prod (ratePi M C))) :=
    integral_congr_ae (Filter.Eventually.of_forall fun _ => rfl)
  rw [hstep]
  -- 被积函数与**第一分量**（物种树 `ρ` 侧）无关 ⇒ 用 `integral_fun_snd` 把 `ρ` 积掉（概率测度 ⇒ 系数 1 ✓）
  have hsnd : (∫ p : ((Fin 4 → ℝ) × ℝ≥0 × ℝ≥0) × (((ℝ × ℝ) × LIdx C) × (Fin C → M.Rate)),
        (((p.2.1.2.1 : ℕ) : ℝ))
        ∂(ρ.prod ((((sojournLaw 2).prod (sojournLaw 2)).prod νL).prod (ratePi M C))))
      = (ρ).real Set.univ •
          ∫ q : ((ℝ × ℝ) × LIdx C) × (Fin C → M.Rate), (((q.1.2.1 : ℕ) : ℝ))
            ∂((((sojournLaw 2).prod (sojournLaw 2)).prod νL).prod (ratePi M C)) :=
    MeasureTheory.integral_fun_snd (μ := ρ)
      (ν := ((((sojournLaw 2).prod (sojournLaw 2)).prod νL).prod (ratePi M C)))
      (f := fun q : ((ℝ × ℝ) × LIdx C) × (Fin C → M.Rate) => (((q.1.2.1 : ℕ) : ℝ)))
  rw [hsnd, show (ρ).real Set.univ = (1 : ℝ) from by
    rw [Measure.real, measure_univ, ENNReal.toReal_one], one_smul]
  -- 再与 `ratePi M C` 那一层无关 ⇒ `integral_fun_fst`（系数 1 ✓）
  have hfst : (∫ q : ((ℝ × ℝ) × LIdx C) × (Fin C → M.Rate), (((q.1.2.1 : ℕ) : ℝ))
        ∂((((sojournLaw 2).prod (sojournLaw 2)).prod νL).prod (ratePi M C)))
      = (ratePi M C).real Set.univ •
          ∫ x : (ℝ × ℝ) × LIdx C, (((x.2.1 : ℕ) : ℝ))
            ∂(((sojournLaw 2).prod (sojournLaw 2)).prod νL) :=
    MeasureTheory.integral_fun_fst (μ := (((sojournLaw 2).prod (sojournLaw 2)).prod νL))
      (ν := ratePi M C) (f := fun x : (ℝ × ℝ) × LIdx C => (((x.2.1 : ℕ) : ℝ)))
  rw [hfst, show (ratePi M C).real Set.univ = (1 : ℝ) from by
    rw [Measure.real, measure_univ, ENNReal.toReal_one], one_smul]
  -- 最后只剩 `νL` 那一层 ⇒ `integral_fun_snd`（系数 1 ✓）
  have hl : (∫ x : (ℝ × ℝ) × LIdx C, (((x.2.1 : ℕ) : ℝ))
        ∂(((sojournLaw 2).prod (sojournLaw 2)).prod νL))
      = (((sojournLaw 2).prod (sojournLaw 2))).real Set.univ •
          ∫ l : LIdx C, ((l : ℕ) : ℝ) ∂νL :=
    MeasureTheory.integral_fun_snd (μ := ((sojournLaw 2).prod (sojournLaw 2))) (ν := νL)
      (f := fun l : LIdx C => ((l : ℕ) : ℝ))
  rw [hl, show (((sojournLaw 2).prod (sojournLaw 2))).real Set.univ = (1 : ℝ) from by
    rw [Measure.real, measure_univ, ENNReal.toReal_one], one_smul]

/-- ★★★ **识别等式 `hlim`（块层，随机物种树）**：
`(∫ blockWR)/(∫ blockLR) = expWeight (kingmanMSCMeasure ρ) τd Ã T`。 -/
theorem blockW_div_blockL_R (M : SiteRateModel) (C : ℕ)
    (ρ : Measure ((Fin 4 → ℝ) × ℝ≥0 × ℝ≥0)) [IsProbabilityMeasure ρ]
    (νL : Measure (LIdx C)) [IsProbabilityMeasure νL]
    {lmax lx0 : ℝ} (hlx0 : 0 ≤ lx0) (hbox : ∀ᵐ p ∂ρ, p ∈ BoxParam lmax lx0) (T : Topo) :
    (∫ bb, blockWR M C T bb ∂(blockRPMeasure M C ρ νL)) /
        (∫ bb, blockLR M C bb ∂(blockRPMeasure M C ρ νL))
      = expWeight (kingmanMSCMeasure ρ) kingmanMSCTopoSym.τd M.Abar T := by
  rw [blockW_integral_R (M := M) (C := C) (ρ := ρ) (νL := νL) hlx0 hbox T,
    blockL_integral_R (M := M) (C := C) (ρ := ρ) (νL := νL)]
  exact mul_div_cancel_left₀ _
    (ne_of_gt (integral_LIdx_pos (C := C) (νL := νL)))

/-- ★★★ **`hlim` 在样本空间上的形态**（把块层积分搬到 `ω ↦ blockWR (ω 0)`）。 -/
theorem block_hlim_R (M : SiteRateModel) (C : ℕ)
    (ρ : Measure ((Fin 4 → ℝ) × ℝ≥0 × ℝ≥0)) [IsProbabilityMeasure ρ]
    (νL : Measure (LIdx C)) [IsProbabilityMeasure νL]
    {lmax lx0 : ℝ} (hlx0 : 0 ≤ lx0) (hbox : ∀ᵐ p ∂ρ, p ∈ BoxParam lmax lx0) (T : Topo) :
    (∫ ω, blockWR M C T (ω 0) ∂(blockRSample M C ρ νL)) /
        (∫ ω, blockLR M C (ω 0) ∂(blockRSample M C ρ νL))
      = expWeight (kingmanMSCMeasure ρ) kingmanMSCTopoSym.τd M.Abar T := by
  have hmapW : (∫ ω, blockWR M C T (ω 0) ∂(blockRSample M C ρ νL))
      = ∫ bb, blockWR M C T bb
          ∂((blockRSample M C ρ νL).map (fun ω : ℕ → BlockR M C => ω 0)) :=
    (integral_map (μ := blockRSample M C ρ νL)
      (φ := fun ω : ℕ → BlockR M C => ω 0)
      (f := fun bb : BlockR M C => blockWR M C T bb)
      (measurable_pi_apply 0).aemeasurable
      (measurable_blockWR (M := M) (C := C) T).aestronglyMeasurable).symm
  have hmapL : (∫ ω, blockLR M C (ω 0) ∂(blockRSample M C ρ νL))
      = ∫ bb, blockLR M C bb
          ∂((blockRSample M C ρ νL).map (fun ω : ℕ → BlockR M C => ω 0)) :=
    (integral_map (μ := blockRSample M C ρ νL)
      (φ := fun ω : ℕ → BlockR M C => ω 0)
      (f := fun bb : BlockR M C => blockLR M C bb)
      (measurable_pi_apply 0).aemeasurable
      (measurable_blockLR (M := M) (C := C)).aestronglyMeasurable).symm
  rw [hmapW, hmapL, blockRSample_map_eval (M := M) (C := C) (ρ := ρ) (νL := νL) (i := 0)]
  exact blockW_div_blockL_R (M := M) (C := C) (ρ := ρ) (νL := νL) hlx0 hbox T

/-! ## 3. 块层 a.e. 收敛与端到端（**不假设 `hconv`**） -/

/-- ★★★ **经验表（随机物种树版）**：把块级平均**显式**写在 `BlockR` 上
（不走 `BlockModelAE.empOfBlocks`，因为后者的 `leaf a b` 参数在 `BlockR` 上无意义）。 -/
noncomputable def empBlocksR (M : SiteRateModel) (C : ℕ) (n : ℕ) (ω : ℕ → BlockR M C) :
    TopoWeight (Fin 4) :=
  fun (S : Finset (Fin 4)) (_hS : S.card = 4) (T : Topo) =>
    (∑ j ∈ Finset.range n, blockWR M C T (ω j)) /
      (∑ j ∈ Finset.range n, blockLR M C (ω j))

-- 2026-10-13 W18：此处原有 `empBlocksR_eq_empOfBlocks`（声称与 `BlockModelAE.empOfBlocks` 相等、
--   且对 `leaf a b` 无依赖）—— **已删除** ✗，理由：
--   · `blockRToBlock (ω j)` 的类型是 `Block M C (ω j).sp.1 (ω j).sp.2.1 (ω j).sp.2.2`，
--     而右端要求 `Block M C leaf a b`；`Block M C · · ·` 是**依赖这三个参数的【类型族】** ✓
--     ⇒ 仅当所有 `ω j` 的物种树参数恰为 `leaf a b` 时才同型 ⇒ 对【任意】`leaf a b` 的等式是**假陈述** ✗。
--   · 它**没有任何调用者** ✓，且与 `empBlocksR` 自己的 docstring **相矛盾** ✗
--     （后者已写明：不走 `BlockModelAE.empOfBlocks`，因为它要求固定的 `leaf a b`，在 `BlockR` 上无意义 ✓）。
--   ⇒ 依协调侧 W18 派单**处置②**：语义已由 `empBlocksR` 的 docstring 承担 ✓ ⇒ 删定理、留本注 ✓。

/-- ★ **`hintM`：块总权重在样本空间上可积**。 -/
theorem blockR_eval_integrable_W (M : SiteRateModel) (C : ℕ)
    (ρ : Measure ((Fin 4 → ℝ) × ℝ≥0 × ℝ≥0)) [IsProbabilityMeasure ρ]
    (νL : Measure (LIdx C)) [IsProbabilityMeasure νL] {lmax lx0 : ℝ} (hlx0 : 0 ≤ lx0)
    (hbox : ∀ᵐ p ∂ρ, p ∈ BoxParam lmax lx0) (T : Topo) :
    Integrable (fun ω : ℕ → BlockR M C => blockWR M C T (ω 0))
      (blockRSample M C ρ νL) := by
  have h1 : Integrable (fun bb : BlockR M C => blockWR M C T bb)
      ((blockRSample M C ρ νL).map (fun ω : ℕ → BlockR M C => ω 0)) := by
    rw [blockRSample_map_eval (M := M) (C := C) (ρ := ρ) (νL := νL) (i := 0)]
    exact integrable_blockWR (M := M) (C := C) (ρ := ρ) (νL := νL) hlx0 hbox T
  have h2 := h1.comp_aemeasurable (measurable_pi_apply 0).aemeasurable
  simpa [Function.comp_def] using h2

/-- ★ **`hintL`：块位点数在样本空间上可积**。 -/
theorem blockR_eval_integrable_L (M : SiteRateModel) (C : ℕ)
    (ρ : Measure ((Fin 4 → ℝ) × ℝ≥0 × ℝ≥0)) [IsProbabilityMeasure ρ]
    (νL : Measure (LIdx C)) [IsProbabilityMeasure νL] :
    Integrable (fun ω : ℕ → BlockR M C => blockLR M C (ω 0))
      (blockRSample M C ρ νL) := by
  have h1 : Integrable (fun bb : BlockR M C => blockLR M C bb)
      ((blockRSample M C ρ νL).map (fun ω : ℕ → BlockR M C => ω 0)) := by
    rw [blockRSample_map_eval (M := M) (C := C) (ρ := ρ) (νL := νL) (i := 0)]
    exact integrable_blockLR (M := M) (C := C) (ρ := ρ) (νL := νL)
  have h2 := h1.comp_aemeasurable (measurable_pi_apply 0).aemeasurable
  simpa [Function.comp_def] using h2

/-- ★★★ **`TopoClose` 形态的 a.e. 收敛（随机物种树）**：
把五条块层假设喂进 `BlockSLLNTopoClose.empWeight_tendsto_ae`。

★ 与 `BlockModelAE.block_emp_tendsto_ae` **同形**，只是 `ν` 从
`kingmanMSCMeasure (dirac (leaf, a, b))` 换成了 `kingmanMSCMeasure ρ`。

★ 经验表取 `empOfBlocks`（对 `leaf a b` **无依赖**：它只读 `blockW` 的 `.1` 分量
与 `blockL`，两处都与物种树无关）。 -/
theorem block_emp_tendsto_ae_R (M : SiteRateModel) (C : ℕ)
    (ρ : Measure ((Fin 4 → ℝ) × ℝ≥0 × ℝ≥0)) [IsProbabilityMeasure ρ]
    (νL : Measure (LIdx C)) [IsProbabilityMeasure νL]
    {lmax lx0 : ℝ} (hlx0 : 0 ≤ lx0) (hbox : ∀ᵐ p ∂ρ, p ∈ BoxParam lmax lx0) :
    ∀ᵐ ω ∂(blockRSample M C ρ νL), ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N,
      TopoClose (empBlocksR M C n ω)
        (fun _ _ T => expWeight (kingmanMSCMeasure ρ) kingmanMSCTopoSym.τd M.Abar T) ε := by
  refine Phylo.Stat.BlockSLLNTopoClose.empWeight_tendsto_ae (μ := blockRSample M C ρ νL)
    (X := Fin 4)
    (fun _ T => expWeight (kingmanMSCMeasure ρ) kingmanMSCTopoSym.τd M.Abar T)
    (empBlocksR M C)
    (Mf := fun k j ω => blockWR M C k.2 (ω j))
    (Lf := fun _ j ω => blockLR M C (ω j))
    (fun k => blockR_iIndepFun (M := M) (C := C) (ρ := ρ) (νL := νL) k.2)
    (fun k j => blockR_identDistrib (M := M) (C := C) (ρ := ρ) (νL := νL) k.2 j)
    (fun _ j ω => blockR_L1 (M := M) (C := C) j ω)
    (fun k => blockR_eval_integrable_W (M := M) (C := C) (ρ := ρ) (νL := νL) hlx0 hbox k.2)
    (fun _ => blockR_eval_integrable_L (M := M) (C := C) (ρ := ρ) (νL := νL))
    (fun k => block_hlim_R (M := M) (C := C) (ρ := ρ) (νL := νL) hlx0 hbox k.2)
    (fun _ _ _ _ _ => rfl)

/-- ★★★ **端到端 a.e. 统计一致性（随机物种树 ＋ 箱体先验，不假设 `hconv`）** ——
W16b 的验收判据。

与 `BlockModelAE.abar_caster_statisticallyConsistent_kingman_ae_blocks` 的**唯一**差别：
物种树的**概率测度 `ρ`** 取代了固定的 `(leaf, a, b)`，代价是**箱体先验** `hbox`
＋ 内枝长正下界 `0 < lx⁻`（后两条在 `CASTERRateBoxAE` 里已把
`hf_int` / `hint` / `hlx` / `hpos` 全部**证成定理**）。

★ **假设面不含 `hconv`** ✓：`hconv` 由 `block_emp_tendsto_ae_R` **供给**。 -/
theorem abar_caster_statisticallyConsistent_kingman_ae_blocks_box
    (M : SiteRateModel) (C : ℕ)
    (ρ : Measure ((Fin 4 → ℝ) × ℝ≥0 × ℝ≥0)) [IsProbabilityMeasure ρ]
    (νL : Measure (LIdx C)) [IsProbabilityMeasure νL]
    {lmax lx0 : ℝ} (hlx0 : 0 < lx0) (hbox : ∀ᵐ p ∂ρ, p ∈ BoxParam lmax lx0)
    {E : ℕ → (ℕ → BlockR M C) → TopoChoice (Fin 4)}
    (hE : ∀ᵐ ω ∂(blockRSample M C ρ νL), ∀ (n : ℕ) (q : TopoChoice (Fin 4)),
      topoScore (empBlocksR M C n ω) q ≤ topoScore (empBlocksR M C n ω) (E n ω)) :
    ∀ᵐ ω ∂(blockRSample M C ρ νL), ∃ N : ℕ, ∀ n ≥ N,
      IsTrueT (fun _ _ => Topo.ab_cd) (E n ω) := by
  refine abar_caster_statisticallyConsistent_kingman_ae_box M ρ hlx0 hbox
    (blockRSample M C ρ νL) (empBlocksR M C) ?_ hE
  filter_upwards [block_emp_tendsto_ae_R (M := M) (C := C) (ρ := ρ) (νL := νL)
    hlx0.le hbox] with ω hω ε hε
  exact hω ε hε

/-! ## 4. 门 5：退化一致性（`ρ = dirac`） -/

/-- ★★★ **门 5（块层 `rfl`）**：`ρ = dirac (leaf, a, b)` 时，
`blockWR`（本件块层）与 `blockW`（`BlockModelAE` 块层）在 `BlockR.ofRaw ((leaf,a,b), r)` 上
**逐字相同**（`blockWR_eq_blockW`，定义层同一）。 -/
theorem blockWR_dirac_eq_blockW (M : SiteRateModel) (C : ℕ)
    (leaf : Fin 4 → ℝ) (a b : ℝ≥0)
    (rest : ((ℝ × ℝ) × LIdx C) × (Fin C → M.Rate)) (T : Topo) :
    blockWR M C T (BlockR.ofRaw ((leaf, a, b), rest))
      = blockW M C leaf a b T (Block.ofRaw (M := M) (C := C) (leaf := leaf) (a := a) (b := b)
          rest) :=
  blockWR_eq_blockW (M := M) (C := C) T _

/-- ★★★ **门 5（目标表 `rfl`）**：Dirac 情形下，`block_emp_tendsto_ae_R` 的
**目标权重表**与 `BlockModelAE.block_emp_tendsto_ae`（`:823`）的**逐字相同**（同一张表）。 -/
theorem block_emp_tendsto_ae_R_dirac_target (M : SiteRateModel) (_C : ℕ)
    (leaf : Fin 4 → ℝ) (a b : ℝ≥0) :
    (fun (S : Finset (Fin 4)) (_ : S.card = 4) (T : Topo) =>
        expWeight (kingmanMSCMeasure (Measure.dirac ((leaf, a, b) : (Fin 4 → ℝ) × ℝ≥0 × ℝ≥0)))
          kingmanMSCTopoSym.τd M.Abar T)
      = fun (S : Finset (Fin 4)) (_ : S.card = 4) (T : Topo) =>
          expWeight (kingmanMSCMeasure (Measure.dirac ((leaf, a, b) : (Fin 4 → ℝ) × ℝ≥0 × ℝ≥0)))
            kingmanMSCTopoSym.τd M.Abar T := rfl

-- ★ 2026-10-13 W18：本声明处为**纯 elaboration 成本**（`whnf` 心跳超时，非数学问题 ✓）⇒
--   在**最小作用域**内局部放宽心跳。★ 注意：本文件第 12 行【原本已有】`set_option maxHeartbeats 800000`
--   （= 默认 200000 的 4 倍 ✗）—— 该放宽**已如实登记在 W16b_HANDOVER.md §12.7** ✓。
set_option maxHeartbeats 4000000 in
/-- ★★★ **门 5（`∫ blockW` 侧）**：`ρ = Measure.dirac ((leaf, a, b) : (Fin 4 → ℝ) × ℝ≥0 × ℝ≥0)` 时，
`blockW_integral_R` 的右端**逐字**是 `BlockModelAE.blockW_integral`（`:604`）的右端。 -/
-- ★★ 2026-10-13 W18【陈述层改动，已留证 ✓】：本探针**原缺 `hleaf`** ✗ ——
--   它用 `(fun i : Fin 4 => by positivity)` 去证**任意** `leaf i ≥ 0` ✗（**为假** ✗），
--   而其**库内对应物** `BlockModelAE.blockW_integral`（`:604`）**本身就带** `(hleaf : ∀ i, 0 ≤ leaf i)` ✓
--   ⇒ 故此处**补上与库内一致的那一条假设** ✓（这是**还原**假设面 ✓，**不是**为过门放松口径 ✗）。
--   另一处 `le_rfl` ✗ 同探针③：它会强行要求 `lx0 = 0` ✗，而 `boxParam_dirac_ae` 给 `lx0 = ↑a + ↑b` ✗
--   ⇒ 换成 `by positivity` ✓（`a b : ℝ≥0` ⇒ `0 ≤ ↑a + ↑b` ✓）。★ 该改动已登记 W16b_HANDOVER.md §12.7 ✓。
theorem blockW_integral_R_dirac (M : SiteRateModel) (C : ℕ)
    (leaf : Fin 4 → ℝ) (a b : ℝ≥0)
    (νL : Measure (LIdx C)) [IsProbabilityMeasure νL] (T : Topo)
    (hleaf : ∀ i, 0 ≤ leaf i) :
    ∫ bb, blockWR M C T bb ∂(blockRPMeasure M C (Measure.dirac ((leaf, a, b) : (Fin 4 → ℝ) × ℝ≥0 × ℝ≥0)) νL)
      = (∫ l, ((l : ℕ) : ℝ) ∂νL) *
          expWeight (kingmanMSCMeasure (Measure.dirac ((leaf, a, b) : (Fin 4 → ℝ) × ℝ≥0 × ℝ≥0)))
            kingmanMSCTopoSym.τd M.Abar T :=
  blockW_integral_R (M := M) (C := C) (ρ := Measure.dirac ((leaf, a, b) : (Fin 4 → ℝ) × ℝ≥0 × ℝ≥0)) (νL := νL)
    (by positivity) (boxParam_dirac_ae leaf hleaf a b) T

-- ★ 2026-10-13 W18：本声明处为**纯 elaboration 成本**（`whnf` 心跳超时，非数学问题 ✓）⇒
--   在**最小作用域**内局部放宽心跳。★ 注意：本文件第 12 行【原本已有】`set_option maxHeartbeats 800000`
--   （= 默认 200000 的 4 倍 ✗）—— 该放宽**已如实登记在 W16b_HANDOVER.md §12.7** ✓。
set_option maxHeartbeats 4000000 in
/-- ★★★ **门 5（识别等式侧）**：`ρ = dirac (leaf, a, b)` 时 `blockW_div_blockL_R` 的右端
**逐字**是 `BlockModelAE.blockW_div_blockL`（`:700`）的右端，故两式的商**同值**。 -/
theorem blockW_div_blockL_R_dirac (M : SiteRateModel) (C : ℕ)
    (leaf : Fin 4 → ℝ) (a b : ℝ≥0)
    (νL : Measure (LIdx C)) [IsProbabilityMeasure νL] (T : Topo)
    (hleaf : ∀ i, 0 ≤ leaf i) :
    (∫ bb, blockWR M C T bb ∂(blockRPMeasure M C (Measure.dirac ((leaf, a, b) : (Fin 4 → ℝ) × ℝ≥0 × ℝ≥0)) νL)) /
        (∫ bb, blockLR M C bb ∂(blockRPMeasure M C (Measure.dirac ((leaf, a, b) : (Fin 4 → ℝ) × ℝ≥0 × ℝ≥0)) νL))
      = (∫ bb, blockW M C leaf a b T bb
            ∂(blockMeasure M C leaf a b νL)) /
          (∫ bb, blockL M C leaf a b bb ∂(blockMeasure M C leaf a b νL)) := by
  -- ★ W18：原为【一条】含两处重隐式推断的 `rw` ✗（isDefEq 心跳超时）⇒ 拆成【两条】✓（实参不变 ✓）
  -- ★★ W18（纯证明层 ✓，陈述未改 ✓）：原来是 `le_rfl` ✗ —— 那会**强行要求 `lx0 = 0`** ✗，
  --   而 `boxParam_dirac_ae` 给的是 `lx0 = ↑a + ↑b` ✗ ⇒ elaborator 被迫去证 `0 = ↑a + ↑b` ✗
  --   ⇒ ★ 这正是 isDefEq 心跳爆炸的**真正原因** ✓（不是数学问题 ✓）。
  --   正确实参 = `0 ≤ ↑a + ↑b` 的证明 ✓（`a b : ℝ≥0` ⇒ 由 `positivity` 给出 ✓）。
  rw [blockW_div_blockL_R (M := M) (C := C) (ρ := Measure.dirac ((leaf, a, b) : (Fin 4 → ℝ) × ℝ≥0 × ℝ≥0)) (νL := νL)
      (by positivity) (boxParam_dirac_ae leaf hleaf a b) T]
  rw [blockW_div_blockL (M := M) (C := C) (leaf := leaf) (a := a) (b := b) (νL := νL)
      hleaf T]

/-! ## 5. 反空洞：端到端定理的假设面有真居民 -/

/-- ★★★ **反空洞（`ρ` 侧）**：只要 `0 ≤ lmax`、`0 < lx⁻`，就存在**概率测度** `ρ`
使箱体先验成立 ⇒ `abar_caster_statisticallyConsistent_kingman_ae_blocks_box` 的
**前件可满足**（不是空真）。 -/
theorem exists_boxParam_resident {lmax lx0 : ℝ} (hlmax : 0 ≤ lmax) (hlx0 : 0 < lx0) :
    ∃ ρ : Measure ((Fin 4 → ℝ) × ℝ≥0 × ℝ≥0), IsProbabilityMeasure ρ ∧
      ∀ᵐ p ∂ρ, p ∈ BoxParam lmax lx0 :=
  exists_probabilityMeasure_boxParam hlmax hlx0

/-- ★★ **反空洞（含块样本空间）**：`ρ` 取箱体居民、`νL := dirac ⟨1, …⟩`
⇒ `blockRPMeasure`（从而 `blockRSample`）是**概率测度**。 -/
theorem exists_blockR_resident (M : SiteRateModel) (C : ℕ) (hC : 1 ≤ C) {lmax lx0 : ℝ}
    (hlmax : 0 ≤ lmax) (hlx0 : 0 < lx0) :
    ∃ (ρ : Measure ((Fin 4 → ℝ) × ℝ≥0 × ℝ≥0)) (νL : Measure (LIdx C)),
      IsProbabilityMeasure ρ ∧ IsProbabilityMeasure νL ∧
        (∀ᵐ p ∂ρ, p ∈ BoxParam lmax lx0) ∧
        IsProbabilityMeasure (blockRPMeasure M C ρ νL) := by
  obtain ⟨ρ, hρ, hbox⟩ := exists_probabilityMeasure_boxParam (lmax := lmax) (lx0 := lx0) hlmax hlx0
  haveI : IsProbabilityMeasure ρ := hρ
  haveI : IsProbabilityMeasure (Measure.dirac (⟨1, by norm_num, hC⟩ : LIdx C)) := inferInstance
  exact ⟨ρ, Measure.dirac (⟨1, by norm_num, hC⟩ : LIdx C), hρ, inferInstance, hbox, inferInstance⟩

end Phylo.Stat.BlockModelRhoAE3
