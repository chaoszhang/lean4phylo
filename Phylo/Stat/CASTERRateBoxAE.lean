/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.Stat.CASTERRateAE
import Phylo.Stat.SiteWeightMeasurable

/-!
# `Phylo.Stat.CASTERRateBoxAE` —— 箱体先验下的 `Ã` 有界性 ＋ 一般物种树测度 `ρ` 的端到端（W15a）

> ★★ **本件超出 W13 规格（beyond-spec）**：规格 §1.2 把物种树取为**固定**的
> （等价于 `ρ = Measure.dirac (leaf, a, b)`），故 **Dirac 情形已经满足规格**；
> 本件是**对库内一般性的加强** —— 把「确定物种树」换成「一般概率测度 `ρ` ＋ 叶长有界先验」。

## 0. 这一批解决的问题（缺口原文）

`Phylo/Stat/CASTERRateAE.lean`（文件头 §诚实边界 1，第 63–66 行）把残留缺口写得很清楚：

> `hf_int` / `hint` 只在「确定物种树」（`ρ = Measure.dirac (leaf, a, b)`）下被消掉。
> 一般 `ρ` 下 `Ã` 关于**叶长**无一致界（`Phylo.JC.e t = exp(−(4/3)t)` 在 `t → −∞` 时爆炸），
> 所以 `hint` 需要「`ρ`-a.e. 叶长有界」这类**对物种树侧先验的条件**。

本文件把这个「需要」**写成一个显式的箱体先验**，并在该先验下把 `hint` / `hf_int`
**真正证掉**（不再作为假设传递）：

```
箱体先验：ρ-a.e. 物种树参数落在  BoxParam lmax lx⁻
          （叶长 i ∈ [0, lmax]、内部枝长 a + b ≥ lx⁻ > 0）
                │  推前  (kingmanMSCMeasure)
                ▼
          ν-a.e. θ ∈ BoxTheta lmax lx⁻
                │
                ├── §2  ★  Ã / f̃ / hint 被积函数在箱体上**一致有界（界 = 1）**
                ▼
          §3  Integrable  ⇒  hf_int / hint   （CASTERRateAE 里的两个假设）
                │
                ▼
          §5  abarTopoIdealBox ：一般 ρ 上的 TopoIdeal（不再需要 Dirac）
                │
                ▼
          §6  端到端 a.e. 统计一致性（一般 ρ 版本）
```

## 1. ★ 上界与下界的区别，以及一条**比派单更弱的前提**（★D 交代）

派单的提示里写「`Ã` 的上界与 `f̃` 的下界不是一回事」——**这正是本件的技术要点**：

* `SiteRateMixture.deltaBox_le_fbar`（下界）用的是「叶长 `≤ lmax` ⇒ `∏ e(叶长)` 有**正**下界」
  与「内枝长 `≥ lx⁻` ⇒ `1 − e(内枝长)` 有正下界」；
* 本文件的**上界**走的是**完全不同的**一条路：`|geneScore S l lx T| ≤ 1`
  （库内 ★★ B3 主件 `SiteWeightMeasurable.abs_geneScore_le_one`，
  **前提恰是枝长非负**）＋ 凸组合（`w ≥ 0`、`∑ w = 1`）＋ `|τd| ≤ 1`。于是：

  ```
  |Ã θ T' r| ≤ ∑_k w_k · |A(scale θ k) T' r| ≤ ∑_k w_k · 1 = 1
  |∑_{T'} τd θ T' · Ã θ T' T| ≤ ∑_{T'} |τd θ T'| · 1 = ∑_{T'} τd θ T' = 1
  ```

  ⇒ **叶长只用在「非负」这一条**（箱体给 `0 ≤ 叶长`），**根本不需要叶长的上界 `lmax`**。

⇒ ★★ **本件如实报告一条比派单更强的结论**（即：前提更弱）：
`hint` / `hf_int` 的**可积性只需要「`ν`-a.e. 叶长非负」**
（本文件 §3 的 `ae_abs_*` 系列与 `*_integrable_of_box` 只用到 `0 ≤ 叶长` 与 `0 ≤ 内枝长`）。
`lmax` 在**证明里没有被用到**；它之所以留在 `BoxParam` / `BoxTheta` 里，是为了让**同一个**
先验同时服务于 `SiteRateMixture.deltaBox_le_fbar` 要的**下界**（那里必须 `叶长 ≤ lmax`）。
⇒ 所以「箱体」是**两类界的公共量化域**，而不是上界所必需（见文件头 §4 诚实边界 2）。

真正需要**正下界**的是 `hlx`（`¬deep ⇒ 0 < 内部枝长`）：它由箱体的内枝长下界 `0 < lx⁻` 供给。

## 2. ★ 消掉了哪些假设（与既有的两条端点对比）

| 假设 | `abarTopoIdeal`（`CASTERRateAE`） | `abarTopoIdeal_kingman`（Dirac） | 本文件 `abarTopoIdealBox`（一般 ρ） |
|---|---|---|---|
| `hdeep` | 假设 | 定理 | 定理 |
| `hf_pos` | 定理 | 定理 | 定理 |
| `hf_int` | **假设** | 定理（Dirac ⇒ `f̃` 常值） | **定理**（箱体 ⇒ 一致界 `1`） |
| `hint` | **假设** | 定理（同上） | **定理**（箱体 ⇒ 一致界 `1`） |
| `hpos` | 假设 | 定理（`dirac_notDeep_pos`） | **定理**（箱体的**下**界 ⇒ `1−e^{−(a+b)}` 有正下界） |
| `hlx` | 假设 | 定理（`lx = a + b > 0`） | **定理**（箱体的内枝长下界） |
| 物种树 | 一般 `ρ` | Dirac | **一般概率测度 `ρ` ＋ 箱体先验** |

## 3. 主要声明（`namespace Phylo.Stat.CASTERRateBoxAE`）

* §1 箱体：`BoxParam`（物种树侧）、`BoxTheta`（`KingmanΘ` 上）＋ 两者的可测性；
* §2 上界：`abs_jc69Amp_le_one`、`abs_A_scaled_le_one`、`abs_Abar_le_one_of_box`、
  `abs_f_scaled_le_one`、`abs_fbar_le_one_of_box`、`abs_tauD_le_one`、`abs_hint_le_one`；
* §3 可积：`abar_integrable_of_box`、`fbar_integrable_of_box`、`abarHint_integrable_of_box`
  ＋ 它们的 `ρ` 直用版（`…_of_boxParam`）；
* §4 推前：`measurableSet_boxParam` / `measurableSet_boxTheta` / `boxTheta_toKingmanΘ` /
  `measure_boxParam_eq_one_iff` / `ae_boxTheta_of_ae_boxParam` / `ae_boxTheta_of_boxParam_eq_one`；
* §5 ★★ 一般 `ρ` 的 `TopoIdeal`：`abarTopoIdealBox` ＋ `abarTopoIdealBox_W` ＋ `abarTopoIdealBox_propB`；
* §6 ★★★ 端到端：`abar_caster_statisticallyConsistent_kingman_ae_box`；
* §7 退化一致性（★最强探针）：`boxParam_dirac_ae` ＋ `abarTopoIdealBox_dirac_W`
  —— **Dirac 是本文件箱体先验的一个特例**，且此时 `W` **逐字退回**库内旗舰端点；
* §8 反空洞：箱体在「`0 ≤ lmax`、`lx⁻ > 0`」下有**概率测度**居民（不是空真）。

## 4. 诚实边界（逐条，不藏）

1. **`hpos` 也是定理（不再是假设）—— 这里更正一个我先前写错的口径**：
   `ν(¬deep) = ∫⁻_ρ (1 − e^{−(a+b)}) dρ`，而 `1 − e^{−(a+b)}` 对 `a + b` **单调递增**
   ⇒ 要它有正下界，需要的是 `a + b` 的**正下界**，**不是上界**
   （`a + b → ∞` 只会让它 `→ 1`）。箱体恰好给 `a + b ≥ lx⁻ > 0`
   ⇒ `1 − e^{−(a+b)} ≥ 1 − e^{−lx⁻} > 0` ⇒ `hpos` 成立
   （`kingmanMSCMeasure_notDeep_pos_of_boxParam`；实现取 `max(a,b) ≥ lx⁻/2` 的一侧，
   避开 `ENNReal` 减法）。★ 由 `lmax` 确实补不上 —— 但它补的本来就不是需要的那一端。
2. **`lmax` 在本文件的证明里没有被用到**（上界 = `1` 只靠「枝长非负」＋凸组合）。
   保留它是为了让**同一个**先验同时服务于 `SiteRateMixture.deltaBox_le_fbar`（下界）。
   这**不是**装饰：`BoxParam` / `BoxTheta` 是「箱体」这一量化域的载体。
3. **`π` / `κ` 仍只登记不使用**：本文件走 JC69 端（`π ≡ 1/4`、无 `κ`），
   与 `SiteRateMixture` / `CASTERRateAE` / `BlockModelAE` 口径一致。
4. **端到端的层次**：§6 的定理与 `CASTERRateAE.abar_caster_statisticallyConsistent_kingman_ae`
   **同形**（`hconv` 仍作为参数），只是把「`ρ` 是 Dirac」换成「`ρ` 满足箱体先验」。
   ⚠️ **没有**升到 `BlockModelAE.abar_caster_statisticallyConsistent_kingman_ae_blocks`
   那一层（**不假设 `hconv`**）：那一层的块概率空间（`Block M C leaf a b`）
   **把物种树固定在 `(leaf, a, b)` 里**，要一般 `ρ` 就得重造一个「物种树也随机」的块空间
   并重证其坐标独立 / 恒同分布 / `hlim` / `hL1` —— 那是**另一件**，本文件**不做**，如实登记。
5. **`θ` 的枝长口径**：沿用 `SiteRateMixture.scale`（逐基因树逐枝**常数**速率乘子），
   比「物种树各枝独立抽速率」粗一档 —— 完整交代见 `SiteRateMixture.lean` 文件头 §诚实边界 2。
6. **`set_option linter.style.haveILetI false`**：本文件与库内 `MSCKingmanMeasure.lean:89`、
   `KingmanCoalescent.lean:130`、`CASTERRateAE.lean:81` 采用同一处置。
   本文件里出现 `haveI` 的确切位置**只有一处**：登记
   `IsProbabilityMeasure (sojournLaw 2)`（它让 `Measure.map_fst_prod` 的 `SFinite` 前提可解）。
   这只关风格，**不改任何陈述**。
7. **无未完成证明 / 无新增公理声明**：全部声明正面构造。
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory
open scoped NNReal ENNReal

namespace Phylo.Stat.CASTERRateBoxAE

open Phylo.Stat.CASTERWeights (Topo)
open Phylo.Stat.CASTEREngine
open Phylo.Stat.CASTERBridge
open Phylo.Stat.CASTERTopo
open Phylo.Stat.CASTERGeneTree
open Phylo.Stat.MSCKingman
open Phylo.Stat.MSCKingmanMeasure
open Phylo.Stat.KingmanCoalescent
open Phylo.Stat.SiteRateMixture
open Phylo.Stat.CASTERRateAE
open Phylo.Stat.SiteWeightMeasurable

/-! ## 1. 箱体：两类界（下界与上界）的公共量化域 -/

/-- ★★ **物种树侧的箱体**：叶长 `∈ [0, lmax]`、内部枝长 `a + b ≥ lx⁻`。

（`a b : ℝ≥0` 故 `a + b ≥ 0` 自动成立，`lx⁻` 的作用是给**正**下界。） -/
def BoxParam (lmax lx0 : ℝ) : Set ((Fin 4 → ℝ) × ℝ≥0 × ℝ≥0) :=
  {p | (∀ i : Fin 4, 0 ≤ p.1 i ∧ p.1 i ≤ lmax) ∧ lx0 ≤ (p.2.1 : ℝ) + (p.2.2 : ℝ)}

/-- ★★ **`KingmanΘ` 上的箱体**（`BoxParam` 经 `toKingmanΘ` 的像）：
叶长 `θ.1.1 i ∈ [0, lmax]`、内部枝长 `θ.1.2 ≥ lx⁻`。 -/
def BoxTheta (lmax lx0 : ℝ) : Set KingmanΘ :=
  {θ | (∀ i : Fin 4, 0 ≤ θ.1.1 i ∧ θ.1.1 i ≤ lmax) ∧ lx0 ≤ θ.1.2}

/-- ★ **`Fin 4 → ℝ` 上的叶长箱体可测**（`Fin 4` 上的可数交）。 -/
theorem measurableSet_leafBox (lmax : ℝ) :
    MeasurableSet {l : Fin 4 → ℝ | ∀ i : Fin 4, l i ∈ Set.Icc (0 : ℝ) lmax} := by
  rw [show {l : Fin 4 → ℝ | ∀ i : Fin 4, l i ∈ Set.Icc (0 : ℝ) lmax}
      = ⋂ i : Fin 4, (fun l : Fin 4 → ℝ => l i) ⁻¹' (Set.Icc (0 : ℝ) lmax) from by
        ext l
        simp]
  exact MeasurableSet.iInter fun i =>
    (measurable_pi_apply i) (measurableSet_Icc : MeasurableSet (Set.Icc (0 : ℝ) lmax))

/-- ★ **`BoxParam` 可测**（叶长部分由 `measurableSet_leafBox` 沿投影拉回，内枝长部分一个 `Ici` 原像）。 -/
theorem measurableSet_boxParam (lmax lx0 : ℝ) : MeasurableSet (BoxParam lmax lx0) := by
  have h1 : MeasurableSet {p : (Fin 4 → ℝ) × ℝ≥0 × ℝ≥0 |
      ∀ i : Fin 4, p.1 i ∈ Set.Icc (0 : ℝ) lmax} := by
    have hbase := measurableSet_leafBox lmax
    have hproj : Measurable (fun p : (Fin 4 → ℝ) × ℝ≥0 × ℝ≥0 => p.1) := measurable_fst
    simpa using hproj hbase
  have h2 : MeasurableSet ((fun p : (Fin 4 → ℝ) × ℝ≥0 × ℝ≥0 =>
      (p.2.1 : ℝ) + (p.2.2 : ℝ)) ⁻¹' Set.Ici lx0) :=
    ((measurable_subtype_coe.comp measurable_snd.fst).add
      (measurable_subtype_coe.comp measurable_snd.snd)) measurableSet_Ici
  have hmem : BoxParam lmax lx0
      = {p : (Fin 4 → ℝ) × ℝ≥0 × ℝ≥0 | ∀ i : Fin 4, p.1 i ∈ Set.Icc (0 : ℝ) lmax}
        ∩ ((fun p : (Fin 4 → ℝ) × ℝ≥0 × ℝ≥0 => (p.2.1 : ℝ) + (p.2.2 : ℝ)) ⁻¹'
            Set.Ici lx0) := by
    ext p
    simp [BoxParam, Set.mem_Icc]
  rw [hmem]
  exact h1.inter h2

/-- ★ **`BoxTheta` 可测**。 -/
theorem measurableSet_boxTheta (lmax lx0 : ℝ) : MeasurableSet (BoxTheta lmax lx0) := by
  have h1 : MeasurableSet {θ : KingmanΘ | ∀ i : Fin 4, θ.1.1 i ∈ Set.Icc (0 : ℝ) lmax} := by
    have hbase := measurableSet_leafBox lmax
    have hproj : Measurable (fun θ : KingmanΘ => θ.1.1) := measurable_fst.fst
    simpa using hproj hbase
  have h2 : MeasurableSet ((fun θ : KingmanΘ => θ.1.2) ⁻¹' Set.Ici lx0) :=
    (measurable_snd.comp measurable_fst) measurableSet_Ici
  have hmem : BoxTheta lmax lx0
      = {θ : KingmanΘ | ∀ i : Fin 4, θ.1.1 i ∈ Set.Icc (0 : ℝ) lmax}
        ∩ ((fun θ : KingmanΘ => θ.1.2) ⁻¹' Set.Ici lx0) := by
    ext θ
    simp [BoxTheta, Set.mem_Icc]
  rw [hmem]
  exact h1.inter h2

/-! ## 2. ★ 上界：箱体上 `Ã` / `f̃` / `hint` 被积函数**一致有界（界 = 1）** -/

/-- ★★ **`|jc69Amp l lx| ≤ 1`**（枝长非负）。

`jc69Amp l lx = (3/4)·∏_i e(l_i)·(1 − e(lx))`，三个因子都落在 `[0, 1]`：
`∏ e(l_i) ≤ 1` 由 `e ≤ 1`（非负枝长）＋ `prod_four_le`，`1 − e(lx) ≤ 1` 由 `e > 0`。

★ 这条是 `Ã` 的**上界**的支点（`SiteRateMixture` 的 `deltaBox` 给的是**下界**）。 -/
theorem abs_jc69Amp_le_one {l : Fin 4 → ℝ} {lx : ℝ} (hl : ∀ i, 0 ≤ l i) (hlx : 0 ≤ lx) :
    |jc69Amp l lx| ≤ 1 := by
  have hPnn : 0 ≤ ∏ i : Fin 4, Phylo.JC.e (l i) :=
    Finset.prod_nonneg fun i _ => (Real.exp_pos _).le
  have hPle : (∏ i : Fin 4, Phylo.JC.e (l i)) ≤ 1 := by
    have h := SiteRateModel.prod_four_le (a := fun i : Fin 4 => Phylo.JC.e (l i))
      (b := fun _ : Fin 4 => (1 : ℝ)) (fun i => (Real.exp_pos _).le)
      (fun i => SiteRateModel.e_le_one_of_nonneg (hl i))
    simpa using h
  have hInn : 0 ≤ 1 - Phylo.JC.e lx := by
    have h := SiteRateModel.e_le_one_of_nonneg hlx
    linarith
  have hIle : 1 - Phylo.JC.e lx ≤ 1 := by
    have h : 0 < Phylo.JC.e lx := Real.exp_pos _
    linarith
  have hnn : 0 ≤ jc69Amp l lx := by
    simp only [jc69Amp]
    exact mul_nonneg (mul_nonneg (by norm_num) hPnn) hInn
  rw [abs_of_nonneg hnn]
  simp only [jc69Amp]
  calc (3 / 4) * (∏ i : Fin 4, Phylo.JC.e (l i)) * (1 - Phylo.JC.e lx)
      ≤ (3 / 4) * 1 * 1 :=
        mul_le_mul (mul_le_mul_of_nonneg_left hPle (by norm_num)) hIle hInn (by norm_num)
    _ ≤ 1 := by norm_num

/-- ★★ **单个速率类别的箱体上界**：箱体上 `|A(scale θ k) T' r| ≤ 1`。

证明：`A` 就是 `geneScore`，而 `scale θ k` 的枝长非负（`r ≥ rL > 0`、`ρ ≥ ρL > 0`、
叶长 `≥ 0`、内枝长 `≥ 0`），故直接吃 ★★ B3 主件。 -/
theorem abs_A_scaled_le_one (M : SiteRateModel) {lmax lx0 : ℝ} (hlx0 : 0 ≤ lx0)
    {θ : KingmanΘ} (hbox : θ ∈ BoxTheta lmax lx0) (k : M.Rate) (T' r : Topo) :
    |jc69PropAData.A (Prod.fst (M.scale θ k)) T' r| ≤ 1 := by
  have hb : (∀ i : Fin 4, 0 ≤ Prod.fst (Prod.fst θ) i ∧ Prod.fst (Prod.fst θ) i ≤ lmax)
      ∧ lx0 ≤ Prod.snd (Prod.fst θ) := hbox
  rw [SiteRateModel.A_scaled_eq_geneScore, SiteRateModel.scale_fst_fst,
    SiteRateModel.scale_fst_snd]
  refine abs_geneScore_le_one T' r _ _ ?_ ?_
  · intro i
    exact mul_nonneg (mul_nonneg (le_trans M.rL_pos.le (M.rL_le k i))
      (le_trans M.ρL_pos.le (M.ρL_le k))) (hb.1 i).1
  · exact mul_nonneg (le_trans M.ρL_pos.le (M.ρL_le k)) (le_trans hlx0 hb.2)

/-- ★★★ **箱体上 `Ã` 一致有界：`|Ã θ T' r| ≤ 1`**。

```
|∑_k w_k · A(scale θ k) T' r| ≤ ∑_k w_k · |A(scale θ k) T' r| ≤ ∑_k w_k · 1 = 1
```

（用 `w ≥ 0`、`∑ w = 1` —— 即 `Ã` 是**凸组合**，故上界与 `k` 无关。） -/
theorem abs_Abar_le_one_of_box (M : SiteRateModel) {lmax lx0 : ℝ} (hlx0 : 0 ≤ lx0)
    {θ : KingmanΘ} (hbox : θ ∈ BoxTheta lmax lx0) (T' r : Topo) :
    |M.Abar θ T' r| ≤ 1 := by
  rw [SiteRateModel.Abar]
  calc |∑ k : M.Rate, M.w k * jc69PropAData.A (Prod.fst (M.scale θ k)) T' r|
      ≤ ∑ k : M.Rate, |M.w k * jc69PropAData.A (Prod.fst (M.scale θ k)) T' r| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k : M.Rate, M.w k * |jc69PropAData.A (Prod.fst (M.scale θ k)) T' r| := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [abs_mul, abs_of_nonneg (M.w_nonneg k)]
    _ ≤ ∑ k : M.Rate, M.w k * 1 := by
        refine Finset.sum_le_sum fun k _ => ?_
        exact mul_le_mul_of_nonneg_left (abs_A_scaled_le_one M hlx0 hbox k T' r)
          (M.w_nonneg k)
    _ = 1 := by simp [M.w_sum]

/-- ★★ **单个速率类别的箱体上界（`f` 版）**：`|f(scale θ k)| ≤ 1`。 -/
theorem abs_f_scaled_le_one (M : SiteRateModel) {lmax lx0 : ℝ} (hlx0 : 0 ≤ lx0)
    {θ : KingmanΘ} (hbox : θ ∈ BoxTheta lmax lx0) (k : M.Rate) :
    |jc69PropAData.f (Prod.fst (M.scale θ k))| ≤ 1 := by
  have hb : (∀ i : Fin 4, 0 ≤ Prod.fst (Prod.fst θ) i ∧ Prod.fst (Prod.fst θ) i ≤ lmax)
      ∧ lx0 ≤ Prod.snd (Prod.fst θ) := hbox
  rw [SiteRateModel.f_scaled_eq_amp, SiteRateModel.ampScaled_eq_jc69Amp]
  refine abs_jc69Amp_le_one (fun i => ?_) (mul_nonneg (le_trans M.ρL_pos.le (M.ρL_le k))
    (le_trans hlx0 hb.2))
  exact mul_nonneg (mul_nonneg (le_trans M.rL_pos.le (M.rL_le k i))
    (le_trans M.ρL_pos.le (M.ρL_le k))) (hb.1 i).1

/-- ★★★ **箱体上 `f̃` 一致有界：`|f̃ θ| ≤ 1`**（同一凸组合论证）。 -/
theorem abs_fbar_le_one_of_box (M : SiteRateModel) {lmax lx0 : ℝ} (hlx0 : 0 ≤ lx0)
    {θ : KingmanΘ} (hbox : θ ∈ BoxTheta lmax lx0) : |M.fbar θ| ≤ 1 := by
  rw [SiteRateModel.fbar]
  calc |∑ k : M.Rate, M.w k * jc69PropAData.f (Prod.fst (M.scale θ k))|
      ≤ ∑ k : M.Rate, |M.w k * jc69PropAData.f (Prod.fst (M.scale θ k))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k : M.Rate, M.w k * |jc69PropAData.f (Prod.fst (M.scale θ k))| := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [abs_mul, abs_of_nonneg (M.w_nonneg k)]
    _ ≤ ∑ k : M.Rate, M.w k * 1 := by
        refine Finset.sum_le_sum fun k _ => ?_
        exact mul_le_mul_of_nonneg_left (abs_f_scaled_le_one M hlx0 hbox k) (M.w_nonneg k)
    _ = 1 := by simp [M.w_sum]

/-- ★★ **`|τd θ T'| ≤ 1`**（对**任意** `MSCTopoSym`：由 `τd_nonneg` ＋ `τd_sum = 1`）。 -/
theorem abs_tauD_le_one {Θ : Type*} (S : MSCTopoSym Θ) (θ : Θ) (T' : Topo) :
    |S.τd θ T'| ≤ 1 := by
  have h1 : S.τd θ T' ≤ ∑ T : Topo, S.τd θ T :=
    Finset.single_le_sum (fun j _ => S.τd_nonneg θ j) (Finset.mem_univ T')
  rw [S.τd_sum θ] at h1
  rw [abs_of_nonneg (S.τd_nonneg θ T')]
  exact h1

/-- ★★★ **正文条件 (2)（「权重一致有界」，`hint` 的被积函数）在箱体上一致有界：界 `= 1`**。

```
|∑_{T'} τd θ T' · Ã θ T' T| ≤ ∑_{T'} |τd θ T'| · 1 = ∑_{T'} τd θ T' = 1
```

（`τd` 非负、全概率 `1`；`Ã` 的界来自 `abs_Abar_le_one_of_box`。） -/
theorem abs_hint_le_one (S : MSCTopoSym KingmanΘ) (M : SiteRateModel) {lmax lx0 : ℝ}
    (hlx0 : 0 ≤ lx0) {θ : KingmanΘ} (hbox : θ ∈ BoxTheta lmax lx0) (T : Topo) :
    |∑ T' : Topo, S.τd θ T' * M.Abar θ T' T| ≤ 1 := by
  calc |∑ T' : Topo, S.τd θ T' * M.Abar θ T' T|
      ≤ ∑ T' : Topo, |S.τd θ T' * M.Abar θ T' T| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ T' : Topo, |S.τd θ T'| * |M.Abar θ T' T| :=
        Finset.sum_congr rfl fun T' _ => by rw [abs_mul]
    _ ≤ ∑ T' : Topo, |S.τd θ T'| * 1 := by
        refine Finset.sum_le_sum fun T' _ => ?_
        exact mul_le_mul_of_nonneg_left (abs_Abar_le_one_of_box M hlx0 hbox T' T)
          (abs_nonneg _)
    _ = ∑ T' : Topo, S.τd θ T' :=
        Finset.sum_congr rfl fun T' _ => by
          rw [mul_one, abs_of_nonneg (S.τd_nonneg θ T')]
    _ = 1 := S.τd_sum θ

/-! ## 3. ★★ 可积性：`hf_int` 与 `hint` **被证掉** -/

/-- ★★ **a.e. 版的 `Ã` 上界**（由箱体 a.e. 直接 `mono`；**不需要**界集的可测性）。 -/
theorem ae_abs_Abar_le_one (M : SiteRateModel) {ν : Measure KingmanΘ} {lmax lx0 : ℝ}
    (hlx0 : 0 ≤ lx0) (hbox : ∀ᵐ θ ∂ν, θ ∈ BoxTheta lmax lx0) (T' r : Topo) :
    ∀ᵐ θ ∂ν, |M.Abar θ T' r| ≤ 1 :=
  hbox.mono fun _ h => abs_Abar_le_one_of_box M hlx0 h T' r

/-- ★★ **a.e. 版的 `f̃` 上界**。 -/
theorem ae_abs_fbar_le_one (M : SiteRateModel) {ν : Measure KingmanΘ} {lmax lx0 : ℝ}
    (hlx0 : 0 ≤ lx0) (hbox : ∀ᵐ θ ∂ν, θ ∈ BoxTheta lmax lx0) :
    ∀ᵐ θ ∂ν, |M.fbar θ| ≤ 1 :=
  hbox.mono fun _ h => abs_fbar_le_one_of_box M hlx0 h

/-- ★★ **a.e. 版的 `hint` 被积函数上界**。 -/
theorem ae_abs_hint_le_one (S : MSCTopoSym KingmanΘ) (M : SiteRateModel)
    {ν : Measure KingmanΘ} {lmax lx0 : ℝ} (hlx0 : 0 ≤ lx0)
    (hbox : ∀ᵐ θ ∂ν, θ ∈ BoxTheta lmax lx0) (T : Topo) :
    ∀ᵐ θ ∂ν, |∑ T' : Topo, S.τd θ T' * M.Abar θ T' T| ≤ 1 :=
  hbox.mono fun _ h => abs_hint_le_one S M hlx0 h T

/-- ★★★ **`Ã` 在箱体先验下可积**（有限测度上「a.e. 有界 ＋ 可测 ⇒ 可积」）。 -/
theorem abar_integrable_of_box (M : SiteRateModel) {ν : Measure KingmanΘ} [IsFiniteMeasure ν]
    {lmax lx0 : ℝ} (hlx0 : 0 ≤ lx0) (hbox : ∀ᵐ θ ∂ν, θ ∈ BoxTheta lmax lx0) (T' r : Topo) :
    Integrable (fun θ : KingmanΘ => M.Abar θ T' r) ν :=
  integrable_of_abs_bound (measurable_Abar M T' r).aestronglyMeasurable
    (ae_abs_Abar_le_one M hlx0 hbox T' r)

/-- ★★★ **`f̃` 在箱体先验下可积** ⇒ `abarTopoIdeal` 的 `hf_int` 在箱体先验下**是定理**。 -/
theorem fbar_integrable_of_box (M : SiteRateModel) {ν : Measure KingmanΘ} [IsFiniteMeasure ν]
    {lmax lx0 : ℝ} (hlx0 : 0 ≤ lx0) (hbox : ∀ᵐ θ ∂ν, θ ∈ BoxTheta lmax lx0) :
    Integrable M.fbar ν :=
  integrable_of_abs_bound (measurable_fbar M).aestronglyMeasurable
    (ae_abs_fbar_le_one M hlx0 hbox)

/-- ★★★ **`hint` 的被积函数在箱体先验下可积**（`S = kingmanMSCTopoSym`）
⇒ `abarTopoIdeal` 的 `hint` 在箱体先验下**是定理**。 -/
theorem abarHint_integrable_of_box (M : SiteRateModel) {ν : Measure KingmanΘ}
    [IsFiniteMeasure ν] {lmax lx0 : ℝ} (hlx0 : 0 ≤ lx0)
    (hbox : ∀ᵐ θ ∂ν, θ ∈ BoxTheta lmax lx0) (T : Topo) :
    Integrable (fun θ : KingmanΘ =>
      ∑ T' : Topo, kingmanMSCTopoSym.τd θ T' * M.abarPropAData.A θ T' T) ν := by
  refine integrable_of_abs_bound (measurable_abarHint M T).aestronglyMeasurable (C := 1) ?_
  filter_upwards [hbox] with θ hθ
  have h := abs_hint_le_one kingmanMSCTopoSym M hlx0 hθ T
  simpa only [SiteRateModel.abarPropAData_A] using h

/-! ## 4. ★★ 从 `ρ` 侧推前到 `ν = kingmanMSCMeasure ρ` -/

/-- ★ **`toKingmanΘ` 保持箱体**（箱体条件只依赖第一分量，且 `toKingmanΘ` 的第二分量
就是把 `(a, b)` 加起来）：`toKingmanΘ q ∈ BoxTheta ↔ q.1 ∈ BoxParam`。 -/
theorem boxTheta_toKingmanΘ {lmax lx0 : ℝ}
    {q : ((Fin 4 → ℝ) × ℝ≥0 × ℝ≥0) × (ℝ × ℝ)} :
    toKingmanΘ q ∈ BoxTheta lmax lx0 ↔ Prod.fst q ∈ BoxParam lmax lx0 :=
  ⟨fun h => show Prod.fst q ∈ BoxParam lmax lx0 from h,
    fun h => show toKingmanΘ q ∈ BoxTheta lmax lx0 from h⟩

/-- ★★ **「`ρ (箱体) = 1`」与「`ρ`-a.e. 落在箱体里」等价**（概率测度）。 -/
theorem measure_boxParam_eq_one_iff {ρ : Measure ((Fin 4 → ℝ) × ℝ≥0 × ℝ≥0)}
    [IsProbabilityMeasure ρ] {lmax lx0 : ℝ} :
    ρ (BoxParam lmax lx0) = 1 ↔ ∀ᵐ p ∂ρ, p ∈ BoxParam lmax lx0 := by
  rw [ae_iff]
  change ρ (BoxParam lmax lx0) = 1 ↔ ρ (BoxParam lmax lx0)ᶜ = 0
  constructor
  · intro h
    rw [measure_compl (measurableSet_boxParam lmax lx0) (measure_ne_top ρ _), h, measure_univ,
      tsub_self]
  · intro h
    have h2 : ρ (BoxParam lmax lx0) + ρ (BoxParam lmax lx0)ᶜ = 1 := by
      rw [measure_add_measure_compl (measurableSet_boxParam lmax lx0), measure_univ]
    rw [h, add_zero] at h2
    exact h2

/-- ★★★ **箱体先验的推前**：`ρ`-a.e. 落在 `BoxParam` ⇒ `ν = kingmanMSCMeasure ρ`-a.e.
落在 `BoxTheta`。

证明：`ν = Measure.map toKingmanΘ (ρ ⊗ σ)`（`σ = sojournLaw 2 ⊗ sojournLaw 2`），
而箱体条件**只依赖第一分量**（`boxTheta_toKingmanΘ`），且
`(ρ ⊗ σ).map Prod.fst = σ univ • ρ = ρ`（`σ` 是概率测度）。 -/
theorem ae_boxTheta_of_ae_boxParam {ρ : Measure ((Fin 4 → ℝ) × ℝ≥0 × ℝ≥0)}
    {lmax lx0 : ℝ} (hρ : ∀ᵐ p ∂ρ, p ∈ BoxParam lmax lx0) :
    ∀ᵐ θ ∂(kingmanMSCMeasure ρ), θ ∈ BoxTheta lmax lx0 := by
  haveI : IsProbabilityMeasure (sojournLaw 2) := isProbabilityMeasure_sojournLaw (by norm_num)
  have hfst : (ρ.prod ((sojournLaw 2).prod (sojournLaw 2))).map Prod.fst = ρ := by
    rw [Measure.map_fst_prod, measure_univ, one_smul]
  have hρ' : ∀ᵐ y ∂(ρ.prod ((sojournLaw 2).prod (sojournLaw 2))).map Prod.fst,
      y ∈ BoxParam lmax lx0 := by
    rw [hfst]
    exact hρ
  have hq : ∀ᵐ q ∂(ρ.prod ((sojournLaw 2).prod (sojournLaw 2))),
      Prod.fst q ∈ BoxParam lmax lx0 :=
    (ae_map_iff measurable_fst.aemeasurable (measurableSet_boxParam lmax lx0)).mp hρ'
  rw [kingmanMSCMeasure]
  exact (ae_map_iff measurable_toKingmanΘ.aemeasurable (measurableSet_boxTheta lmax lx0)).mpr
    (hq.mono fun q hq => boxTheta_toKingmanΘ.mpr hq)

/-- ★★★ **`= 1` 形态的推前**（与 `ae_boxTheta_of_ae_boxParam` 等价，便于下游书写）。 -/
theorem ae_boxTheta_of_boxParam_eq_one {ρ : Measure ((Fin 4 → ℝ) × ℝ≥0 × ℝ≥0)}
    [IsProbabilityMeasure ρ] {lmax lx0 : ℝ} (hρ : ρ (BoxParam lmax lx0) = 1) :
    ∀ᵐ θ ∂(kingmanMSCMeasure ρ), θ ∈ BoxTheta lmax lx0 :=
  ae_boxTheta_of_ae_boxParam ((measure_boxParam_eq_one_iff).mp hρ)

/-- ★★★ **`ρ` 直用版（本件第一件的主结论）**：
只要 `ρ` 给箱体全测度，`Ã` 在 `ν = kingmanMSCMeasure ρ` 下**可积**。 -/
theorem abar_integrable_of_boxParam (M : SiteRateModel)
    {ρ : Measure ((Fin 4 → ℝ) × ℝ≥0 × ℝ≥0)} [IsProbabilityMeasure ρ]
    {lmax lx0 : ℝ} (hlx0 : 0 ≤ lx0) (hρ : ∀ᵐ p ∂ρ, p ∈ BoxParam lmax lx0) (T' r : Topo) :
    Integrable (fun θ : KingmanΘ => M.Abar θ T' r) (kingmanMSCMeasure ρ) :=
  abar_integrable_of_box M hlx0 (ae_boxTheta_of_ae_boxParam hρ) T' r

/-- ★★★ **`ρ` 直用版**：箱体先验下 `f̃` 可积（⇒ `hf_int`）。 -/
theorem fbar_integrable_of_boxParam (M : SiteRateModel)
    {ρ : Measure ((Fin 4 → ℝ) × ℝ≥0 × ℝ≥0)} [IsProbabilityMeasure ρ]
    {lmax lx0 : ℝ} (hlx0 : 0 ≤ lx0) (hρ : ∀ᵐ p ∂ρ, p ∈ BoxParam lmax lx0) :
    Integrable M.abarPropAData.f (kingmanMSCMeasure ρ) := by
  rw [show M.abarPropAData.f = M.fbar from rfl]
  exact fbar_integrable_of_box M hlx0 (ae_boxTheta_of_ae_boxParam hρ)

/-- ★★★ **`ρ` 直用版**：箱体先验下 `hint` 可积 —— 即 `CASTERRateAE` 文件头
（第 63–66 行）所说的「需要叶长有界先验的 `hint`」**在该先验下被证掉**。 -/
theorem abarHint_integrable_of_boxParam (M : SiteRateModel)
    {ρ : Measure ((Fin 4 → ℝ) × ℝ≥0 × ℝ≥0)} [IsProbabilityMeasure ρ]
    {lmax lx0 : ℝ} (hlx0 : 0 ≤ lx0) (hρ : ∀ᵐ p ∂ρ, p ∈ BoxParam lmax lx0) (T : Topo) :
    Integrable (fun θ : KingmanΘ =>
      ∑ T' : Topo, kingmanMSCTopoSym.τd θ T' * M.abarPropAData.A θ T' T)
      (kingmanMSCMeasure ρ) :=
  abarHint_integrable_of_box M hlx0 (ae_boxTheta_of_ae_boxParam hρ) T

/-- ★★ **箱体先验下的 `hlx`**（`¬deep` 时内部枝长正）：由 `0 < lx⁻ ≤ θ.1.2` 直接得。 -/
theorem hlx_of_boxTheta {ν : Measure KingmanΘ} {lmax lx0 : ℝ} (hlx0 : 0 < lx0)
    (hbox : ∀ᵐ θ ∂ν, θ ∈ BoxTheta lmax lx0) :
    ∀ᵐ θ ∂ν, ¬ kingmanMSCTopoSym.deep θ → 0 < Prod.snd (Prod.fst θ) := by
  filter_upwards [hbox] with θ hθ _
  have hb : (∀ i : Fin 4, 0 ≤ Prod.fst (Prod.fst θ) i ∧ Prod.fst (Prod.fst θ) i ≤ lmax)
      ∧ lx0 ≤ Prod.snd (Prod.fst θ) := hθ
  exact lt_of_lt_of_le hlx0 hb.2

/-- ★★★ **箱体先验 ⇒ `hpos`**：`0 < lx⁻` 时 `0 < ν {θ | ¬ deep θ}`
（⇒ `abarTopoIdeal` 的 `hpos` 在箱体先验下**也是定理**，不再是参数）。

逐点内容：`ν(¬deep) = ∫⁻_ρ (1 − e^{−(a+b)}) dρ`，而 `1 − e^{−(a+b)}` 对 `a + b` **单调递增**
⇒ 箱体的**正下界** `a + b ≥ lx⁻ > 0` 就给出一致正下界
（`a ≥ lx⁻/2` 或 `b ≥ lx⁻/2`，对应侧的单枝不合并概率 `≥ 1 − e^{−lx⁻/2}`）。

★ **注意方向**（本文件先前的口径在这里被更正）：需要的不是 `a + b` 的**上**界
（`a+b → ∞` 只会让 `1 − e^{−(a+b)} → 1`），而是**下**界 —— 箱体恰好给的就是下界。 -/
theorem kingmanMSCMeasure_notDeep_pos_of_boxParam
    {ρ : Measure ((Fin 4 → ℝ) × ℝ≥0 × ℝ≥0)} [IsProbabilityMeasure ρ]
    {lmax lx0 : ℝ} (hlx0 : 0 < lx0) (hbox : ∀ᵐ p ∂ρ, p ∈ BoxParam lmax lx0) :
    0 < kingmanMSCMeasure ρ DeepSetᶜ := by
  haveI : IsProbabilityMeasure (sojournLaw 2) := isProbabilityMeasure_sojournLaw (by norm_num)
  rw [kingmanMSCMeasure_notDeep ρ]
  set c : ℝ≥0∞ := ENNReal.ofReal (1 - Real.exp (-(lx0 / 2))) with hcdef
  have hcpos : 0 < c := by
    rw [hcdef, ENNReal.ofReal_pos]
    have h : Real.exp (-(lx0 / 2)) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    linarith
  have hpt : ∀ u : (Fin 4 → ℝ) × ℝ≥0 × ℝ≥0, u ∈ BoxParam lmax lx0 →
      c ≤ ((sojournLaw 2).prod (sojournLaw 2))
        {v : ℝ × ℝ | ¬ ((u.2.1 : ℝ) < v.1 ∧ (u.2.2 : ℝ) < v.2)} := by
    intro u hu
    have hu' : (∀ i : Fin 4, 0 ≤ u.1 i ∧ u.1 i ≤ lmax)
        ∧ lx0 ≤ (u.2.1 : ℝ) + (u.2.2 : ℝ) := hu
    have hsub1 : Set.Iic (u.2.1 : ℝ) ×ˢ (Set.univ : Set ℝ)
        ⊆ {v : ℝ × ℝ | ¬ ((u.2.1 : ℝ) < v.1 ∧ (u.2.2 : ℝ) < v.2)} := by
      rintro ⟨y1, y2⟩ ⟨hy1, -⟩
      simp only [Set.mem_ofPred_eq, Set.mem_Iic] at hy1 ⊢
      exact fun h => absurd h.1 (not_lt.mpr hy1)
    have hsub2 : (Set.univ : Set ℝ) ×ˢ Set.Iic (u.2.2 : ℝ)
        ⊆ {v : ℝ × ℝ | ¬ ((u.2.1 : ℝ) < v.1 ∧ (u.2.2 : ℝ) < v.2)} := by
      rintro ⟨y1, y2⟩ ⟨-, hy2⟩
      simp only [Set.mem_ofPred_eq, Set.mem_Iic] at hy2 ⊢
      exact fun h => absurd h.2 (not_lt.mpr hy2)
    have hval1 : ((sojournLaw 2).prod (sojournLaw 2))
        (Set.Iic (u.2.1 : ℝ) ×ˢ (Set.univ : Set ℝ))
        = ENNReal.ofReal (1 - Real.exp (-(u.2.1 : ℝ))) := by
      rw [Measure.prod_prod, measure_univ, mul_one,
        sojournLaw_Iic (show 2 ≤ 2 by norm_num) (u.2.1 : ℝ) (by positivity),
        Coalescent.firstMergeCDF_two]
    have hval2 : ((sojournLaw 2).prod (sojournLaw 2))
        ((Set.univ : Set ℝ) ×ˢ Set.Iic (u.2.2 : ℝ))
        = ENNReal.ofReal (1 - Real.exp (-(u.2.2 : ℝ))) := by
      rw [Measure.prod_prod, measure_univ, one_mul,
        sojournLaw_Iic (show 2 ≤ 2 by norm_num) (u.2.2 : ℝ) (by positivity),
        Coalescent.firstMergeCDF_two]
    by_cases ha : lx0 / 2 ≤ (u.2.1 : ℝ)
    · refine le_trans ?_ (measure_mono hsub1)
      rw [hval1, hcdef]
      refine ENNReal.ofReal_le_ofReal ?_
      have h : Real.exp (-(u.2.1 : ℝ)) ≤ Real.exp (-(lx0 / 2)) := Real.exp_le_exp.mpr (by linarith)
      linarith
    · have hb : lx0 / 2 ≤ (u.2.2 : ℝ) := by
        have h1 : (u.2.1 : ℝ) < lx0 / 2 := not_le.mp ha
        linarith [hu'.2]
      refine le_trans ?_ (measure_mono hsub2)
      rw [hval2, hcdef]
      refine ENNReal.ofReal_le_ofReal ?_
      have h : Real.exp (-(u.2.2 : ℝ)) ≤ Real.exp (-(lx0 / 2)) := Real.exp_le_exp.mpr (by linarith)
      linarith
  have hmono : ∫⁻ u, (BoxParam lmax lx0).indicator (fun _ => c) u ∂ρ
      ≤ ∫⁻ u, ((sojournLaw 2).prod (sojournLaw 2))
          {v : ℝ × ℝ | ¬ ((u.2.1 : ℝ) < v.1 ∧ (u.2.2 : ℝ) < v.2)} ∂ρ := by
    refine lintegral_mono_ae ?_
    filter_upwards [hbox] with u hu
    rw [Set.indicator_of_mem hu]
    exact hpt u hu
  have hval : ∫⁻ u, (BoxParam lmax lx0).indicator (fun _ => c) u ∂ρ = c := by
    rw [lintegral_indicator_const (measurableSet_boxParam lmax lx0) c,
      (measure_boxParam_eq_one_iff (ρ := ρ)).mpr hbox, mul_one]
  have key : (0 : ℝ≥0∞) < ∫⁻ u, (BoxParam lmax lx0).indicator (fun _ => c) u ∂ρ := by
    rw [hval]
    exact hcpos
  exact lt_of_lt_of_le key hmono

/-! ## 5. ★★★ 一般 `ρ` 上的 `TopoIdeal`（箱体先验版） -/

/-- ★★★ **箱体先验下的 `TopoIdeal`（一般 `ρ`，不再要求 Dirac）**。

与 `CASTERRateAE.abarTopoIdeal` 的**唯一**差别：本定义把 `hf_int` / `hint` / `hlx` / `hpos`
**全部从参数里去掉** —— 它们都由 §3 / §4 的定理在箱体先验下供给。

剩下的参数：`ρ`（概率测度）、箱体先验 `hbox`、内枝长正下界 `0 < lx⁻`。
（★ `hpos` 由 `kingmanMSCMeasure_notDeep_pos_of_boxParam` 在**内部**供给：
`1 − e^{−(a+b)}` 对 `a + b` 单调递增，故箱体的**下**界 `a + b ≥ lx⁻ > 0` 正是所需。） -/
noncomputable def abarTopoIdealBox (M : SiteRateModel)
    (ρ : Measure ((Fin 4 → ℝ) × ℝ≥0 × ℝ≥0)) [IsProbabilityMeasure ρ]
    {lmax lx0 : ℝ} (hlx0 : 0 < lx0) (hbox : ∀ᵐ p ∂ρ, p ∈ BoxParam lmax lx0) : TopoIdeal (Fin 4) :=
  abarTopoIdeal (X := Fin 4) M kingmanMSCTopoSym (kingmanMSCMeasure ρ)
    measurableSet_kingmanMSCTopoSym_deep
    (hlx_of_boxTheta hlx0 (ae_boxTheta_of_ae_boxParam hbox))
    (fbar_integrable_of_boxParam M hlx0.le hbox)
    (kingmanMSCMeasure_notDeep_pos_of_boxParam hlx0 hbox)
    (fun T => abarHint_integrable_of_boxParam M hlx0.le hbox T)

/-- ★★ **`abarTopoIdealBox` 的 `W` 逐字展开**：
`W = fun _ _ T => expWeight (kingmanMSCMeasure ρ) kingmanMSCTopoSym.τd Ã T`
—— 与 `abarTopoIdeal_kingman_W` 同形，只是 `ν` 从 Dirac 换成了 `kingmanMSCMeasure ρ`。 -/
theorem abarTopoIdealBox_W (M : SiteRateModel)
    (ρ : Measure ((Fin 4 → ℝ) × ℝ≥0 × ℝ≥0)) [IsProbabilityMeasure ρ]
    {lmax lx0 : ℝ} (hlx0 : 0 < lx0) (hbox : ∀ᵐ p ∂ρ, p ∈ BoxParam lmax lx0) :
    (abarTopoIdealBox M ρ hlx0 hbox).W
      = fun _ _ T => expWeight (kingmanMSCMeasure ρ) kingmanMSCTopoSym.τd M.Abar T := rfl

/-- ★★ **`propB` 逐字取出**：真拓扑 `ab|cd` 在每个 4-元集上严格最大。 -/
theorem abarTopoIdealBox_propB (M : SiteRateModel)
    (ρ : Measure ((Fin 4 → ℝ) × ℝ≥0 × ℝ≥0)) [IsProbabilityMeasure ρ]
    {lmax lx0 : ℝ} (hlx0 : 0 < lx0) (hbox : ∀ᵐ p ∂ρ, p ∈ BoxParam lmax lx0)
    (S₀ : Finset (Fin 4)) (hS₀ : S₀.card = 4) (T : Topo) (hT : T ≠ Topo.ab_cd) :
    (abarTopoIdealBox M ρ hlx0 hbox).W S₀ hS₀ T
      < (abarTopoIdealBox M ρ hlx0 hbox).W S₀ hS₀ Topo.ab_cd :=
  (abarTopoIdealBox M ρ hlx0 hbox).propB S₀ hS₀ T hT

/-! ## 6. ★★★ 端到端：一般 `ρ` 的 a.e. 统计一致性 -/

/-- ★★★ **端到端 a.e. 统计一致性（一般物种树测度 `ρ` ＋ 箱体先验）**。

与 `CASTERRateAE.abar_caster_statisticallyConsistent_kingman_ae` **同形**，
唯一区别是**假设面**：

| | 既有端点（`…_kingman_ae`） | 本定理 |
|---|---|---|
| 物种树 | `Measure.dirac (leaf, a, b)` ＋ `0 < a + b` | **一般概率测度 `ρ`** |
| 叶长 | 无额外条件 | **箱体先验** `∀ᵐ p ∂ρ, p ∈ BoxParam lmax lx⁻` |
| 内枝长 | 由 `a + b > 0` 自动 | `0 < lx⁻ ≤ a + b`（箱体的一部分） |
| `hpos` | 定理（`dirac_notDeep_pos`） | **定理**（`kingmanMSCMeasure_notDeep_pos_of_boxParam`） |
| `hf_int` / `hint` / `hlx` | 定理（`CASTERRateAE` §5） | 定理（本文件 §3/§4） |
| `hconv` / `hE` | 假设 | 假设（同形） |

★ 这是**新增**声明，**不改**任何既有定理（★C）。 -/
theorem abar_caster_statisticallyConsistent_kingman_ae_box {Ω : Type*} [MeasurableSpace Ω]
    (M : SiteRateModel) (ρ : Measure ((Fin 4 → ℝ) × ℝ≥0 × ℝ≥0)) [IsProbabilityMeasure ρ]
    {lmax lx0 : ℝ} (hlx0 : 0 < lx0) (hbox : ∀ᵐ p ∂ρ, p ∈ BoxParam lmax lx0)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (emp : ℕ → Ω → TopoWeight (Fin 4))
    (hconv : ∀ᵐ ω ∂μ, ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N,
      TopoClose (emp n ω) (abarTopoIdealBox M ρ hlx0 hbox).W ε)
    {E : ℕ → Ω → TopoChoice (Fin 4)}
    (hE : ∀ᵐ ω ∂μ, ∀ (n : ℕ) (q : TopoChoice (Fin 4)),
      topoScore (emp n ω) q ≤ topoScore (emp n ω) (E n ω)) :
    ∀ᵐ ω ∂μ, ∃ N : ℕ, ∀ n ≥ N, IsTrueT (fun _ _ => Topo.ab_cd) (E n ω) :=
  topo_statisticallyConsistent_ae (abarTopoIdealBox M ρ hlx0 hbox) μ emp hconv
    exists_not_true_topoChoice_fin4 hE

/-! ## 7. ★★★ 退化一致性：Dirac 是箱体先验的特例（**最强探针**） -/

/-- ★★★ **Dirac 满足箱体先验**：取 `lmax = ∑_i leaf i`（叶长非负时它 ≥ 每个叶长）、
`lx⁻ = a + b`。 -/
theorem boxParam_dirac_ae (leaf : Fin 4 → ℝ) (hleaf : ∀ i, 0 ≤ leaf i) (a b : ℝ≥0) :
    ∀ᵐ p ∂(Measure.dirac (leaf, a, b)),
      p ∈ BoxParam (∑ i : Fin 4, leaf i) ((a : ℝ) + (b : ℝ)) :=
  (MeasureTheory.ae_dirac_iff (measurableSet_boxParam _ _)).mpr
    ⟨fun i => ⟨hleaf i,
        Finset.single_le_sum (fun j _ => hleaf j) (Finset.mem_univ i)⟩, le_rfl⟩

/-- ★★★ **退化一致性（★最强探针）**：`ρ = Measure.dirac (leaf, a, b)`（**确定物种树**）
时，本文件新造的 `abarTopoIdealBox` 的权重表 `W` **逐字等于**库内旗舰端点
`CASTERRateAE.abarTopoIdeal_kingman` 的 `W`。

即：一般 `ρ` 的新结论在 Dirac 上**退回**既有结果（与 W13 端到端主定理同一张表）。 -/
theorem abarTopoIdealBox_dirac_W (M : SiteRateModel) (leaf : Fin 4 → ℝ)
    (hleaf : ∀ i, 0 ≤ leaf i) (a b : ℝ≥0) (hab : 0 < (a : ℝ) + (b : ℝ)) :
    (abarTopoIdealBox M (Measure.dirac (leaf, a, b)) hab
        (boxParam_dirac_ae leaf hleaf a b)).W
      = (abarTopoIdeal_kingman M leaf a b hab).W := rfl

/-- ★★ **退化一致性的具体推论**：Dirac 情形下，本文件的 `TopoIdeal` 在 `S₀` 上的
权重表与库内旗舰端点**逐点相同**（把 `W` 的相等取出到一个点上）。 -/
theorem abarTopoIdealBox_dirac_W_apply (M : SiteRateModel) (leaf : Fin 4 → ℝ)
    (hleaf : ∀ i, 0 ≤ leaf i) (a b : ℝ≥0) (hab : 0 < (a : ℝ) + (b : ℝ))
    (S₀ : Finset (Fin 4)) (hS₀ : S₀.card = 4) (T : Topo) :
    (abarTopoIdealBox M (Measure.dirac (leaf, a, b)) hab
        (boxParam_dirac_ae leaf hleaf a b)).W S₀ hS₀ T
      = (abarTopoIdeal_kingman M leaf a b hab).W S₀ hS₀ T := by
  rw [abarTopoIdealBox_dirac_W M leaf hleaf a b hab]

/-- ★★★ **本文件的箱体路线**逐字**包含 Dirac 路线**（机器验证的"严格更一般"）：
把 `abar_caster_statisticallyConsistent_kingman_ae_box` 用在 `ρ = Measure.dirac (leaf, a, b)` 上，
配合 `abarTopoIdealBox_dirac_W`（`rfl`），得到**与库内 Dirac 端点
`CASTERRateAE.abar_caster_statisticallyConsistent_kingman_ae` 完全相同的陈述**
（同一 `hconv` 目标 `(abarTopoIdeal_kingman M leaf a b hab).W`、同一结论）。

⇒ 这证明：Dirac 端点是本文件一般 `ρ` 版本的一个**特例**（不是两条互不相干的路线）。 -/
theorem abar_caster_statisticallyConsistent_kingman_ae_via_box_dirac {Ω : Type*}
    [MeasurableSpace Ω]
    (M : SiteRateModel) (leaf : Fin 4 → ℝ) (hleaf : ∀ i, 0 ≤ leaf i) (a b : ℝ≥0)
    (hab : 0 < (a : ℝ) + (b : ℝ))
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (emp : ℕ → Ω → TopoWeight (Fin 4))
    (hconv : ∀ᵐ ω ∂μ, ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N,
      TopoClose (emp n ω) (abarTopoIdeal_kingman M leaf a b hab).W ε)
    {E : ℕ → Ω → TopoChoice (Fin 4)}
    (hE : ∀ᵐ ω ∂μ, ∀ (n : ℕ) (q : TopoChoice (Fin 4)),
      topoScore (emp n ω) q ≤ topoScore (emp n ω) (E n ω)) :
    ∀ᵐ ω ∂μ, ∃ N : ℕ, ∀ n ≥ N, IsTrueT (fun _ _ => Topo.ab_cd) (E n ω) :=
  abar_caster_statisticallyConsistent_kingman_ae_box M (Measure.dirac (leaf, a, b)) hab
    (boxParam_dirac_ae leaf hleaf a b) μ emp (by
      filter_upwards [hconv] with ω hω ε hε
      exact hω ε hε) hE

/-! ## 8. ★ 反空洞：箱体先验有**概率测度**居民（不是空真） -/

/-- ★★★ **反空洞（第一件）**：只要 `0 ≤ lmax`、`0 < lx⁻`，就**存在概率测度** `ρ`
使得箱体先验 `∀ᵐ p ∂ρ, p ∈ BoxParam lmax lx⁻` 成立
（取 `ρ = Measure.dirac ((fun _ => 0), ⟨lx⁻, _⟩, 0)`）。

⇒ 本文件的主定理**不是空真**：其假设面在上述参数下有真居民。 -/
theorem exists_probabilityMeasure_boxParam {lmax lx0 : ℝ} (hlmax : 0 ≤ lmax) (hlx0 : 0 < lx0) :
    ∃ ρ : Measure ((Fin 4 → ℝ) × ℝ≥0 × ℝ≥0), IsProbabilityMeasure ρ ∧
      ∀ᵐ p ∂ρ, p ∈ BoxParam lmax lx0 := by
  have hpt : ((fun _ : Fin 4 => (0 : ℝ)), ⟨lx0, hlx0.le⟩, (0 : ℝ≥0)) ∈ BoxParam lmax lx0 := by
    refine ⟨fun _ => ⟨le_rfl, hlmax⟩, ?_⟩
    show lx0 ≤ ((⟨lx0, hlx0.le⟩ : ℝ≥0) : ℝ) + ((0 : ℝ≥0) : ℝ)
    have h1 : ((⟨lx0, hlx0.le⟩ : ℝ≥0) : ℝ) = lx0 := rfl
    have h2 : ((0 : ℝ≥0) : ℝ) = 0 := rfl
    linarith
  exact ⟨Measure.dirac ((fun _ : Fin 4 => (0 : ℝ)), ⟨lx0, hlx0.le⟩, (0 : ℝ≥0)), inferInstance,
    (MeasureTheory.ae_dirac_iff (p := fun p => p ∈ BoxParam lmax lx0)
      (measurableSet_boxParam lmax lx0)).mpr hpt⟩

/-- ★★★ **反空洞（第二件）**：同样参数下存在**概率测度** `ν` 在 `KingmanΘ` 上
使 `BoxTheta` 先验成立（即 §3 的可积性定理有真前件）。 -/
theorem exists_probabilityMeasure_boxTheta {lmax lx0 : ℝ} (hlmax : 0 ≤ lmax)
    (hlx0 : 0 < lx0) :
    ∃ ν : Measure KingmanΘ, IsProbabilityMeasure ν ∧ ∀ᵐ θ ∂ν, θ ∈ BoxTheta lmax lx0 := by
  obtain ⟨ρ, hρ, hbox⟩ := exists_probabilityMeasure_boxParam (lmax := lmax) (lx0 := lx0) hlmax hlx0
  exact ⟨kingmanMSCMeasure ρ, inferInstance, ae_boxTheta_of_ae_boxParam hbox⟩

end Phylo.Stat.CASTERRateBoxAE

end
