/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.Stat.Coalescent
import Mathlib.Probability.Distributions.Exponential
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Probability.Independence.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup

/-!
# `Phylo.Stat.KingmanCoalescent` —— Kingman 1982 逗留时间律 (1.7) 与 Theorem 1

本文件把 Kingman (1982) *The Coalescent*（Stochastic Processes and their Applications **13**
235–248，下称 **K82**）的**测度论**内容形式化：

* **(1.7)**（K82 第 **129–137** 行）：`|ξ| = k` 的状态逗留时间 `τ_k` 的概率密度为
  `d_k e^{−d_k t}`（`t > 0`），`d_k = ½k(k−1)`；即 `τ_k ~ Exp(d_k)`。
* **Theorem 1**（K82 第 **210–215** 行）："In an n-coalescent, the death process `(D_t ; t ≥ 0)`
  and the jump chain `(S_k ; k = n, n−1, …, 1)` are **independent**, and `R_t = S_{D_t}` for all
  `t ≥ 0`."
* **(1.11)**（K82 第 **174–195** 行）：`T = Σ_{k=2}^n τ_k`，`τ_k` **相互独立**，各自服从 (1.7)。
  K82 第 **252–256** 行给出机制：「conditioned on the jump chain the sojourn times are independent,
  the sojourn time in a state `ξ` having probability density `q_ξ e^{−q_ξ t}`」，而溯祖里
  `q_ξ = d_k`（只依赖块数）⇒「条件分布 = 无条件分布」⇒ 独立。

## 本文件新增的 Mathlib import（对既有 import 闭包是**新增**的四处）

    import Mathlib.Probability.Distributions.Exponential          -- expMeasure / cdf_expMeasure_eq
    import Mathlib.MeasureTheory.Integral.Pi                      -- integral_eval / integrable_eval
    import Mathlib.Probability.Independence.Basic                 -- IndepFun / indepFun_prod
    import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup   -- 仅为 Gamma_two : Gamma 2 = 1

⚠️ 第四处**只是**为了 `Gamma_two`（从 `Phylo.Stat.Coalescent` 的闭包拿不到）。
积分核 `integral_rpow_mul_exp_neg_mul_Ioi` 本来就在既有闭包内
（`Mathlib/Analysis/SpecialFunctions/Gamma/Basic.lean:465`）。

## 与 W10a（跳链）的解耦

W10a（`Phylo/Stat/KingmanJumpChain.lean`）由**另一个 agent 并行**实现。本文件因此**不 import**
它：Theorem 1 的联合律写成**对任意跳链测度 `μ` 都成立**的参数形式

    nCoalescentLaw μ n = μ.prod (sojournJointLaw n)

协调侧之后把 `μ` 实例化成跳链 PMF（`jumpPMF n n` 的 `toMeasure`）即可接上。

## ★ 措辞纪律（Theorem 1 到底证明了什么）

`sojournJointLaw n` 就是 **`Measure.pi`（= 独立指数律的乘积）**，`nCoalescentLaw μ n` 就是
**乘积测度** `μ.prod (sojournJointLaw n)`。本文件对独立性的证明走 Mathlib 的
`indepFun_prod`；它要求**两个因子都是概率测度**，因此本文件的

    theorem indepFun_fst_snd_nCoalescent (μ : Measure Ω) [IsProbabilityMeasure μ]
        (n : ℕ) (hn : 2 ≤ n) : IndepFun Prod.fst Prod.snd (nCoalescentLaw μ n)

是**真·`IndepFun`**（`⟂ᵢ`，即 `∀ s t 可测, μ (f⁻¹s ∩ g⁻¹t) = μ (f⁻¹s) * μ (g⁻¹t)`），
**不是**「联合律 = 乘积测度」的代用语；并且**另外**证明了两个边缘恒等式
`(nCoalescentLaw μ n).fst = μ` 与 `(nCoalescentLaw μ n).snd = sojournJointLaw n`。
**两件事都做了。** 唯一需要 `[IsProbabilityMeasure μ]` 的原因是 Mathlib 那条
`indepFun_prod` 的假设，**不是**数学内容上的额外要求。

## ★ 方向与参数域的两条纪律

1. **方向**：`P(τ_k > t) = e^{−d_k t}`（生存函数，`Coalescent.survival`）而**不是**
   `1 − e^{−d_k t}`（那是 `Coalescent.firstMergeCDF`）。
2. **参数域**：K82 (1.7) 的密度只在 `t > 0` 上给出，逗留时间 `τ_k ≥ 0` 几乎必然。
   因此 `sojournLaw_Ioi` 只对 **`0 ≤ t`** 断言 `= ofReal (Coalescent.survival k t)`；
   对 `t < 0` 正确的值是 `1`（`sojournLaw_Ioi_of_neg`）。
   ⚠️ 这不是在弱化结论，而是**必须的**：`Coalescent.survival k t = e^{−d_k t}` 在 `t < 0` 时
   `> 1`（如 `k = 2, t = −1` 时 `e ≈ 2.718`），**不可能**等于概率。
   库内 `Phylo/Stat/Coalescent.lean` 的既有声明**未改动**，本文件只是在文档里指出
   `survival` 的可用域是 `t ≥ 0`。

## 诚实边界（逐条）

| 条目 | 状态 |
|---|---|
| K82 (1.7) `τ_k ~ Exp(d_k)`（密度 `d_k e^{−d_k t}`） | **已形式化**（`sojournLaw`） |
| K82 (1.7) 与库内 `Coalescent.survival` 的接合 `P(τ_k > t) = e^{−d_k t}`（`0 ≤ t`） | **已证**（`sojournLaw_Ioi`） |
| K82 (1.7) 的分布函数层 `P(τ_k ≤ t) = 1 − e^{−d_k t}` = `Coalescent.firstMergeCDF` | **已证**（`sojournLaw_Iic`） |
| `E[τ_k] = 1/d_k`（K82 第 **184–193** 行） | **已证**（`integral_id_sojournLaw`，从 `withDensity` 定义硬算） |
| K82 (1.11) `τ_k` **相互独立**、联合律 = 独立指数之积 | **已形式化**（`sojournJointLaw = Measure.pi`；`isProbabilityMeasure_sojournJointLaw`） |
| K82 Theorem 1 的**联合律形式**（跳链 ⊥ 逗留时间） | **已证**（`nCoalescentLaw` / `indepFun_fst_snd_nCoalescent` / 两条边缘） |
| K82 (1.12) `E[T] = 2(1−1/n)` | **已证**（`integral_sum_sojournJointLaw`，经 `Coalescent.expectedTotalCoalescenceTime`） |
| `k < 2`（`d_k = 0`）的退化情形 | **已证**（`expMeasure_eq_zero_of_nonpos` / `sojournLaw_zero_of_lt_two`） |
| K82 Theorem 1 的 `R_t = S_{D_t}` 那半条 | ❌ **未形式化** |
| K82 第 **259–266** 行的证明路线「条件分布 = 无条件分布 ⇒ 独立」 | ❌ **未形式化** |
| 「跳链概率测度 `μ` 的存在性与它是 `jumpPMF`」 | ❌ **不在本文件**（W10a 的交付物） |

### 未做的两条（明确报告，不硬做）

1. **`R_t = S_{D_t}` 与 `(D_t)` 的路径构造没有形式化。** 需要「纯死亡过程」
   （时间指标、可数状态、吸收态的 `Measure` 层过程）与跳链的联合路径空间；
   Mathlib 没有这样的现成器材，本库也没有。本文件交付的 Theorem 1 是它的**定律层**
   内容（「联合律 = 边缘之积」），这是现有器材能证出来的全部。
2. **「条件分布 = 无条件分布 ⇒ 独立」没有形式化。** 本文件把 `μ.prod ν` 当作独立性的
   **载体**（这正是 Theorem 1 的内容），而没有从 `q_ξ e^{−q_ξ t}` 的条件密度出发
   去**推导**它 —— 那需要先有 `(D_t)`，同上。

### 两条接口说明（不是缺口，是选择）

* `sojournLaw_Ioi` / `sojournLaw_Iic` 带 **`2 ≤ k`** 假设，`k < 2` 的退化情形另立
  `sojournLaw_zero_of_lt_two`（那时 `d_k = 0`，`sojournLaw k` 是**零测度**，
  `Ioi t` 与 `Iic t` 的测度都是 `0`）。这样主定理的假设就是**数学上必需**的那一条。
* `isProbabilityMeasure_sojournJointLaw` / `integral_eval_sojournJointLaw` /
  `integrable_eval_sojournJointLaw` 保留 `2 ≤ n` 参数但**证明里用不到**它
  （`n < 2` 时 `Fin (n - 1)` 是空类型，`Measure.pi` 的概率性空洞成立）：
  保留是为了**接口稳定**，参数名写成 `_hn` 以免触发 unused-variable 告警。

### 一条技术说明

`integral_id_expMeasure` 把 `expMeasure r = volume.withDensity (gammaPDF 1 r)` **展开**后硬算
（`integral_withDensity_eq_integral_toReal_smul` ＋ `Gamma.Basic` 的
`integral_rpow_mul_exp_neg_mul_Ioi`），没有跳过任何一步。
`expMeasure_Iic_eq` 走 `withDensity_apply` ＋ `lintegral_exponentialPDF_eq_antiDeriv`
（`Exponential.lean:118`），**不经过 `cdf` 的 `StieltjesFunction` 强制转换**
（那条路在本 Mathlib 版本上与 `Measure` 的强制转换不接）。
`expMeasure_eq_zero_of_nonpos` 的要点是：`r < 0` 时密度 `r e^{−rt}` 在 `[0, ∞)` 上**为负**，
`ENNReal.ofReal` 把它压成 `0`。
**本文件零 `sorry`、零 `axiom`**（`#print axioms` 只列 `propext, Classical.choice, Quot.sound`）。
-/

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal

-- `haveI` 在本文件里是**必需的**：`Measure.pi` / `Measure.prod` / `measure_univ`
-- 都要从"因子是概率测度"这个**实例**里取。库内已有先例
-- （`Phylo/PhylogramContract.lean:854`、`Phylo/SplitsDetermineTree.lean:58`）。
set_option linter.style.haveILetI false

namespace Phylo.Stat.KingmanCoalescent

/-! ## 0. 指数分布的器材（薄封装） -/

/-- `expMeasure r (Iic t)` 就是密度 `r e^{−rt}` 在 `(−∞, t]` 上的积分。

（`expMeasure r = volume.withDensity (gammaPDF 1 r)` 而 `gammaPDF 1 r = exponentialPDF r`。） -/
theorem expMeasure_Iic {r : ℝ} (t : ℝ) :
    ProbabilityTheory.expMeasure r (Set.Iic t)
      = ∫⁻ y in Set.Iic t, ProbabilityTheory.exponentialPDF r y := by
  rw [ProbabilityTheory.expMeasure, ProbabilityTheory.gammaMeasure,
    withDensity_apply _ measurableSet_Iic]
  refine setLIntegral_congr_fun measurableSet_Iic (fun y _ => ?_)
  rw [ProbabilityTheory.exponentialPDF_eq, ProbabilityTheory.gammaPDF_eq, Real.rpow_one]
  norm_num

/-- `expMeasure r (Iic t)` 的显式值：`t ≥ 0` 时 `1 − e^{−rt}`，`t < 0` 时 `0`。

只用 `withDensity_apply` ＋ `lintegral_exponentialPDF_eq_antiDeriv`
（`Exponential.lean:118`），**不经过 `cdf` 的 `StieltjesFunction` 强制转换**
（那条路在本 Mathlib 版本上与 `Measure` 的强制转换不接）。 -/
theorem expMeasure_Iic_eq {r : ℝ} (hr : 0 < r) (t : ℝ) :
    ProbabilityTheory.expMeasure r (Set.Iic t)
      = if 0 ≤ t then 1 - ENNReal.ofReal (Real.exp (-(r * t))) else 0 := by
  rw [expMeasure_Iic, ProbabilityTheory.lintegral_exponentialPDF_eq_antiDeriv hr t]
  by_cases h : 0 ≤ t
  · rw [ite_eq_left h, ite_eq_left h, ENNReal.ofReal_sub _ (Real.exp_pos _).le,
      ENNReal.ofReal_one]
  · rw [ite_eq_right h, ite_eq_right h, ENNReal.ofReal_zero]

/-- `r ≤ 0` 时 `expMeasure r` 是零测度（`k < 2` 时 `d_k = 0` 的退化情形）。

关键：`r < 0` 时密度 `r e^{−rt}` 在 `[0, ∞)` 上**为负**，故 `ENNReal.ofReal` 把它压成 `0`。 -/
theorem expMeasure_eq_zero_of_nonpos {r : ℝ} (hr : r ≤ 0) :
    ProbabilityTheory.expMeasure r = 0 := by
  have hpdf : ProbabilityTheory.gammaPDF 1 r = 0 := by
    funext x
    rw [ProbabilityTheory.gammaPDF_eq]
    split_ifs with hx
    · rw [Real.rpow_one, Gamma_one, div_one, show ((1:ℝ) - 1) = 0 from by norm_num,
        Real.rpow_zero, mul_one]
      exact ENNReal.ofReal_eq_zero.mpr (mul_nonpos_of_nonpos_of_nonneg hr (Real.exp_pos _).le)
    · exact ENNReal.ofReal_zero
  rw [ProbabilityTheory.expMeasure, ProbabilityTheory.gammaMeasure, hpdf, withDensity_zero]

/-- ★ **`expMeasure r (Ioi t) = ofReal (e^{−rt})`**（`r > 0`，**`0 ≤ t`**）。

⚠️ **`0 ≤ t` 是必需的**：`t < 0` 时指数律集中在 `[0, ∞)`，故 `(t, ∞)` 的测度是 `1`，
而 `ofReal (e^{−rt}) = ofReal (e^{r|t|}) > 1`（如 `r = 1, t = −1` 时 `e ≈ 2.718`）
—— 两者**不可能**相等。这正是 `Coalescent.survival` 只在 `t ≥ 0` 上可当概率用的原因。 -/
theorem expMeasure_Ioi_of_pos {r : ℝ} (hr : 0 < r) (t : ℝ) (ht : 0 ≤ t) :
    ProbabilityTheory.expMeasure r (Set.Ioi t) = ENNReal.ofReal (Real.exp (-(r * t))) := by
  haveI : IsProbabilityMeasure (ProbabilityTheory.expMeasure r) :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure hr
  have hsplit : ProbabilityTheory.expMeasure r (Set.Iic t)
      + ProbabilityTheory.expMeasure r (Set.Ioi t) = 1 := by
    rw [← measure_union (Set.Iic_disjoint_Ioi le_rfl) measurableSet_Ioi, Set.Iic_union_Ioi]
    exact measure_univ
  have hc : ProbabilityTheory.expMeasure r (Set.Iic t)
      = 1 - ENNReal.ofReal (Real.exp (-(r * t))) := by
    rw [expMeasure_Iic_eq hr t, ite_eq_left ht]
  have hle : ENNReal.ofReal (Real.exp (-(r * t))) ≤ 1 :=
    ENNReal.ofReal_le_one.mpr (by rw [Real.exp_le_one_iff]; nlinarith)
  have hne : (1 : ℝ≥0∞) - ENNReal.ofReal (Real.exp (-(r * t))) ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self
  rw [hc] at hsplit
  have hsplit' : ProbabilityTheory.expMeasure r (Set.Ioi t)
      + (1 - ENNReal.ofReal (Real.exp (-(r * t)))) = 1 := by
    rw [add_comm]; exact hsplit
  have hb : ProbabilityTheory.expMeasure r (Set.Ioi t)
      = 1 - (1 - ENNReal.ofReal (Real.exp (-(r * t)))) :=
    ENNReal.eq_sub_of_add_eq hne hsplit'
  rw [hb, ENNReal.sub_sub_cancel ENNReal.one_ne_top hle]

/-- `∫_{t>0} t · e^{−rt} dt = 1/r²`（密度层，K82 (1.7) 期望计算的核）。 -/
theorem integral_Ioi_id_exp {r : ℝ} (hr : 0 < r) :
    ∫ t in Set.Ioi 0, t * Real.exp (-(r * t)) = 1 / r ^ 2 := by
  have h2 : (0:ℝ) < 2 := by norm_num
  have hpow : ∀ t : ℝ, t ^ ((2:ℝ) - 1) = t := by
    intro t
    rw [show ((2:ℝ) - 1) = (1:ℝ) from by norm_num, Real.rpow_one]
  calc ∫ t in Set.Ioi 0, t * Real.exp (-(r * t))
      = ∫ t in Set.Ioi 0, t ^ ((2:ℝ) - 1) * Real.exp (-(r * t)) :=
        setIntegral_congr_fun measurableSet_Ioi (fun t _ => by rw [hpow t])
    _ = (1 / r) ^ (2:ℝ) * Gamma 2 := integral_rpow_mul_exp_neg_mul_Ioi h2 hr
    _ = 1 / r ^ 2 := by
        rw [show Gamma (2:ℝ) = 1 from Gamma_two, mul_one, Real.rpow_two, div_pow]
        norm_num

/-- ★ **`E[Exp(r)] = 1/r`**：`∫ x ∂(expMeasure r) = 1/r`。

从 `expMeasure r = volume.withDensity (gammaPDF 1 r)` **展开硬算**：
`integral_withDensity_eq_integral_toReal_smul` 把积分读到密度层，再用
`integral_Ioi_id_exp`。 -/
theorem integral_id_expMeasure {r : ℝ} (hr : 0 < r) :
    ∫ t, t ∂(ProbabilityTheory.expMeasure r) = 1 / r := by
  have hmeas : Measurable (ProbabilityTheory.gammaPDF 1 r) :=
    (ProbabilityTheory.measurable_gammaPDFReal 1 r).ennreal_ofReal
  have hpt : ∀ x : ℝ, (ProbabilityTheory.gammaPDF 1 r x).toReal • x
      = (if 0 ≤ x then r * x * Real.exp (-(r * x)) else 0) := by
    intro x
    rw [ProbabilityTheory.gammaPDF,
      ENNReal.toReal_ofReal (ProbabilityTheory.gammaPDFReal_nonneg zero_lt_one hr x),
      smul_eq_mul, ProbabilityTheory.gammaPDFReal]
    split_ifs with h
    · rw [show ((1:ℝ) - 1) = 0 from by norm_num, Real.rpow_zero, Gamma_one, div_one,
        Real.rpow_one]
      ring
    · exact zero_mul x
  calc ∫ t, t ∂(ProbabilityTheory.expMeasure r)
      = ∫ x, (ProbabilityTheory.gammaPDF 1 r x).toReal • x ∂(volume : Measure ℝ) := by
        rw [ProbabilityTheory.expMeasure, ProbabilityTheory.gammaMeasure]
        exact integral_withDensity_eq_integral_toReal_smul hmeas
          (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top) (fun x : ℝ => x)
    _ = ∫ x, (if 0 ≤ x then r * x * Real.exp (-(r * x)) else 0) ∂(volume : Measure ℝ) :=
        integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = ∫ x in Set.Ioi 0, (if 0 ≤ x then r * x * Real.exp (-(r * x)) else 0)
          ∂(volume : Measure ℝ) := by
        rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Set.Ioi 0)]
        intro x hx
        have hx0 : x ≤ 0 := le_of_not_gt (fun hlt => hx hlt)
        by_cases h0 : 0 ≤ x
        · rw [ite_eq_left h0]
          have hxeq : x = 0 := le_antisymm hx0 h0
          rw [hxeq]
          ring
        · rw [ite_eq_right h0]
    _ = ∫ x in Set.Ioi 0, r * x * Real.exp (-(r * x)) ∂(volume : Measure ℝ) :=
        setIntegral_congr_fun measurableSet_Ioi (fun a ha => ite_eq_left ha.le)
    _ = 1 / r := by
        rw [show (∫ x in Set.Ioi 0, r * x * Real.exp (-(r * x)))
            = r * ∫ x in Set.Ioi 0, x * Real.exp (-(r * x)) from by
          rw [← integral_const_mul]
          exact setIntegral_congr_fun measurableSet_Ioi (fun x _ => by ring)]
        rw [integral_Ioi_id_exp hr]
        field_simp

/-! ## 1. 逗留时间律 (1.7)：`τ_k ~ Exp(d_k)` -/

/-- **★ K82 (1.7)**（第 **129–137** 行）：`|ξ| = k` 的状态逗留时间 `τ_k` 的**律**是速率
`d_k = ½k(k−1)` 的指数分布（原文密度 `d_k e^{−d_k t}`，`t > 0`）。

速率用库内既有的 `Coalescent.kingmanRate`（`Phylo/Stat/Coalescent.lean:119`），
故 `k ≥ 2` 时它是概率测度（`isProbabilityMeasure_sojournLaw`）。 -/
noncomputable def sojournLaw (k : ℕ) : Measure ℝ :=
  ProbabilityTheory.expMeasure (Coalescent.kingmanRate k)

/-- `k ≥ 2` 时 `sojournLaw k` 是概率测度（(1.7) 的密度积分为 `1`）。 -/
theorem isProbabilityMeasure_sojournLaw {k : ℕ} (hk : 2 ≤ k) :
    IsProbabilityMeasure (sojournLaw k) :=
  ProbabilityTheory.isProbabilityMeasure_expMeasure (Coalescent.kingmanRate_pos hk)

/-- **★★ K82 (1.7) 的生存函数层，与库内既有设施接合**：

`2 ≤ k` 且 `0 ≤ t` 时 `sojournLaw k (Ioi t) = ofReal (Coalescent.survival k t)`，
即 `P(τ_k > t) = e^{−d_k t}`。

⚠️ **方向**：是**生存函数** `e^{−d_k t}`（`Coalescent.survival`，
`Phylo/Stat/Coalescent.lean:304`），**不是** `1 − e^{−d_k t}`（那是 `Coalescent.firstMergeCDF`）。

⚠️ **`0 ≤ t` 是必需的**（不是可以省的假设）：K82 (1.7) 的密度只在 `t > 0` 上给出；
`t < 0` 时正确的概率是 `1`（见 `sojournLaw_Ioi_of_neg`），而
`Coalescent.survival k t = e^{−d_k t} > 1`，**不可能**等于概率。 -/
theorem sojournLaw_Ioi {k : ℕ} (hk : 2 ≤ k) (t : ℝ) (ht : 0 ≤ t) :
    sojournLaw k (Set.Ioi t) = ENNReal.ofReal (Coalescent.survival k t) := by
  rw [sojournLaw, expMeasure_Ioi_of_pos (Coalescent.kingmanRate_pos hk) t ht, Coalescent.survival,
    ← neg_mul]

/-- `k < 2`（即 `k = 0` 或 `k = 1`，`d_k = 0`）时的退化情形：`sojournLaw k` 是零测度，
故 `Ioi t` 与 `Iic t` 的测度都是 `0`。 -/
theorem sojournLaw_zero_of_lt_two {k : ℕ} (hk : ¬ 2 ≤ k) (t : ℝ) :
    sojournLaw k (Set.Ioi t) = 0 ∧ sojournLaw k (Set.Iic t) = 0 := by
  have hk1 : k = 0 ∨ k = 1 := by omega
  rcases hk1 with hk0 | hk1
  · subst hk0
    exact ⟨by rw [sojournLaw, Coalescent.kingmanRate_zero,
        expMeasure_eq_zero_of_nonpos le_rfl]; rfl,
      by rw [sojournLaw, Coalescent.kingmanRate_zero,
        expMeasure_eq_zero_of_nonpos le_rfl]; rfl⟩
  · subst hk1
    exact ⟨by rw [sojournLaw, Coalescent.kingmanRate_one,
        expMeasure_eq_zero_of_nonpos le_rfl]; rfl,
      by rw [sojournLaw, Coalescent.kingmanRate_one,
        expMeasure_eq_zero_of_nonpos le_rfl]; rfl⟩

/-- `t < 0` 时 `sojournLaw k (Ioi t) = 1`（逗留时间非负，故 `(t, ∞)` 是必然事件）。 -/
theorem sojournLaw_Ioi_of_neg {k : ℕ} (hk : 2 ≤ k) {t : ℝ} (ht : t < 0) :
    sojournLaw k (Set.Ioi t) = 1 := by
  haveI : IsProbabilityMeasure (sojournLaw k) := isProbabilityMeasure_sojournLaw hk
  have hc : sojournLaw k (Set.Iic t) = 0 := by
    rw [sojournLaw, expMeasure_Iic_eq (Coalescent.kingmanRate_pos hk) t,
      ite_eq_right (not_le.mpr ht)]
  have hsplit : sojournLaw k (Set.Iic t) + sojournLaw k (Set.Ioi t) = 1 := by
    rw [← measure_union (Set.Iic_disjoint_Ioi le_rfl) measurableSet_Ioi, Set.Iic_union_Ioi]
    exact measure_univ
  rw [hc, zero_add] at hsplit
  exact hsplit

/-- `sojournLaw k (Iic t) = ofReal (1 − e^{−d_k t})`，即 (1.7) 的**分布函数层**
（`0 ≤ t` 时 = `Coalescent.firstMergeCDF`，`Phylo/Stat/Coalescent.lean:307`）。

⚠️ 与 `sojournLaw_Ioi` 互补：`P(τ_k ≤ t) = 1 − e^{−d_k t}`、`P(τ_k > t) = e^{−d_k t}`。 -/
theorem sojournLaw_Iic {k : ℕ} (hk : 2 ≤ k) (t : ℝ) (ht : 0 ≤ t) :
    sojournLaw k (Set.Iic t) = ENNReal.ofReal (Coalescent.firstMergeCDF k t) := by
  have hkpos := Coalescent.kingmanRate_pos hk
  have hc : sojournLaw k (Set.Iic t)
      = 1 - ENNReal.ofReal (Real.exp (-(Coalescent.kingmanRate k * t))) := by
    rw [sojournLaw, expMeasure_Iic_eq hkpos t, ite_eq_left ht]
  rw [hc, Coalescent.firstMergeCDF, Coalescent.survival]
  have hexp : -(Coalescent.kingmanRate k * t) = -(Coalescent.kingmanRate k) * t := by ring
  rw [hexp]
  have ha : (0:ℝ) ≤ Real.exp (-(Coalescent.kingmanRate k) * t) := (Real.exp_pos _).le
  rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ ha]

/-- ★ **`E[τ_k] = 1/d_k`**（K82 (1.7)，第 **129–137** 行；期望值见第 **184–193** 行）。 -/
theorem integral_id_sojournLaw {k : ℕ} (hk : 2 ≤ k) :
    ∫ t, t ∂(sojournLaw k) = 1 / Coalescent.kingmanRate k :=
  integral_id_expMeasure (Coalescent.kingmanRate_pos hk)

/-- `Integrable` 版本（供 Fubini / 线性性用）。 -/
theorem integrable_id_sojournLaw {k : ℕ} (hk : 2 ≤ k) :
    Integrable (fun t : ℝ => t) (sojournLaw k) :=
  Integrable.of_integral_ne_zero (by
    rw [integral_id_sojournLaw hk]
    exact div_ne_zero one_ne_zero (ne_of_gt (Coalescent.kingmanRate_pos hk)))

/-- ★ 接合点：`1/d_k` **就是**库内既有的 `Coalescent.sojournMean k`（第 **193** 行）。 -/
theorem inv_kingmanRate_eq_sojournMean {k : ℕ} (hk : 2 ≤ k) :
    1 / Coalescent.kingmanRate k = Coalescent.sojournMean k := by
  have hk' : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have h1 : (k : ℝ) ≠ 0 := by linarith
  have h2 : (k : ℝ) - 1 ≠ 0 := by linarith
  rw [Coalescent.kingmanRate, Coalescent.sojournMean]
  field_simp

/-- `E[τ_{m+2}] = 2/((m+2)(m+1))`，以 `kingmanRate` 表达。 -/
theorem inv_kingmanRate_add_two (m : ℕ) :
    1 / Coalescent.kingmanRate (m + 2) = Coalescent.sojournMean (m + 2) :=
  inv_kingmanRate_eq_sojournMean (by omega)

/-! ## 2. 联合律 (1.11)：独立指数之积 -/

/-- **★★ K82 (1.11)**（第 **174–195** 行）：`n − 1` 个逗留时间 `τ_{n}, τ_{n−1}, …, τ_2` 的
**联合律** = 独立指数之积（`Measure.pi`，第 `i` 个坐标的速率是 `d_{i+2}`）。 -/
noncomputable def sojournJointLaw (n : ℕ) : Measure (Fin (n - 1) → ℝ) :=
  Measure.pi (fun i : Fin (n - 1) => sojournLaw (i.1 + 2))

/-- `n ≥ 2` 时 `sojournJointLaw n` 是概率测度。

（⚠️ 证明本身**不需要** `n ≥ 2`：`n < 2` 时 `Fin (n - 1)` 是空类型，`Measure.pi` 的
概率性空洞地成立。假设保留是为了与接口一致，并标明我们关心的参数域。） -/
theorem isProbabilityMeasure_sojournJointLaw {n : ℕ} (_hn : 2 ≤ n) :
    IsProbabilityMeasure (sojournJointLaw n) := by
  haveI : ∀ i : Fin (n - 1), IsProbabilityMeasure (sojournLaw (i.1 + 2)) := fun i =>
    isProbabilityMeasure_sojournLaw (by omega)
  exact Measure.pi.instIsProbabilityMeasure _

/-- **★ 单坐标的期望**：`∫ τ, τ i ∂(sojournJointLaw n) = 1/d_{i+2}`
（`Measure.pi` 的第 `i` 个边缘就是 `sojournLaw (i.1+2)`）。

器材：`MeasureTheory.integral_eval`（`Mathlib/MeasureTheory/Integral/Pi.lean:151`）。 -/
theorem integral_eval_sojournJointLaw {n : ℕ} (_hn : 2 ≤ n) (i : Fin (n - 1)) :
    ∫ τ : Fin (n - 1) → ℝ, τ i ∂(sojournJointLaw n)
      = 1 / Coalescent.kingmanRate (i.1 + 2) := by
  haveI : ∀ j : Fin (n - 1), IsProbabilityMeasure (sojournLaw (j.1 + 2)) := fun j =>
    isProbabilityMeasure_sojournLaw (by omega)
  rw [sojournJointLaw, MeasureTheory.integral_eval]
  exact integral_id_sojournLaw (by omega)

/-- `Integrable` 版本。 -/
theorem integrable_eval_sojournJointLaw {n : ℕ} (_hn : 2 ≤ n) (i : Fin (n - 1)) :
    Integrable (fun τ : Fin (n - 1) → ℝ => τ i) (sojournJointLaw n) := by
  haveI : ∀ j : Fin (n - 1), IsProbabilityMeasure (sojournLaw (j.1 + 2)) := fun j =>
    isProbabilityMeasure_sojournLaw (by omega)
  rw [sojournJointLaw]
  exact MeasureTheory.integrable_eval (integrable_id_sojournLaw (by omega))

/-! ## 3. Theorem 1：跳链 ⊥ 逗留时间（联合律形式） -/

/-- **★★ K82 Theorem 1 的联合律形式**（第 **210–215** 行）：`n`-溯祖的联合律
= 跳链的概率测度 `μ` **⊗** 逗留时间联合律 `sojournJointLaw n`。

以**任意** `μ : Measure Ω` 为参数，故与 W10a（跳链）**解耦**：协调侧把 `μ` 实例化成
`(jumpPMF n n).toMeasure` 即可。 -/
noncomputable def nCoalescentLaw {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (n : ℕ) : Measure (Ω × (Fin (n - 1) → ℝ)) :=
  μ.prod (sojournJointLaw n)

/-- `μ` 是概率测度、`n ≥ 2` 时 `nCoalescentLaw μ n` 是概率测度。 -/
theorem isProbabilityMeasure_nCoalescentLaw {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ} (hn : 2 ≤ n) :
    IsProbabilityMeasure (nCoalescentLaw μ n) := by
  haveI : IsProbabilityMeasure (sojournJointLaw n) := isProbabilityMeasure_sojournJointLaw hn
  exact Measure.prod.instIsProbabilityMeasure μ (sojournJointLaw n)

/-- **★★★ K82 Theorem 1**：跳链与逗留时间**独立**。

这里是**真·`IndepFun`**（不是「联合律 = 乘积测度」的代用语）；走 Mathlib 的
`indepFun_prod`，故需要 `[IsProbabilityMeasure μ]` 与 `2 ≤ n`
（后者是为了让 `sojournJointLaw n` 是概率测度）。 -/
theorem indepFun_fst_snd_nCoalescent {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ} (hn : 2 ≤ n) :
    IndepFun Prod.fst Prod.snd (nCoalescentLaw μ n) := by
  haveI : IsProbabilityMeasure (sojournJointLaw n) := isProbabilityMeasure_sojournJointLaw hn
  rw [nCoalescentLaw]
  have h := indepFun_prod (μ := μ) (ν := sojournJointLaw n)
    (X := fun ω : Ω => ω) (Y := fun τ : Fin (n - 1) → ℝ => τ) measurable_id measurable_id
  simpa only [Function.comp_def] using h

/-- Theorem 1 的**第一边缘**：跳链方向的边缘律就是 `μ`。 -/
theorem fst_nCoalescentLaw {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {n : ℕ} (hn : 2 ≤ n) : (nCoalescentLaw μ n).fst = μ := by
  haveI : IsProbabilityMeasure (sojournJointLaw n) := isProbabilityMeasure_sojournJointLaw hn
  rw [nCoalescentLaw, Measure.fst_prod]

/-- Theorem 1 的**第二边缘**：逗留时间方向的边缘律就是 `sojournJointLaw n`。 -/
theorem snd_nCoalescentLaw {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ} (hn : 2 ≤ n) :
    (nCoalescentLaw μ n).snd = sojournJointLaw n := by
  haveI : IsProbabilityMeasure (sojournJointLaw n) := isProbabilityMeasure_sojournJointLaw hn
  rw [nCoalescentLaw, Measure.snd_prod]

/-! ## 4. 期望：(1.12) `E[T] = 2(1 − 1/n)` -/

/-- **★★ K82 (1.11)+(1.12)**：`E[T] = E[Σ_{k=2}^n τ_k] = 2(1 − 1/n)`。

（`T = Σ_{k=2}^{n} τ_k` 与 `τ_k` 的独立性见 K82 第 **174–195** 行；
闭形式见 `Coalescent.expectedTotalCoalescenceTime`，`Phylo/Stat/Coalescent.lean:242`。） -/
theorem integral_sum_sojournJointLaw {n : ℕ} (hn : 2 ≤ n) :
    ∫ τ, ∑ i : Fin (n - 1), τ i ∂(sojournJointLaw n) = 2 * (1 - 1 / (n : ℝ)) := by
  rw [integral_finsetSum _ (fun i _ => integrable_eval_sojournJointLaw hn i)]
  rw [show (∑ i : Fin (n - 1), ∫ a : Fin (n - 1) → ℝ, a i ∂(sojournJointLaw n))
      = ∑ i : Fin (n - 1), 1 / Coalescent.kingmanRate (i.1 + 2) from
    Finset.sum_congr rfl (fun i _ => integral_eval_sojournJointLaw hn i)]
  rw [Fin.sum_univ_eq_sum_range (fun j => 1 / Coalescent.kingmanRate (j + 2)) (n - 1)]
  rw [show (∑ j ∈ Finset.range (n - 1), 1 / Coalescent.kingmanRate (j + 2))
      = ∑ j ∈ Finset.range (n - 1), Coalescent.sojournMean (j + 2) from
    Finset.sum_congr rfl (fun j _ => inv_kingmanRate_add_two j)]
  exact Coalescent.expectedTotalCoalescenceTime hn

end Phylo.Stat.KingmanCoalescent
