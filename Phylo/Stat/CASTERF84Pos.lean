/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.Stat.MSCKingmanMeasure
import Phylo.Stat.CASTERF84PropA
import Mathlib.Tactic

/-!
# `Phylo.Stat.CASTERF84Pos` —— F84 的**正性条件从「额外假设」变成「定理」**（子批 W13h）

## 1. 这一环补的是什么

`Phylo/Stat/MSCKingmanMeasure.lean` §6 已经把 JC69 / LM1 端到端定理里的两条**解析假设**

* `hf_int : Integrable P.f ν`（**幅度可积**）、
* `hf_pos : ∀ᵐ θ ∂ν, ¬ S.deep θ → 0 < P.f θ`（**幅度 `a.e.` 为正**）

**从 weight 表推出**，并给出**参数更少**的旗舰端点
`jc69_caster_statisticallyConsistent_kingman_measure_derived`。

F84 是**唯一没跟上**的模型，原因在 `W13_SPEC.md` §6.1 写得很清楚 ——
**F84 的 `λ` 不是常数、也不是自由参数，而是由 `π, κ` 算出来的**：

| 模型 | `λ` 的地位 | 需要的输入 |
|---|---|---|
| JC69 | **常数** `4/3` | 只要 `lx > 0` |
| LM1 | **自由参数** | `lm1_hf_pos_ae` 直接带 `hlam : 0 < lam` |
| **F84** | **闭式** `lamF84 π κ` | ⇒ **必须从 `π, κ` 推**（不能照搬上面两支） |

本文件把这条链补完：

```
π > 0 且 Σπ = 1、0 ≤ κ      ──►  0 < lamF84 π κ        （lamF84_pos）
0 < lamF84 π κ 且 0 < lx     ──►  0 < f84Amp π (lamF84 π κ) lx   （f84Amp_pos）
                             ──►  0 < (f84PropADataK π κ …).f θ  （当 0 < θ.1.2）
                             ──►  f84_hf_pos_ae   —— `hf_pos` **不再是假设**
                             ──►  f84_hf_int      —— `hf_int` **不再是假设**
```

## 2. ★ 与规格 §1.2 末表的逐条对应（**不发明新假设**）

所需条件**库内早已列出**（`Phylo/Stat/CASTERF84.lean` §3「假设（逐条）与诚实边界」原文）：

> `hsum : π_R + π_Y = 1`（即 `Σπ = 1`）；`hR : π_R ≠ 0`、`hY : π_Y ≠ 0`（`Bmat` 含除法）；
> **非负性证书另需 `π > 0`、`0 ≤ κ`、`0 ≤ λ`、`0 ≤ t`**。

⇒ 本文件把「`π > 0`、`Σπ = 1`、`0 ≤ κ`」这三条**形式化**，然后**推出** `0 < λ`。
`hR` / `hY` 由 `π > 0` **自动蕴含**（见 `piR_ne_zero_of_pos` / `piY_ne_zero_of_pos`），
**不额外要求** `λ` 或 `t` 的假设（它们由 `π, κ` 与 `lx > 0` 算出）。

## 3. ⚠️ `λ` 的口径差（**必须声明**）

`Phylo/Stat/CASTERF84.lean` §3 边界 (a) 写「`lam` 是**自由参数**，不形式化附录 1601 的 `λ` 闭式」；
而 `Phylo/Stat/CASTERF84PropA.lean` 的 `f84PropAData` / `f84PropADataK`
**已采用闭式** `λ = lamF84 θ.2.1 θ.2.2`。⇒ **两端口径不同**。

本文件**在 `PropA` 口径上做**（即 `λ := lamF84 π κ`），因为：
(1) 那才是**端到端定理** `f84_caster_statisticallyConsistent*` 实际用的幅度；
(2) `CASTERF84.lean` 那一侧的 `Kmat` / `Qmat` 把 `lam` 当参数，与正性无关
（`sm_pos` / `rm_pos` 对**任意** `lam` 都成立，见 `Phylo/Stat/CASTERF84.lean` §0）。
⇒ 本文件**不**触碰 `CASTERF84.lean` 的声明，只在其 §3 的过期注释处做**注释**修正。

## 4. 诚实边界

* 仍**未**消掉的：`hint`（正文条件 (2)「权重一致有界」）与 `hconv`（大数定律）。
  `hint` 的 `a.e.` 形式要 `θ ↦ τd θ T'` 与 `θ ↦ A θ T' T` 的**可测性**，
  而 `geneScore` / `patternProb` 的可测性库内尚无（缺口 **B2**，属子批 W13a）；
  `hconv` 是**块级 SLLN**（缺口 **B4**，属子批 W13d）。
* 本文件的 `hf_int` / `hf_pos` **只对 `ν = kingmanMSCMeasure ρ`（「固定物种树侧」）**给出，
  与 §6 对 JC69 / LM1 的口径**逐字一致**（`ρ` 是**参数**，MSC 不指定枝长先验）。
* `κ` 的建模涵义（规格 §6.1）：「`κ ≥ 0` ⟺ 类内（transition）速率 ≥ 跨类（transversion）速率」，
  且 `κ = 0` **有意保留**为「等速替换」的 F81 退化点 —— 本文件**不**要求 `0 < κ`。

## 5. 退化一致性（★ 最强探针）

* `κ = 0` 时 `lamF84 π 0 = π_Rπ_Y / ((1 − Σπᵢ²)π_Rπ_Y) = 1 / (1 − Σπᵢ²) > 0`
  ⇒ `f84Amp π (lamF84 π 0) lx = 2π_Aπ_Cπ_Gπ_Tπ_Rπ_Y(1 − e^{−lx/(1−Σπᵢ²)}) > 0`
  —— 正是 **F81**（等速替换）的幅度，**仍是正的**（本文件所有引理在 `κ = 0` 处不退化）。
* `π ≡ (1/4,1/4,1/4,1/4)`（`Σπ = 1`、`π > 0` 均成立）时 `Σπᵢ² = 1/4` ⇒ `lamF84 π κ = 1/(3/4 + κ)`：
  与 `W13_SPEC.md` §8④ 的口径一致（JC69 的 `λ` 是常数 `4/3 = 1/(3/4)`，对应 `κ = 0`）。

## 6. ⚠️ 三条**修正**（★D：规格 §6.1 未写、但对形式化是决定性的）

**(a) `f84Const` 比 `f84Amp` 多一个 `∏rm` 叶长因子**（`Phylo/Stat/CASTERF84PropA.lean`
的 `f84Amp` 与 `f84Const` 两个 `def` 之差）⇒ `f84PropADataK` 的幅度**不是**常数，
而是

    f θ = f84Amp π (lamF84 π κ) θ.1.2 · ∏ᵢ rm (lamF84 π κ) κ (θ.1.1 i)

⇒ **不能照抄** JC69 / LM1 的「像点上幅度是**常数** ⇒ 可积」路线
（`MSCKingmanMeasure.lean` §6.4 的 `hf_int` 证明正是靠这一条）。
本文件改用 **`rm ≤ 1`（在 `0 ≤ λ`、`0 ≤ κ` 下）** 把幅度**一致**压制住，再做可积性。

**(b) `sm` 没有注册可测性** ⇒ `fun_prop` 对 `f84Amp` **失败**（实测报
`No theorems found for Phylo.CASTERF84.sm`）⇒ 本文件先证 `sm_measurable` 再组合。

**(c) `Σπᵢ² < 1` 不能用 Cauchy–Schwarz** —— 它只给 `Σπᵢ² ≥ 1/4`（方向反、也不严格）。
正确的理由是**逐项** `πᵢ² < πᵢ`（因 `0 < πᵢ < 1`）。
规格 §1.2 末表第 1 行要的恰是 `Σπᵢ² < 1`（否则 `lamF84` 的分母第一项退化为 `0`）。
-/

set_option autoImplicit false

-- 本文件在命题目标上用 `haveI` 声明临时实例（`IsProbabilityMeasure`）；
-- linter 会建议 `have`，但那会把实例变成**命题假设**而破坏 `IsProbabilityMeasure` 的作用，
-- 故保留 `haveI` 并关掉该 linter（先例：`MSCKingmanMeasure.lean:89`、`KingmanCoalescent.lean:130`）。
set_option linter.style.haveILetI false

noncomputable section

namespace Phylo.Stat.CASTERF84Pos

open Phylo.CASTERF84
open Phylo.Stat.CASTERF84PropA
open Phylo.Stat.CASTERWeights
open Phylo.Stat.CASTERTopo
open Phylo.Stat.CASTERBridge
open Phylo.Stat.MSCInstance
open Phylo.Stat.MSCKingman
open Phylo.Stat.MSCKingmanMeasure
open MeasureTheory

/-! ## 0. 一条**纯标量**引理：`Fin 4` 正概率向量 ⇒ 平方和**严格** `< 1` -/

/-- ★★★ **`Σπ = 1` 与 `π > 0` ⇒ `Σπᵢ² < 1`（★ 严格）**。

**理由**：`π` 是**概率向量**，故每个分量 `πᵢ ∈ (0, 1)`
（`πᵢ > 0` 是假设；`πᵢ < 1` 由 `πᵢ = 1 − Σ_{j≠i} πⱼ < 1` 得到）⇒ **`πᵢ² < πᵢ`**（逐项）
⇒ 求和得 `Σπᵢ² < Σπᵢ = 1`。✓

⚠️ **Cauchy–Schwarz 在这里帮不上忙**：它只给 `(Σπᵢ)² ≤ 4Σπᵢ²`
（即 `Σπᵢ² ≥ 1/4`）—— **方向是下界、且不严格**，推不出 `Σπᵢ² < 1`。
规格 §1.2 末表第 1 行要的正是这个**严格上界**（否则 `lamF84` 的分母第一项退化为 `0`）。

⚠️ ★A/★D 记录：本条曾试图走「三条偏差非零」的 Lagrange 路线，
但「`π₀ ≠ π₁`」**是假命题** —— 反例 `π = (0.1, 0.1, 0.4, 0.4)`
（`π > 0`、`Σπ = 1` 都成立而 `π₀ = π₁`）。⇒ 已改走上面的逐项路线（**证伪后立即收口**）。 -/
theorem sum_sq_lt_one_of_pos (pi : Fin 4 → ℝ)
    (hpos : ∀ i : Fin 4, 0 < pi i) (hsum : ∑ i : Fin 4, pi i = 1) :
    ∑ i : Fin 4, pi i ^ 2 < 1 := by
  have h4 : pi 0 + pi 1 + pi 2 + pi 3 = 1 := by
    simpa only [Fin.sum_univ_four] using hsum
  have e0 : pi 0 < 1 := by linarith [h4, hpos 1, hpos 2, hpos 3]
  have e1 : pi 1 < 1 := by linarith [h4, hpos 0, hpos 2, hpos 3]
  have e2 : pi 2 < 1 := by linarith [h4, hpos 0, hpos 1, hpos 3]
  have e3 : pi 3 < 1 := by linarith [h4, hpos 0, hpos 1, hpos 2]
  have hs0 : pi 0 ^ 2 < pi 0 := by nlinarith [hpos 0, e0]
  have hs1 : pi 1 ^ 2 < pi 1 := by nlinarith [hpos 1, e1]
  have hs2 : pi 2 ^ 2 < pi 2 := by nlinarith [hpos 2, e2]
  have hs3 : pi 3 ^ 2 < pi 3 := by nlinarith [hpos 3, e3]
  rw [Fin.sum_univ_four]
  linarith

/-! ## 1. 两条**纯标量**正性引理（缺口清单 §6.1 #2 与 #3） -/

/-- ★★★ **`lamF84` 的分母为正**：`(1 − Σπᵢ²)·π_Rπ_Y + 2κ(π_Aπ_Gπ_Y + π_Cπ_Tπ_R) > 0`。

* 第一项 `> 0`：`Σπᵢ² < 1`（见 `sum_sq_lt_one_of_pos`），
  再由 `π_R = π_A + π_G > 0`、`π_Y = π_C + π_T > 0`；
* 第二项 `≥ 0`：`0 ≤ κ` 且 `π_Aπ_Gπ_Y + π_Cπ_Tπ_R ≥ 0`。 -/
theorem f84_denom_pos (pi : Fin 4 → ℝ) (κ : ℝ)
    (hpos : ∀ i : Fin 4, 0 < pi i) (hsum : piR pi + piY pi = 1) (hκ : 0 ≤ κ) :
    0 < (1 - (pi 0 ^ 2 + pi 1 ^ 2 + pi 2 ^ 2 + pi 3 ^ 2)) * piR pi * piY pi
      + 2 * κ * (pi 0 * pi 1 * piY pi + pi 2 * pi 3 * piR pi) := by
  have hsumall : ∑ i : Fin 4, pi i = 1 := sum_pi pi hsum
  have hsqall : ∑ i : Fin 4, pi i ^ 2 < 1 := sum_sq_lt_one_of_pos pi hpos hsumall
  have hexp : pi 0 ^ 2 + pi 1 ^ 2 + pi 2 ^ 2 + pi 3 ^ 2 = ∑ i : Fin 4, pi i ^ 2 := by
    rw [Fin.sum_univ_four]
  have hpR : 0 < piR pi := by
    have h : 0 < pi 0 + pi 1 := add_pos (hpos 0) (hpos 1)
    simpa only [piR] using h
  have hpY : 0 < piY pi := by
    have h : 0 < pi 2 + pi 3 := add_pos (hpos 2) (hpos 3)
    simpa only [piY] using h
  have h1 : 0 < (1 - (pi 0 ^ 2 + pi 1 ^ 2 + pi 2 ^ 2 + pi 3 ^ 2)) * piR pi * piY pi := by
    rw [hexp]
    exact mul_pos (mul_pos (by linarith) hpR) hpY
  have h2 : 0 ≤ pi 0 * pi 1 * piY pi :=
    mul_nonneg (mul_nonneg (hpos 0).le (hpos 1).le) hpY.le
  have h3 : 0 ≤ pi 2 * pi 3 * piR pi :=
    mul_nonneg (mul_nonneg (hpos 2).le (hpos 3).le) hpR.le
  nlinarith [mul_nonneg hκ (add_nonneg h2 h3), h1]

/-- ★★★ **缺口清单 §6.1 #2 补完**：`0 < lamF84 π κ`
（由「`π` 是正概率向量 ＋ `0 ≤ κ`」推出，**不是**额外假设）。

这正是 `W13_SPEC.md` §4⑤ / §6.1 要的那条链：
**模型条件 ⇒ `0 < lamF84 π κ`**，于是 `CASTERF84.lean` §3 列的「非负性证书另需 `0 ≤ λ`」
从**假设**变成**定理**。 -/
theorem lamF84_pos (pi : Fin 4 → ℝ) (κ : ℝ)
    (hpos : ∀ i : Fin 4, 0 < pi i) (hsum : piR pi + piY pi = 1) (hκ : 0 ≤ κ) :
    0 < lamF84 pi κ := by
  unfold lamF84
  have hpR : 0 < piR pi := by
    have h : 0 < pi 0 + pi 1 := add_pos (hpos 0) (hpos 1)
    simpa only [piR] using h
  have hpY : 0 < piY pi := by
    have h : 0 < pi 2 + pi 3 := add_pos (hpos 2) (hpos 3)
    simpa only [piY] using h
  exact div_pos (mul_pos hpR hpY) (f84_denom_pos pi κ hpos hsum hκ)

/-- ★★★ **缺口清单 §6.1 #3 补完**：`0 < f84Amp π λ lx`。

`f84Amp = 2·π_Aπ_Cπ_Gπ_T·π_Rπ_Y·(1 − e^{−λ·lx})`（`Phylo/Stat/CASTERF84PropA.lean` 的 `f84Amp`），
四个因子逐个为正：

* `2 > 0`；
* `π_Aπ_Cπ_Gπ_T > 0`、`π_Rπ_Y > 0` —— **正是「`π` 有正下界」这条模型条件**（规格 §1.2 末表第 1 行）；
* `1 − sm λ lx > 0` —— 由 `λ·lx > 0` 与 `sm λ lx = e^{−λ·lx} < 1`。

⚠️ 本引理只要求**乘积** `λ·lx > 0`（最一般的形式）；调用处用
`0 < lamF84 π κ`（`lamF84_pos`）与 `0 < lx` 经 `mul_pos` 供给。
⇒ `λ` 与 `lx` 的**正性都由本文件算出**，不是假设。 -/
theorem f84Amp_pos (pi : Fin 4 → ℝ) (hpos : ∀ i : Fin 4, 0 < pi i)
    {lam lx : ℝ} (hl : 0 < lam * lx) : 0 < f84Amp pi lam lx := by
  have h4 : sm lam lx < 1 := by
    have hlt : -(lam * lx) < 0 := by linarith
    calc sm lam lx = Real.exp (-(lam * lx)) := rfl
      _ < Real.exp 0 := Real.exp_lt_exp.mpr hlt
      _ = 1 := Real.exp_zero
  have h5 : 0 < 1 - sm lam lx := by linarith
  have hprod : 0 < pi 0 * pi 2 * pi 1 * pi 3 :=
    mul_pos (mul_pos (mul_pos (hpos 0) (hpos 2)) (hpos 1)) (hpos 3)
  have hpR : 0 < piR pi := by
    have h : 0 < pi 0 + pi 1 := add_pos (hpos 0) (hpos 1)
    simpa only [piR] using h
  have hpY : 0 < piY pi := by
    have h : 0 < pi 2 + pi 3 := add_pos (hpos 2) (hpos 3)
    simpa only [piY] using h
  unfold f84Amp
  have hpre : 0 < 2 * (pi 0 * pi 2 * pi 1 * pi 3) * piR pi * piY pi :=
    mul_pos (mul_pos (mul_pos (by norm_num) hprod) hpR) hpY
  nlinarith [hpre]

/-! ## 2. 「`π` 是正概率向量」⇒ §6.1 的 `hR` / `hY` **自动成立** -/

/-- ★★ **`π > 0` ⇒ `π_R ≠ 0`**（`CASTERF84PropA` 的 `hR` 不再是独立假设）。 -/
theorem piR_ne_zero_of_pos (pi : Fin 4 → ℝ) (hpos : ∀ i : Fin 4, 0 < pi i) :
    piR pi ≠ 0 := by
  have h : 0 < pi 0 + pi 1 := add_pos (hpos 0) (hpos 1)
  simpa only [piR] using ne_of_gt h

/-- ★★ **`π > 0` ⇒ `π_Y ≠ 0`**（`CASTERF84PropA` 的 `hY` 不再是独立假设）。 -/
theorem piY_ne_zero_of_pos (pi : Fin 4 → ℝ) (hpos : ∀ i : Fin 4, 0 < pi i) :
    piY pi ≠ 0 := by
  have h : 0 < pi 2 + pi 3 := add_pos (hpos 2) (hpos 3)
  simpa only [piY] using ne_of_gt h

/-! ## 3. 幅度的**因式分解**（★D：`f84Const` 比 `f84Amp` 多一个 `∏rm`） -/

/-- ★★ **`sm` 可测**（`sm lam t = e^{−lam·t}`）。

⚠️ `fun_prop` **证不出** `Measurable (fun t => sm lam t)` —— `sm` 是库内自定义 `def`，
没有注册 `Measurable` 实例（实测报 `No theorems found for Phylo.CASTERF84.sm`）
⇒ 必须先 `unfold sm` 把它变成 `Real.exp` 的复合，`fun_prop` 才能收口。 -/
theorem sm_measurable (lam : ℝ) : Measurable fun t : ℝ => sm lam t := by
  unfold sm
  fun_prop

-- 把上一条注册进 `fun_prop` 数据库：不然 `fun_prop` 对 `sm` 无法自动推进
-- （实测：`No theorems found for Phylo.CASTERF84.sm`）。
attribute [fun_prop] sm_measurable

/-- ★★ **`f84Amp` 关于内枝长可测**（用于 `hf_int` 的 `Measurable` 前提）。

⚠️ 上面先证 `sm_measurable` 是**必需**的：`fun_prop` 对 `sm` 本身无实例，
但一旦 `sm_measurable` 进入环境，`fun_prop` 就能把下一条整个收口。 -/
theorem measurable_f84Amp (pi : Fin 4 → ℝ) (κ : ℝ) :
    Measurable fun lx : ℝ => f84Amp pi (lamF84 pi κ) lx := by
  unfold f84Amp
  fun_prop

/-- ★★ **`rm lam kap t ≤ 1`（当 `0 ≤ lam·(1+kap)·t`）**。
（本文件当前**未**直接调用它 —— 保留作 §5 的备用路线与后续子批的器材。） -/
theorem rm_le_one {lam kap t : ℝ} (h : 0 ≤ lam * (1 + kap) * t) : rm lam kap t ≤ 1 := by
  unfold rm
  rw [Real.exp_le_one_iff]
  linarith

/-- ★★ **幅度的因式分解**：`f θ = f84Amp π (lamF84 π κ) θ.1.2 · ∏ᵢ rm (lamF84 π κ) κ (θ.1.1 i)`。

⚠️ **不能**写成「`f θ = f84Amp π (lamF84 π κ) θ.1.2`」—— 那**是假命题**
（`f84Const` 比 `f84Amp` 多一个 `∏rm` 叶长因子，见 §6(a)）。
本文件的正性（§4）与有界性（§5）都建立在这条**正确的**因式分解上。 -/
theorem f84PropADataK_f_factor (pi : Fin 4 → ℝ) (κ : ℝ)
    (hR : piR pi ≠ 0) (hY : piY pi ≠ 0) (θ : KingmanΘ) :
    (f84PropADataK pi κ hR hY).f θ
      = f84Amp pi (lamF84 pi κ) θ.1.2
        * (rm (lamF84 pi κ) κ (θ.1.1 0) * rm (lamF84 pi κ) κ (θ.1.1 1)
          * rm (lamF84 pi κ) κ (θ.1.1 2) * rm (lamF84 pi κ) κ (θ.1.1 3)) := by
  have hfun : (f84PropADataK pi κ hR hY).f
      = fun θ : KingmanΘ => f84F_uncond pi κ θ.1 := rfl
  rw [hfun]
  simp only [f84F_uncond, f84Const]

/-- ★★ **幅度的正性（逐点版，条件是「内枝长 `> 0`」）** —— `a.e.` 版的基石。

⚠️ `hR` / `hY` 在此**未被用到**（正性只涉及 `f84Amp` 的四个因子与恒正的 `rm`）；
它们保留在签名里是为了与 `f84PropADataK` 的**参数口径**逐字一致。 -/
theorem f84PropADataK_f_pos_of (pi : Fin 4 → ℝ) (κ : ℝ)
    (hR : piR pi ≠ 0) (hY : piY pi ≠ 0)
    (hpos : ∀ i : Fin 4, 0 < pi i) (hsum : piR pi + piY pi = 1) (hκ : 0 ≤ κ)
    {θ : KingmanΘ} (hθ : 0 < θ.1.2) :
    0 < (f84PropADataK pi κ hR hY).f θ := by
  rw [f84PropADataK_f_factor]
  have hA : 0 < f84Amp pi (lamF84 pi κ) θ.1.2 :=
    f84Amp_pos pi hpos (mul_pos (lamF84_pos pi κ hpos hsum hκ) hθ)
  have h0 : 0 < rm (lamF84 pi κ) κ (θ.1.1 0) := rm_pos _ _ _
  have h1 : 0 < rm (lamF84 pi κ) κ (θ.1.1 1) := rm_pos _ _ _
  have h2 : 0 < rm (lamF84 pi κ) κ (θ.1.1 2) := rm_pos _ _ _
  have h3 : 0 < rm (lamF84 pi κ) κ (θ.1.1 3) := rm_pos _ _ _
  have hrm : 0 < rm (lamF84 pi κ) κ (θ.1.1 0) * rm (lamF84 pi κ) κ (θ.1.1 1)
      * rm (lamF84 pi κ) κ (θ.1.1 2) * rm (lamF84 pi κ) κ (θ.1.1 3) :=
    mul_pos (mul_pos (mul_pos h0 h1) h2) h3
  exact mul_pos hA hrm

/-! ## 4. ★★★ `hf_pos` **不再是假设**（缺口清单 §6.1 #4 的一半） -/

/-- ★★★ **F84 的 `hf_pos`（`a.e.` 形式）是定理**：
把 `Phylo.Stat.MSCInstance.f84_caster_statisticallyConsistent_kingman` 的假设
`hf_pos : ∀ᵐ θ ∂ν, ¬ deep θ → 0 < (f84PropADataK π κ …).f θ` **证掉**。

**证明路线**（与 `MSCKingmanMeasure.lean` §6.3 的 `jc69_hf_pos_ae` **逐字同型**）：

1. `rw [ae_iff]` ⇒ 只需证 `ν {θ | ¬(¬deep θ → 0 < f θ)} = 0`；
2. 用 `measure_mono_null` 把该集合**包含**进 `{θ | θ.1.2 ≤ 0}`，而后者由
   `kingmanMSCMeasure_dirac_lx_nonpos` 是**零测**（像点的内枝长恒 `a + b > 0`）；
3. 包含关系：若 `¬deep θ` 且 `0 < θ.1.2`，则 `f θ > 0`（`f84PropADataK_f_pos_of`）。

⚠️ **必须**是 `a.e.` 形式：`KingmanΘ` 是**乘积类型**，其中有 `θ.1.2 ≤ 0` 的
物理不可达点（`f = 0`）⇒ 逐点形式是**假命题**（见 `MSCKingmanMeasure.lean` §6 的说明）。 -/
theorem f84_hf_pos_ae (pi : Fin 4 → ℝ) (κ : ℝ)
    (hpos : ∀ i : Fin 4, 0 < pi i) (hsum : piR pi + piY pi = 1) (hκ : 0 ≤ κ)
    (leaf : Fin 4 → ℝ) (a b : NNReal) (hab : 0 < ((a : ℝ) + (b : ℝ))) :
    ∀ᵐ θ ∂(kingmanMSCMeasure (Measure.dirac (leaf, a, b))),
      ¬ kingmanMSCTopoSym.deep θ →
        0 < (f84PropADataK pi κ (piR_ne_zero_of_pos pi hpos)
          (piY_ne_zero_of_pos pi hpos)).f θ := by
  rw [ae_iff]
  refine measure_mono_null (fun θ hθ => ?_)
    (kingmanMSCMeasure_dirac_lx_nonpos leaf a b hab)
  have hg : (f84PropADataK pi κ (piR_ne_zero_of_pos pi hpos)
      (piY_ne_zero_of_pos pi hpos)).f θ
      = f84Amp pi (lamF84 pi κ) θ.1.2
        * (rm (lamF84 pi κ) κ (θ.1.1 0) * rm (lamF84 pi κ) κ (θ.1.1 1)
          * rm (lamF84 pi κ) κ (θ.1.1 2) * rm (lamF84 pi κ) κ (θ.1.1 3)) :=
    f84PropADataK_f_factor pi κ _ _ θ
  by_contra hcon
  have hpos : 0 < (f84PropADataK pi κ (piR_ne_zero_of_pos pi hpos)
      (piY_ne_zero_of_pos pi hpos)).f θ :=
    f84PropADataK_f_pos_of pi κ _ _ hpos hsum hκ (not_le.mp hcon)
  exact (not_imp.mp hθ).2 hpos

/-! ## 5. `hf_int`（幅度可积）—— **已证到「常数化 + 有界」这一步，收口尚欠一格**

本节把 F84 的 `hf_int` 所需的两件**数学内容**全部证完：

1. **像点上幅度是常数**（`f84F_uncond_factor` + `toKingmanΘ_apply`）；
2. **该常数 `B` 非负**（由 `f84Amp_pos` 与 `rm_pos`）。

⇒ `Integrable.of_bound` 直接给出乘积空间上的可积性
（见 `f84_hf_int_image`）。

⚠️ **诚实边界**：把它从 `Measure.map` 的积分拉回
`Integrable g (kingmanMSCMeasure …)` 还差一格代理收口：本库的
`integrable_map_measure` / `Integrable.comp_measurable` 都要求**复合形式** `Integrable (g ∘ F) v`，
而 `Integrable g (Measure.map F v)` 与它**不是** definitional 相等（已实测：
`exact` / `simpa` / `change` 均报 Type mismatch）。
`lintegral_map'` 路线需要额外的 `0 ≤ᵐ g`，而那条**可由常数化给出**
（见 `hf_int` 的第 3 步）—— 即总共只差一步 `ae_map_iff` 的收尾。
故本节**不声称 `f84_hf_int` 已完成**（遵守 BRIEF §2.1「零假命题」）。 -/

/-- ★★ **`rm` 可测**（同 `sm`：自定义 `def` 没有注册 `Measurable` 实例）。 -/
theorem rm_measurable (lam kap : ℝ) : Measurable fun t : ℝ => rm lam kap t := by
  unfold rm
  fun_prop

attribute [fun_prop] rm_measurable

/-- ★★ **`f84F_uncond` 可测**（展开成 `f84Amp`·`∏rm` 后逐项可测）。

⚠️ 这条依赖 `sm_measurable` / `rm_measurable` 与 `fun_prop` 的配合（见 §3）。 -/
theorem measurable_f84F_uncond (pi : Fin 4 → ℝ) (κ : ℝ) :
    Measurable (fun θ : (Fin 4 → ℝ) × ℝ => f84F_uncond pi κ θ) := by
  simp only [f84F_uncond, f84Const, f84Amp]
  fun_prop

/-- ★★★ **幅度在任意 `θ` 上的因式分解**（`f84Const` 的原始形）：

    f84F_uncond π κ (l, lx)
      = f84Amp π (lamF84 π κ) lx · ∏ᵢ rm (lamF84 π κ) κ (l i)

⚠️ **不能**写成「`= f84Amp π (lamF84 π κ) lx`」 —— 那**是假命题**
（`f84Const` 比 `f84Amp` 多一个 `∏rm` 叶长因子）。 -/
theorem f84F_uncond_factor (pi : Fin 4 → ℝ) (κ : ℝ)
    (l : Fin 4 → ℝ) (lx : ℝ) :
    f84F_uncond pi κ (l, lx)
      = f84Amp pi (lamF84 pi κ) lx
        * (rm (lamF84 pi κ) κ (l 0) * rm (lamF84 pi κ) κ (l 1)
          * rm (lamF84 pi κ) κ (l 2) * rm (lamF84 pi κ) κ (l 3)) := by
  simp only [f84F_uncond, f84Const]

/-- ★★ **`toKingmanΘ` 在 `((leaf, a, b), v)` 上的闭式**：内枝长恒为 `a + b`，
叶长分量恒为**给定的 `leaf`**（不是零函数！—— 它是种树侧参数）。 -/
theorem toKingmanΘ_apply (leaf : Fin 4 → ℝ) (a b : NNReal) (v : ℝ × ℝ) :
    toKingmanΘ ((leaf, a, b), v)
      = ((leaf, (a : ℝ) + (b : ℝ)),
          (decide ((a : ℝ) < v.1), decide ((b : ℝ) < v.2))) := rfl

/-- ★★★ **`hf_int` 的数学内核（已证）**：在 `ρ = dirac (leaf, a, b)` 的**乘积空间**上，
F84 的幅度**恒等于常数** `B`、且 `B ≥ 0` ⇒ 可积。

这就是 JC69/LM1 的 `hf_int` 证明里「像点上是常数」那一步，
只是 F84 的常数多了一个 `∏rm (leaf)` 因子。

⚠️ `_hpos` / `_hsum` / `_hκ` 在**本条的证明里未被用到** —— 常数化与可积性不需要它们；
保留（并加 `_` 前缀以消除 linter 告警）是为了与 `lamF84_pos` / `f84Amp_pos` /
`f84_hf_pos_ae` / `f84_hf_int` 的**参数口径逐字一致**。 -/
theorem f84F_uncond_image_const (pi : Fin 4 → ℝ) (κ : ℝ)
    (leaf : Fin 4 → ℝ) (a b : NNReal) :
    ∀ v : ℝ × ℝ,
      f84F_uncond pi κ (toKingmanΘ ((leaf, a, b), v)).1
        = f84Amp pi (lamF84 pi κ) ((a : ℝ) + (b : ℝ))
          * (rm (lamF84 pi κ) κ (leaf 0) * rm (lamF84 pi κ) κ (leaf 1)
            * rm (lamF84 pi κ) κ (leaf 2) * rm (lamF84 pi κ) κ (leaf 3)) := by
  intro v
  rw [toKingmanΘ_apply]
  exact f84F_uncond_factor pi κ leaf ((a : ℝ) + (b : ℝ))

/-- ★★★ **`hf_int` 的数学内核（已证）**：在 `ρ = dirac (leaf, a, b)` 的**乘积空间**上，
F84 的幅度**恒等于常数** ⇒ 可积。

这就是 JC69/LM1 的 `hf_int` 证明里「像点上是常数」那一步，
只是 F84 的常数多了一个 `∏rm (leaf)` 因子（见 `f84F_uncond_image_const`）。

⚠️ 本条**不需要** `hpos` / `hsum` / `hκ` —— 常数化与可积性不用它们，
故签名里**不列**它们（避免 linter 的 `unusedVariables` 告警；
那三条在外层 `f84_hf_int` 的签名里。） -/
theorem f84_hf_int_image (pi : Fin 4 → ℝ) (κ : ℝ)
    (leaf : Fin 4 → ℝ) (a b : NNReal) :
    Integrable (fun v : ℝ × ℝ =>
        f84F_uncond pi κ (toKingmanΘ ((leaf, a, b), v)).1)
      ((Phylo.Stat.KingmanCoalescent.sojournLaw 2).prod
        (Phylo.Stat.KingmanCoalescent.sojournLaw 2)) := by
  haveI : IsProbabilityMeasure (Phylo.Stat.KingmanCoalescent.sojournLaw 2) :=
    Phylo.Stat.KingmanCoalescent.isProbabilityMeasure_sojournLaw (by norm_num)
  haveI : IsProbabilityMeasure
      ((Phylo.Stat.KingmanCoalescent.sojournLaw 2).prod
        (Phylo.Stat.KingmanCoalescent.sojournLaw 2)) := inferInstance
  refine (integrable_const (f84Amp pi (lamF84 pi κ) ((a : ℝ) + (b : ℝ))
      * (rm (lamF84 pi κ) κ (leaf 0) * rm (lamF84 pi κ) κ (leaf 1)
        * rm (lamF84 pi κ) κ (leaf 2) * rm (lamF84 pi κ) κ (leaf 3)))).congr ?_
  exact Filter.Eventually.of_forall fun v => (f84F_uncond_image_const pi κ leaf a b v).symm

/-- ★★★ **`Integrable` 沿 `Measure.map` 的拉回**：若 `g ∘ F` 在 `v` 上可积、`F` 可测，
则 `g` 在 `Measure.map F v` 上可积。

⚠️ 不能直接 `exact`：`Integrable` / `HasFiniteIntegral` 在 `Measure.map` 下**不是**
definitional 相等（实测报 Type mismatch）。必须分两个分量：
`AEStronglyMeasurable` 直接取，`HasFiniteIntegral` 用 `hasFiniteIntegral_iff_norm`
（**norm 形**，避开 `…_iff_ofReal` 的 `0 ≤ᵐ g` 额外侧条件）加 `lintegral_map'` 改写。 -/
theorem integrable_map_of {g : KingmanΘ → ℝ} {F : ℝ × ℝ → KingmanΘ}
    {v : Measure (ℝ × ℝ)} (hF : Measurable F) (hg : Measurable g)
    (h : Integrable (g ∘ F) v) : Integrable g (Measure.map F v) := by
  refine ⟨hg.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  rw [lintegral_map' (f := fun a : KingmanΘ => ENNReal.ofReal ‖g a‖) (g := F)
    ((continuous_abs.measurable.comp hg).ennreal_ofReal.aemeasurable) hF.aemeasurable]
  rw [← hasFiniteIntegral_iff_norm]
  exact h.2

/-- ★★★ **缺口清单 §6.1 #4 的另一半（完成）**：把
`Phylo.Stat.MSCInstance.f84_caster_statisticallyConsistent_kingman` 的假设
`hf_int : Integrable (f84PropADataK π κ …).f ν` **证掉**。

ν 的口径**与 JC69/LM1 的 `…_hf_int` 逐字同型**：只对
`ν = kingmanMSCMeasure (Measure.dirac (leaf, a, b))`（**固定种树侧参数**）。

⚠️ **完整诚实边界（必读）**：本定理**不对一般 `ρ`** 成立 ——
因为 F84 的幅度带 `∏ᵢ rm (λ, κ, lᵢ)` 因子，而 `rm lam kap t = e^{−lam(1+kap)t}`
**对 `t → −∞` 无界**（`Phylo/Stat/CASTERF84.lean` 的 `rm_pos` 只给正性）
⇒ 当 `ρ` 在叶长上给出负值时，`∏rm` 可任意大，故可积性不成立。
JC69/LM1 无此因子，故它们的 `…_hf_int` 也只对 `dirac` 叙述（同样是 `dirac`）。
若要一般 `ρ`，需 `ρ` 集中在叶长 `≥ 0` 的集上（即模型 §1.2 的「叶长有界」条件）——
这正是规格 §1.2 末表第 1 行要求的。 -/
theorem f84_hf_int (pi : Fin 4 → ℝ) (κ : ℝ)
    (hpos : ∀ i : Fin 4, 0 < pi i) (_hsum : piR pi + piY pi = 1) (_hκ : 0 ≤ κ)
    (leaf : Fin 4 → ℝ) (a b : NNReal) :
    Integrable (f84PropADataK pi κ (piR_ne_zero_of_pos pi hpos)
      (piY_ne_zero_of_pos pi hpos)).f
      (kingmanMSCMeasure (Measure.dirac (leaf, a, b))) := by
  have hmeas : Measurable (fun θ : KingmanΘ => f84F_uncond pi κ θ.1) :=
    (measurable_f84F_uncond pi κ).comp measurable_fst
  have hfun : (f84PropADataK pi κ (piR_ne_zero_of_pos pi hpos)
      (piY_ne_zero_of_pos pi hpos)).f
      = fun θ : KingmanΘ => f84F_uncond pi κ θ.1 := rfl
  have hmap : Measurable (fun v : ℝ × ℝ => toKingmanΘ ((leaf, a, b), v)) :=
    measurable_toKingmanΘ.comp (measurable_const.prodMk measurable_id)
  rw [hfun, kingmanMSCMeasure_dirac_eq_map]
  refine integrable_map_of hmap hmeas ?_
  exact f84_hf_int_image pi κ leaf a b

end Phylo.Stat.CASTERF84Pos
