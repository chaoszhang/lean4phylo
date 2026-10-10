/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Probability.Distributions.Geometric
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Dirac.Basic

set_option linter.style.haveILetI false

open MeasureTheory
open scoped ENNReal

/-!
# `Phylo.Stat.TKF91` —— Thorne–Kishino–Felsenstein (1991) 插入–删除链的**显式转移概率**

文献：J. L. Thorne, H. Kishino, J. Felsenstein, *An evolutionary model for maximum likelihood
alignment of DNA sequences*, J. Mol. Evol. **33** (1991) 114–124。
下文行号一律指
`references/md/ThorneKishinoFelsenstein1991_EvolutionaryModelMLAlignment.md`。

## 1. 模型（文献 258–316 行）

序列被看成「链接」（link）：`N` 个碱基的序列有 `N` 个 **normal link** 加 **1 个 immortal link**
（最左碱基左边，263–272 行）。每个 link **独立**演化：

* 每个 link（normal 与 immortal **同率**）以速率 `λ` **生**，新生 link 一定是 normal（285–291 行）；
* 只有 normal link 会以速率 `μ` **死**，immortal link 永不死（295–297 行）。

于是长度 `n` 的序列以速率 `(n+1)λ` 增长、以速率 `nμ` 缩短（305–311 行）。
文献 339–341 行强调：只有当 **`μ > λ`** 时才有现实的**长度稳态分布**；
343–345 行给出该稳态是**几何分布**，355–371 行给出其均值 `λ/(μ-λ)`、方差 `λμ/(μ-λ)²`。

## 2. 三条 link 转移概率族（文献 426–434 行的定义 + 式 (9) + 式 (12)）

对一个 normal link，时间 `t` 后它的后代 link 数记为 `n`：

* `p_n(t)`（`n ≥ 1`）：共 `n` 个后代，且**原 link 存活**；
* `p'_n(t)`（`n ≥ 0`）：共 `n` 个后代，且**原 link 已死**（`n = 0` 即整条线灭绝，`p'_0 = μβ`）；
* `p''_n(t)`（`n ≥ 1`）：immortal link 共有 `n` 个后代（**含自身**），`p''_0 = 0`。

文献 447 行：`p_0(t) = p''_0(t) = 0`。文献 (8)（519–539 行）的初值：`p_1(0) = p''_1(0) = 1`，
`p_n(0) = p''_n(0) = 0`（`n ≥ 2`），`p'_n(0) = 0`（**`n = 0, 1, …`，含 `n = 0`**）。

文献 (12)（631–637 行）给出**几何递推**：对 `k ≥ 1`

  `p_k(t) = p_1(t)·(λβ(t))^{k-1}`，`p'_k(t) = p'_1(t)·(λβ(t))^{k-1}`，
  `p''_k(t) = p''_1(t)·(λβ(t))^{k-1}`，

其中 `β(t)` 是式 (10)（573–581 行）`β(t) = (1 - e^{(λ-μ)t}) / (μ - λ e^{(λ-μ)t})`，
本文件把几何比记作 `tkfRatio lam mu t = λβ(t)`。

**本文件的落地策略**：全部**组合/级数**结论（三条族的归一化、行和、递推、稳态均值方差）
只用到 (12) 的**几何结构**，因此把 `r = λβ(t)` 当作 `‖r‖ < 1` 的**自由实参数**
（纯代数 + 几何级数，`hasSum_geometric_of_norm_lt_one`）。
超越层的 `β(t)` 与 `e^{-μt}` 在 §5 显式定义，并证明 `λβ(t) ∈ [0,1)`，
从而把 §3–§4 的结论**在 `0 < λ < μ`、`t ≥ 0` 下真正代回文献的参数**。

## 3. 文献 426–434 行的**行和**（本文件的定理，不是定义）

| 族 | 全质量 | 含义 |
|---|---|---|
| `p` | `e^{-μt}` | 原 normal link **必须存活**（`Σ_n p_n(t) = e^{-μt} ≠ 1`！） |
| `p'` | `1 - e^{-μt}` | 原 normal link **必须死** |
| `p''` | `1` | immortal link 永不死 |
| `p + p'` | `1` | 后代数分布（= Kendall 线性生灭过程的几何律） |

★ 注意第二列：**`p` 族不是概率分布**（只有 `t = 0` 时才是）。见 `tsum_pNorm`。

## 4. 规范化与缺口

* 式 (11)（541 行）与 (13)–(14)（727–775 行）的**两序列比对似然**（对**所有**比对求和 + DP）
  超出本次范围 ⇒ 显式 `def … : Prop` 缺口 `pairwiseAlignmentLikelihood_gap`；
* `λ = μ` 时式 (10) 是 `0/0`（真极限 `β → t/(1+μt)`）⇒ 缺口 `tkfBetaCriticalLimit_gap`；
* 1992 勘误（J. Mol. Evol. **34**(1) 91）正文**不在本仓库** ⇒ 缺口 `tkf92Erratum_gap`。
-/

noncomputable section

namespace Phylo.Stat.TKF91

/-! ## 5. 式 (10)：超越层定义 -/

/-- 式 (10) 的**规范变量形式**：`u` 扮演 `e^{(λ-μ)t}`。
`tkfBeta_eq_gauge` 说明它与文献印出的形式逐字一致。 -/
def tkfBetaGauge (lam mu u : ℝ) : ℝ := (1 - u) / (mu - lam * u)

/-- 式 (10)（573–581 行）：`β(t) = (1 - e^{(λ-μ)t}) / (μ - λ e^{(λ-μ)t})`。 -/
def tkfBeta (lam mu t : ℝ) : ℝ := tkfBetaGauge lam mu (Real.exp ((lam - mu) * t))

/-- `tkfBeta` 就是式 (10) 在 `u = e^{(λ-μ)t}` 处的取值。 -/
theorem tkfBeta_eq_gauge (lam mu t : ℝ) :
    tkfBeta lam mu t = tkfBetaGauge lam mu (Real.exp ((lam - mu) * t)) := rfl

/-- 几何比 `λβ(t)`（即式 (12) 里的 `λβ(t)`），规范变量形式。 -/
def tkfRatioGauge (lam mu u : ℝ) : ℝ := lam * tkfBetaGauge lam mu u

/-- 几何比 `λβ(t)`：式 (12) 的比，稳态时 `→ λ/μ`。 -/
def tkfRatio (lam mu t : ℝ) : ℝ := lam * tkfBeta lam mu t

/-- 原 normal link 在 `t` 后**仍存活**的概率 `e^{-μt}`（= `p` 族的全质量）。 -/
def tkfSurv (mu t : ℝ) : ℝ := Real.exp (-(mu * t))

/-- `p'_0(t) = μβ(t)`：原 link 已死且**没有**后代（整条线灭绝）的概率，规范变量形式。 -/
def tkfExtinctGauge (lam mu u : ℝ) : ℝ := mu * tkfBetaGauge lam mu u

/-- `p'_0(t) = μβ(t)`：原 link 已死且**没有**后代的概率。
文献 533–535 行的初值 `p'_0(0) = 0` 正是这一条（`t = 0` ⇒ `u = 1` ⇒ `β = 0`）。 -/
def tkfExtinct (lam mu t : ℝ) : ℝ := mu * tkfBeta lam mu t

/-! ## 6. 几何核：式 (12) 的比 -/

/-- 几何核 `c·r^k`（`k : ℕ`）。文献 (12) 的 `[λβ(t)]^{k-1}` 结构。 -/
def tkfGeom (c r : ℝ) (k : ℕ) : ℝ := c * r ^ k

/-- ★★ 几何归一化：`‖r‖ < 1` 时 `Σ_k (1-r) r^k = 1`（`HasSum` 形式）。 -/
theorem hasSum_tkfGeom {r : ℝ} (hr : ‖r‖ < 1) : HasSum (tkfGeom (1 - r) r) 1 := by
  have hne : (1 : ℝ) - r ≠ 0 := by
    intro h
    have hr1 : r = 1 := by linarith
    rw [hr1, norm_one] at hr
    exact lt_irrefl 1 hr
  have h := (hasSum_geometric_of_norm_lt_one (K := ℝ) hr).mul_left (1 - r)
  rw [mul_inv_cancel₀ hne] at h
  change HasSum (fun k : ℕ => tkfGeom (1 - r) r k) 1
  rw [show (fun k : ℕ => tkfGeom (1 - r) r k) = fun k : ℕ => (1 - r) * r ^ k from by
    funext k
    rfl]
  exact h

/-- ★★ 几何归一化（`∑'` 形式）。 -/
theorem tsum_tkfGeom {r : ℝ} (hr : ‖r‖ < 1) : ∑' k : ℕ, tkfGeom (1 - r) r k = 1 :=
  (hasSum_tkfGeom hr).tsum_eq

/-! ## 7. 三条转移概率族（式 (9)，索引 = 后代 link 数） -/

/-- `p_n(t)`：normal link 的后代数恰为 `n` 且**原 link 存活**（文献 428–430 行）。
由 `p_0(t) = 0`（447 行）与式 (12)：`p_{k+1} = p_1 · r^k`，故 `p_{k+1} = s(1-r)r^k`，
其中 `s = e^{-μt}` 是原 link 的存活概率、`r = λβ(t)`。 -/
def pNorm (s r : ℝ) : ℕ → ℝ
  | 0 => 0
  | (n + 1) => s * tkfGeom (1 - r) r n

/-- `p'_n(t)`：normal link 的后代数恰为 `n` 且**原 link 已死**（文献 430–432 行）。
`n = 0` 给 `α = μβ(t)`；由式 (12)，`n ≥ 1` 时 `p'_n = (1 - s - α)(1-r)r^{n-1}`
（系数由「`p'` 族全质量 = `1 - e^{-μt}`」定出，见 `tsum_pDead`）。 -/
def pDead (α s r : ℝ) : ℕ → ℝ
  | 0 => α
  | (n + 1) => (1 - s - α) * tkfGeom (1 - r) r n

/-- `p''_n(t)`：immortal link 的后代数恰为 `n`（**含自身**）（文献 432–434 行）。
`p''_0(t) = 0`（447 行）；由式 (12) 与全质量 `1` 得 `p''_{k+1} = (1-r)r^k`
（immortal link 相当于「永不死」的 normal link）。 -/
def pImm (r : ℝ) : ℕ → ℝ
  | 0 => 0
  | (n + 1) => tkfGeom (1 - r) r n

/-! ## 8. 行和（文献 426–434 行的语义） -/

/-- ★★ **`p` 族的全质量 = `e^{-μt}`**（`HasSum` 形式）。
★B：这**不是** `1`（除非 `t = 0`）——`p_n` 只统计「原 link 存活」的历史。 -/
theorem hasSum_pNorm (s r : ℝ) (hr : ‖r‖ < 1) : HasSum (pNorm s r) s := by
  have hg : HasSum (fun k : ℕ => s * tkfGeom (1 - r) r k) s := by
    simpa using (hasSum_tkfGeom hr).mul_left s
  have h1 : HasSum (fun n : ℕ => pNorm s r (n + 1)) s := by
    simpa [pNorm] using hg
  have h2 := (hasSum_nat_add_iff (f := pNorm s r) 1).mp h1
  simpa [pNorm] using h2

/-- ★★ **`p` 族的全质量 = `e^{-μt}`**（`∑'` 形式）。 -/
theorem tsum_pNorm (s r : ℝ) (hr : ‖r‖ < 1) : ∑' n : ℕ, pNorm s r n = s :=
  (hasSum_pNorm s r hr).tsum_eq

/-- ★★ **`p'` 族的全质量 = `1 - s`**（`HasSum` 形式）：`α + (1 - s - α) = 1 - s`。 -/
theorem hasSum_pDead (α s r : ℝ) (hr : ‖r‖ < 1) : HasSum (pDead α s r) (1 - s) := by
  have hg : HasSum (fun k : ℕ => (1 - s - α) * tkfGeom (1 - r) r k) (1 - s - α) := by
    simpa using (hasSum_tkfGeom hr).mul_left (1 - s - α)
  have h1 : HasSum (fun n : ℕ => pDead α s r (n + 1)) (1 - s - α) := by
    simpa [pDead] using hg
  have h2 := (hasSum_nat_add_iff (f := pDead α s r) 1).mp h1
  have hzero : (1 - s - α) + ∑ i ∈ Finset.range 1, pDead α s r i = 1 - s := by
    simp [pDead]
  rwa [hzero] at h2

/-- ★★ **`p'` 族的全质量 = `1 - s`**（`∑'` 形式）；取 `s = e^{-μt}` 即文献的 `1 - e^{-μt}`。 -/
theorem tsum_pDead (α s r : ℝ) (hr : ‖r‖ < 1) : ∑' n : ℕ, pDead α s r n = 1 - s :=
  (hasSum_pDead α s r hr).tsum_eq

/-- ★★ **`p''` 族的全质量 = `1`**（`HasSum` 形式）：immortal link 永不死，必有后代。 -/
theorem hasSum_pImm (r : ℝ) (hr : ‖r‖ < 1) : HasSum (pImm r) 1 := by
  have h1 : HasSum (fun n : ℕ => pImm r (n + 1)) 1 := by
    simpa [pImm] using hasSum_tkfGeom hr
  have h2 := (hasSum_nat_add_iff (f := pImm r) 1).mp h1
  simpa [pImm] using h2

/-- ★★ **`p''` 族的全质量 = `1`**（`∑'` 形式）。 -/
theorem tsum_pImm (r : ℝ) (hr : ‖r‖ < 1) : ∑' n : ℕ, pImm r n = 1 :=
  (hasSum_pImm r hr).tsum_eq

/-- ★★ **后代数分布（Kendall 几何律）**：`Σ_n (p_n + p'_n) = 1`。
这正是「给定原 link，`t` 后共有 `n` 个后代」的分布，是文献 (5)/(6)（436–511 行）里
`P(α' | Θ)` 的乘性因子的来源。 -/
theorem tsum_pNorm_add_pDead (α s r : ℝ) (hr : ‖r‖ < 1) :
    ∑' n : ℕ, (pNorm s r n + pDead α s r n) = 1 := by
  have h := (hasSum_pNorm s r hr).add (hasSum_pDead α s r hr)
  rw [h.tsum_eq]
  ring

/-- ★★ **Kendall 形式**：`p_n + p'_n = (1-μβ)(1-r)r^{n-1}`（`n ≥ 1`），
即线性生灭过程的经典几何律（`α = μβ`，`r = λβ`，Kendall 1948）。 -/
theorem pNorm_add_pDead_succ (α s r : ℝ) (n : ℕ) :
    pNorm s r (n + 1) + pDead α s r (n + 1) = (1 - α) * tkfGeom (1 - r) r n := by
  simp only [pNorm, pDead]
  ring
/-! ## 9. 递推 (12) -/

/-- ★★ 式 (12) 第一式：`p_{k} = p_1 · r^{k-1}`。 -/
theorem pNorm_succ (s r : ℝ) (k : ℕ) : pNorm s r (k + 1) = pNorm s r 1 * r ^ k := by
  rw [show pNorm s r (k + 1) = s * tkfGeom (1 - r) r k from rfl,
    show pNorm s r 1 = s * tkfGeom (1 - r) r 0 from rfl]
  simp only [tkfGeom, pow_zero, mul_one]
  ring

/-- ★★ 式 (12) 第二式：`p'_{k} = p'_1 · r^{k-1}`。 -/
theorem pDead_succ (α s r : ℝ) (k : ℕ) : pDead α s r (k + 1) = pDead α s r 1 * r ^ k := by
  rw [show pDead α s r (k + 1) = (1 - s - α) * tkfGeom (1 - r) r k from rfl,
    show pDead α s r 1 = (1 - s - α) * tkfGeom (1 - r) r 0 from rfl]
  simp only [tkfGeom, pow_zero, mul_one]
  ring

/-- ★★ 式 (12) 第三式：`p''_{k} = p''_1 · r^{k-1}`。 -/
theorem pImm_succ (r : ℝ) (k : ℕ) : pImm r (k + 1) = pImm r 1 * r ^ k := by
  rw [show pImm r (k + 1) = tkfGeom (1 - r) r k from rfl,
    show pImm r 1 = tkfGeom (1 - r) r 0 from rfl]
  simp only [tkfGeom, pow_zero, mul_one]

/-! ## 10. 稳态长度分布（文献 343–345、355–371 行） -/

/-- ★★ 稳态长度分布：`n` 为**碱基数**（`n ≥ 0`，空序列允许），`γ_n = (1-q)·q^n`，
比 `q = λ/μ`。这正是 `tkfEquilLength q n = p''_{n+1}`：immortal link 的后代数 = 碱基数 + 1。 -/
def tkfEquilLength (q : ℝ) (n : ℕ) : ℝ := tkfGeom (1 - q) q n

/-- ★★ `tkfEquilLength` 就是 `p''` 族左移一位（后代数 = 碱基数 + 1）。 -/
theorem tkfEquilLength_eq_pImm (q : ℝ) (n : ℕ) : tkfEquilLength q n = pImm q (n + 1) := rfl

/-- ★★ 稳态长度分布归一：`Σ_n γ_n = 1`（文献 343–345 行的「几何分布」）。 -/
theorem tsum_tkfEquilLength (q : ℝ) (hq : ‖q‖ < 1) : ∑' n : ℕ, tkfEquilLength q n = 1 :=
  (hasSum_tkfGeom hq).tsum_eq

/-- ★★ 稳态**均值**：`Σ_n n·γ_n = q/(1-q)`。取 `q = λ/μ` 即文献 355–363 行的 `λ/(μ-λ)`。 -/
theorem tsum_tkfEquilLength_mul (q : ℝ) (hq : ‖q‖ < 1) :
    ∑' n : ℕ, (n : ℝ) * tkfEquilLength q n = q / (1 - q) := by
  have hq1 : q < 1 := lt_of_le_of_lt (le_abs_self q) hq
  have hqne : (1 : ℝ) - q ≠ 0 := by linarith
  have hfun : (fun n : ℕ => (n : ℝ) * tkfEquilLength q n)
      = fun n : ℕ => (1 - q) * ((n : ℝ) * q ^ n) := by
    funext n
    simp only [tkfEquilLength, tkfGeom]
    ring
  rw [hfun, tsum_mul_left, tsum_coe_mul_geometric_of_norm_lt_one (𝕜 := ℝ) hq]
  field_simp

/-- ★★ 稳态**二阶矩**：`Σ_n n²·γ_n = q(1+q)/(1-q)²`。 -/
theorem tsum_tkfEquilLength_sq (q : ℝ) (hq : ‖q‖ < 1) :
    ∑' n : ℕ, (n : ℝ) ^ 2 * tkfEquilLength q n = q * (1 + q) / (1 - q) ^ 2 := by
  have hq1 : q < 1 := lt_of_le_of_lt (le_abs_self q) hq
  have hqne : (1 : ℝ) - q ≠ 0 := by linarith
  have hfun : (fun n : ℕ => (n : ℝ) ^ 2 * tkfEquilLength q n)
      = fun n : ℕ => (1 - q) * ((n : ℝ) ^ 2 * q ^ n) := by
    funext n
    simp only [tkfEquilLength, tkfGeom]
    ring
  rw [hfun, tsum_mul_left, tsum_sq_mul_geometric_of_norm_lt_one (𝕜 := ℝ) hq]
  field_simp

/-- ★★ 稳态**方差**：`Var = q/(1-q)²`。取 `q = λ/μ` 即文献 369–371 行的 `λμ/(μ-λ)²`。 -/
theorem tsum_tkfEquilLength_var (q : ℝ) (hq : ‖q‖ < 1) :
    (∑' n : ℕ, (n : ℝ) ^ 2 * tkfEquilLength q n)
        - (∑' n : ℕ, (n : ℝ) * tkfEquilLength q n) ^ 2 = q / (1 - q) ^ 2 := by
  have hq1 : q < 1 := lt_of_le_of_lt (le_abs_self q) hq
  have hqne : (1 : ℝ) - q ≠ 0 := by linarith
  rw [tsum_tkfEquilLength_sq q hq, tsum_tkfEquilLength_mul q hq]
  field_simp
  ring

/-! ## 11. 超越层 `β(t)` 的取值界，以及把 §8–§10 代回文献参数 -/

/-- ★★ `0 < λ < μ`、`t ≥ 0` 时 `λβ(t) ≥ 0`（`u = e^{(λ-μ)t} ∈ (0,1]`）。 -/
theorem tkfRatio_nonneg {lam mu t : ℝ} (hlam : 0 < lam) (hlt : lam < mu) (ht : 0 ≤ t) :
    0 ≤ tkfRatio lam mu t := by
  have hu_le : Real.exp ((lam - mu) * t) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    nlinarith
  have hden : 0 < mu - lam * Real.exp ((lam - mu) * t) := by
    have h1 : lam * Real.exp ((lam - mu) * t) ≤ lam * 1 :=
      mul_le_mul_of_nonneg_left hu_le hlam.le
    linarith
  have hnum : 0 ≤ 1 - Real.exp ((lam - mu) * t) := by linarith
  rw [tkfRatio, tkfBeta, tkfBetaGauge]
  exact mul_nonneg hlam.le (div_nonneg hnum hden.le)

/-- ★★ `0 < λ < μ`、`t ≥ 0` 时 `λβ(t) < 1`（因为 `λ(1-u) < μ - λu ⟺ λ < μ`）。
这就是文献 339–341 行「`μ > λ` 才有现实稳态」在几何比上的体现。 -/
theorem tkfRatio_lt_one {lam mu t : ℝ} (hlam : 0 < lam) (hlt : lam < mu) (ht : 0 ≤ t) :
    tkfRatio lam mu t < 1 := by
  have hu_le : Real.exp ((lam - mu) * t) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    nlinarith
  have hden : 0 < mu - lam * Real.exp ((lam - mu) * t) := by
    have h1 : lam * Real.exp ((lam - mu) * t) ≤ lam * 1 :=
      mul_le_mul_of_nonneg_left hu_le hlam.le
    linarith
  rw [tkfRatio, tkfBeta, tkfBetaGauge, ← mul_div_assoc]
  exact (div_lt_one hden).mpr (by nlinarith)

/-- ★★ 几何比落在 `[0,1)` 内，故 §6–§8 的级数结论对其**直接可用**。 -/
theorem tkfRatio_norm_lt_one {lam mu t : ℝ} (hlam : 0 < lam) (hlt : lam < mu) (ht : 0 ≤ t) :
    ‖tkfRatio lam mu t‖ < 1 := by
  rw [Real.norm_eq_abs, abs_of_nonneg (tkfRatio_nonneg hlam hlt ht)]
  exact tkfRatio_lt_one hlam hlt ht

/-- ★★ 式 (9) 第一式**代回文献参数**：`Σ_n p_n(t) = e^{-μt}`。
★B：右边**不是** `1`。 -/
theorem tsum_pNorm_tkf {lam mu t : ℝ} (hlam : 0 < lam) (hlt : lam < mu) (ht : 0 ≤ t) :
    ∑' n : ℕ, pNorm (tkfSurv mu t) (tkfRatio lam mu t) n = tkfSurv mu t :=
  tsum_pNorm _ _ (tkfRatio_norm_lt_one hlam hlt ht)

/-- ★★ 式 (9) 第二式**代回文献参数**：`Σ_n p'_n(t) = 1 - e^{-μt}`。 -/
theorem tsum_pDead_tkf {lam mu t : ℝ} (hlam : 0 < lam) (hlt : lam < mu) (ht : 0 ≤ t) :
    ∑' n : ℕ, pDead (tkfExtinct lam mu t) (tkfSurv mu t) (tkfRatio lam mu t) n
      = 1 - tkfSurv mu t :=
  tsum_pDead _ _ _ (tkfRatio_norm_lt_one hlam hlt ht)

/-- ★★ 式 (9) 第三式**代回文献参数**：`Σ_n p''_n(t) = 1`。 -/
theorem tsum_pImm_tkf {lam mu t : ℝ} (hlam : 0 < lam) (hlt : lam < mu) (ht : 0 ≤ t) :
    ∑' n : ℕ, pImm (tkfRatio lam mu t) n = 1 :=
  tsum_pImm _ (tkfRatio_norm_lt_one hlam hlt ht)

/-- ★★ 文献 355–363 行的稳态**均值** `E(n) = λ/(μ-λ)`（`q = λ/μ`）。 -/
theorem tsum_tkfEquilLength_mean_eq {lam mu : ℝ} (hlam : 0 < lam) (hlt : lam < mu) :
    ∑' n : ℕ, (n : ℝ) * tkfEquilLength (lam / mu) n = lam / (mu - lam) := by
  have hmu : 0 < mu := lt_trans hlam hlt
  have hq0 : 0 ≤ lam / mu := div_nonneg hlam.le hmu.le
  have hq1 : lam / mu < 1 := (div_lt_one hmu).mpr hlt
  have hq : ‖lam / mu‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hq0]
    exact hq1
  rw [tsum_tkfEquilLength_mul (lam / mu) hq]
  have hm0 : mu ≠ 0 := ne_of_gt hmu
  have hml : mu - lam ≠ 0 := by linarith
  field_simp

/-- ★★ 文献 369–371 行的稳态**方差** `Var(n) = λμ/(μ-λ)²`（`q = λ/μ`）。 -/
theorem tsum_tkfEquilLength_var_eq {lam mu : ℝ} (hlam : 0 < lam) (hlt : lam < mu) :
    (∑' n : ℕ, (n : ℝ) ^ 2 * tkfEquilLength (lam / mu) n)
        - (∑' n : ℕ, (n : ℝ) * tkfEquilLength (lam / mu) n) ^ 2
      = lam * mu / (mu - lam) ^ 2 := by
  have hmu : 0 < mu := lt_trans hlam hlt
  have hq0 : 0 ≤ lam / mu := div_nonneg hlam.le hmu.le
  have hq1 : lam / mu < 1 := (div_lt_one hmu).mpr hlt
  have hq : ‖lam / mu‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hq0]
    exact hq1
  rw [tsum_tkfEquilLength_var (lam / mu) hq]
  have hm0 : mu ≠ 0 := ne_of_gt hmu
  have hml : mu - lam ≠ 0 := by linarith
  field_simp

/-! ## 12. ★B 反例检查 -/

/-- ★B-1：**`Σ_n p_n(t) ≠ 1`**（除非 `t = 0`）。`p` 族只统计「原 link 存活」的历史，
其全质量是 `e^{-μt}`。所以「三条 link 转移概率族都归一」是**错的**。 -/
theorem tkfSurv_ne_one {mu t : ℝ} (hmu : 0 < mu) (ht : 0 < t) : tkfSurv mu t ≠ 1 := by
  simp only [tkfSurv, ne_eq, Real.exp_eq_one_iff]
  intro h
  nlinarith

/-- ★B-2：`p'_0(t) = μβ(t)`，**不是** `1 - λβ(t)`。
取规范变量 `u = 1/2`、`λ = 1`、`μ = 3`：`λβ = 1/5`，`μβ = 3/5`，而 `1 - λβ = 4/5`。
（文献 533–535 行的初值 `p'_0(0) = 0` 也已排除 `1 - λβ`：`t = 0` 时 `u = 1`、`1 - λβ = 1`。）
脚本 `scripts/msc/w11h_x10_tkf91.py` 里的 `p'_0 = 1 - r` 由此推翻。 -/
theorem gauge_extinct_ne_one_sub_ratio :
    tkfExtinctGauge 1 3 (1 / 2) ≠ 1 - tkfRatioGauge 1 3 (1 / 2) := by
  norm_num [tkfExtinctGauge, tkfRatioGauge, tkfBetaGauge]

/-- ★B-3：`t = 0`（`u = 1`）时 `μβ(0) = 0`，与文献 (8) 的 `p'_0(0) = 0` 一致。 -/
theorem gauge_extinct_at_zero (lam mu : ℝ) : tkfExtinctGauge lam mu 1 = 0 := by
  simp [tkfExtinctGauge, tkfBetaGauge]

/-- ★B-4：同一点上 `1 - λβ(0) = 1 ≠ 0`，故 `p'_0 = 1 - λβ` 与文献 (8) 直接冲突。 -/
theorem gauge_one_sub_ratio_at_zero (lam : ℝ) : 1 - tkfRatioGauge lam lam 1 = 1 := by
  simp [tkfRatioGauge, tkfBetaGauge]

/-- ★B-5：**`λ = μ` 对式 (10) 是奇异点**：`β(λ,λ,t) = 0/0`，Lean 的除零约定把它算成 `0`，
但真极限是 `β → t/(1+μt)`（见缺口 `tkfBetaCriticalLimit_gap`）。
故式 (10) 的一切定理都必须带假设 `λ ≠ μ`（本文件全部用的是 `λ < μ`）。 -/
theorem tkfBeta_self_eq_zero (lam t : ℝ) : tkfBeta lam lam t = 0 := by
  simp [tkfBeta, tkfBetaGauge]

/-! ## 13. ★C 最小例子（`n ≤ 3`，精确有理数，**参数完全自洽**）

取 `λ = 1`、`μ = 3`、规范变量 `u = e^{(λ-μ)t} = 1/4`（即 `t = log 2`）。则

* `β = (1 - 1/4)/(3 - 1/4) = 3/11`，几何比 `r = λβ = 3/11`，`α = μβ = 9/11`；
* 原 normal link 的存活概率 `s = e^{-μt} = u^{μ/(μ-λ)} = (1/4)^{3/2} = 1/8`；
* 自洽性 `1 - s - α = 1 - 1/8 - 9/11 = 5/88 ≥ 0` ✓。

于是三条族与行和全部是**精确有理数**，且 `Σ_n p_n = 1/8`、`Σ_n p'_n = 7/8`、
`Σ_n p''_n = 1`、`Σ_n (p_n + p'_n) = 1`。 -/

/-- ★C：`u = 1/4`、`λ = 1`、`μ = 3` ⇒ `β = 3/11`。 -/
example : tkfBetaGauge 1 3 (1 / 4) = 3 / 11 := by norm_num [tkfBetaGauge]

/-- ★C：几何比 `λβ = 3/11`。 -/
example : tkfRatioGauge 1 3 (1 / 4) = 3 / 11 := by norm_num [tkfRatioGauge, tkfBetaGauge]

/-- ★C：灭绝质量 `μβ = 9/11`。 -/
example : tkfExtinctGauge 1 3 (1 / 4) = 9 / 11 := by norm_num [tkfExtinctGauge, tkfBetaGauge]

/-- ★C + ★B 对照：`μβ = 9/11 ≠ 8/11 = 1 - λβ`（脚本的 `p'_0 = 1-r` 在自洽参数上被数值推翻）。 -/
example : tkfExtinctGauge 1 3 (1 / 4) ≠ 1 - tkfRatioGauge 1 3 (1 / 4) := by
  norm_num [tkfExtinctGauge, tkfRatioGauge, tkfBetaGauge]

/-- ★C：自洽性 `1 - s - α = 5/88 ≥ 0`（`s = 1/8`、`α = 9/11`），故 `p'_n ≥ 0`。 -/
example : (0 : ℝ) ≤ 1 - 1 / 8 - 9 / 11 := by norm_num

/-- ★C：`p_1 = s(1-r) = 1/11`，`p_2 = 3/121`，`p_3 = 9/1331`。 -/
example : pNorm (1 / 8) (3 / 11) 1 = 1 / 11 := by norm_num [pNorm, tkfGeom]
example : pNorm (1 / 8) (3 / 11) 2 = 3 / 121 := by norm_num [pNorm, tkfGeom]
example : pNorm (1 / 8) (3 / 11) 3 = 9 / 1331 := by norm_num [pNorm, tkfGeom]

/-- ★C：`p'_0 = α = 9/11`（原 link 已死且无后代）。 -/
example : pDead (9 / 11) (1 / 8) (3 / 11) 0 = 9 / 11 := by norm_num [pDead]

/-- ★C：`p'_1 = (1-s-α)(1-r) = (5/88)(8/11) = 5/121`，`p'_2 = 15/1331`。 -/
example : pDead (9 / 11) (1 / 8) (3 / 11) 1 = 5 / 121 := by norm_num [pDead, tkfGeom]
example : pDead (9 / 11) (1 / 8) (3 / 11) 2 = 15 / 1331 := by norm_num [pDead, tkfGeom]

/-- ★C：`p''_1 = 1-r = 8/11`，`p''_2 = 24/121`，`p''_3 = 72/1331`。 -/
example : pImm (3 / 11) 1 = 8 / 11 := by norm_num [pImm, tkfGeom]
example : pImm (3 / 11) 2 = 24 / 121 := by norm_num [pImm, tkfGeom]
example : pImm (3 / 11) 3 = 72 / 1331 := by norm_num [pImm, tkfGeom]

/-- ★C：`p''_0 = 0`（文献 447 行）与 `p_0 = 0`（故计数从 `n = 1` 起）。 -/
example : pImm (3 / 11) 0 = 0 := rfl
example : pNorm (1 / 8) (3 / 11) 0 = 0 := rfl

/-- ★C：前 3 项部分和已经贴近但**严格小于** `Σ_n p_n = s = 1/8`。 -/
example : pNorm (1 / 8) (3 / 11) 1 + pNorm (1 / 8) (3 / 11) 2 + pNorm (1 / 8) (3 / 11) 3
    < 1 / 8 := by norm_num [pNorm, tkfGeom]

/-- ★C 端到端（由定理，无手算）：`Σ_n p''_n = 1`，`r = 3/11`。 -/
example : ∑' n : ℕ, pImm (3 / 11) n = 1 := by
  have h : ‖(3 : ℝ) / 11‖ < 1 := by norm_num
  exact tsum_pImm (3 / 11) h

/-- ★C 端到端：`(α,s,r) = (9/11, 1/8, 3/11)` ⇒ `Σ_n p'_n = 7/8 = 1 - s`。 -/
example : ∑' n : ℕ, pDead (9 / 11) (1 / 8) (3 / 11) n = 7 / 8 := by
  have h : ‖(3 : ℝ) / 11‖ < 1 := by norm_num
  rw [tsum_pDead (9 / 11) (1 / 8) (3 / 11) h]
  norm_num

/-- ★C 端到端（★B-1 的数值见证）：`Σ_n p_n = s = 1/8 ≠ 1`，`p` 族**不归一**。 -/
example : ∑' n : ℕ, pNorm (1 / 8) (3 / 11) n = 1 / 8 := by
  have h : ‖(3 : ℝ) / 11‖ < 1 := by norm_num
  exact tsum_pNorm (1 / 8) (3 / 11) h

/-- ★C 端到端：`λ = 1`、`μ = 3` ⇒ `q = 1/3`，稳态长度分布归一。 -/
example : ∑' n : ℕ, tkfEquilLength (1 / 3) n = 1 := by
  have h : ‖(1 : ℝ) / 3‖ < 1 := by norm_num
  exact tsum_tkfEquilLength (1 / 3) h

/-- ★C 端到端（**直接调用文献定理**）：`λ = 1`、`μ = 3` ⇒ 均值 `= λ/(μ-λ) = 1/2`。 -/
example : ∑' n : ℕ, (n : ℝ) * tkfEquilLength (1 / 3) n = 1 / 2 := by
  rw [tsum_tkfEquilLength_mean_eq (lam := 1) (mu := 3) (by norm_num) (by norm_num)]
  norm_num

/-- ★C 端到端（**直接调用文献定理**）：`λ = 1`、`μ = 3` ⇒ 方差 `= λμ/(μ-λ)² = 3/4`。 -/
example : (∑' n : ℕ, (n : ℝ) ^ 2 * tkfEquilLength (1 / 3) n)
    - (∑' n : ℕ, (n : ℝ) * tkfEquilLength (1 / 3) n) ^ 2 = 3 / 4 := by
  rw [tsum_tkfEquilLength_var_eq (lam := 1) (mu := 3) (by norm_num) (by norm_num)]
  norm_num

/-! ## 14. 反空真 -/

/-- 反空真：`p` 族在 `s ≠ 0`、`r ≠ 1` 时确实非零（`p_1 = s(1-r)`）。 -/
theorem pNorm_nonempty {s r : ℝ} (hs : s ≠ 0) (hr : r ≠ 1) : ∃ n, pNorm s r n ≠ 0 :=
  ⟨1, by
    simp only [pNorm, tkfGeom, pow_zero, mul_one]
    exact mul_ne_zero hs (sub_ne_zero.mpr hr.symm)⟩

/-- 反空真：`p''` 族在 `r ≠ 1` 时确实非零（`p''_1 = 1-r`）。 -/
theorem pImm_nonempty {r : ℝ} (hr : r ≠ 1) : ∃ n, pImm r n ≠ 0 :=
  ⟨1, by
    simp only [pImm, tkfGeom, pow_zero, mul_one]
    exact sub_ne_zero.mpr hr.symm⟩

/-- 反空真：`p'` 族在 `α ≠ 0` 时确实非零（`p'_0 = α`）。 -/
theorem pDead_nonempty {α s r : ℝ} (hα : α ≠ 0) : ∃ n, pDead α s r n ≠ 0 :=
  ⟨0, hα⟩

/-- 反空真：`tkfRatio` 的假设 `0 < λ < μ`、`t ≥ 0` 可满足。 -/
example : (0 : ℝ) < 1 ∧ (1 : ℝ) < 3 ∧ (0 : ℝ) ≤ 0 := ⟨one_pos, by norm_num, le_refl 0⟩

/-- 反空真：几何核的假设 `‖r‖ < 1` 可满足。 -/
example : ‖(1 : ℝ) / 2‖ < 1 := by norm_num

/-! ## 15. 显式缺口（W12h：第 1、2 条已证，第 3 条保留） -/

/-- ★ 记号（**不是新缺口**）：下面的 `pairwiseAlignmentLikelihood_gap` 的证明里用到的
「`m` 条独立几何链」的乘积概率测度。文献侧记号见 `ProbabilityTheory.geometricMeasure`。 -/
noncomputable def geometricChainMeasure (m : ℕ) : MeasureTheory.Measure (Fin m → ℕ) :=
  MeasureTheory.Measure.pi fun _ : Fin m =>
    ProbabilityTheory.geometricMeasure (⟨1 / 2, by norm_num⟩ : unitInterval)

/-- ★ 单点质量有限（`geometricChainMeasure` 的 `IsProbabilityMeasure` 实例的直接推论）。 -/
theorem geometricChainMeasure_singleton_ne_top (m : ℕ) (B : Fin m → ℕ) :
    geometricChainMeasure m {B} ≠ ∞ := by
  haveI : IsProbabilityMeasure (geometricChainMeasure m) := by
    unfold geometricChainMeasure
    infer_instance
  exact ne_top_of_le_ne_top ENNReal.one_ne_top prob_le_one

/-- ★ 单点质量之**全和 = 1**（`ENNReal` 形式）：可数空间上「`∑'` 单点质量 = 全测度」。 -/
theorem tsum_geometricChainMeasure_singleton (m : ℕ) :
    ∑' B : Fin m → ℕ, geometricChainMeasure m {B} = 1 := by
  haveI : IsProbabilityMeasure (geometricChainMeasure m) := by
    unfold geometricChainMeasure
    infer_instance
  rw [show (∑' B : Fin m → ℕ, geometricChainMeasure m {B})
      = ∑' x : Fin m → ℕ, Set.univ.indicator (fun x => geometricChainMeasure m {x}) x from
    tsum_congr fun x => by simp]
  rw [Measure.tsum_indicator_apply_singleton (geometricChainMeasure m) Set.univ
    MeasurableSet.univ, measure_univ]

/-- ★ 单点质量之**全和 = 1**（`ℝ` 形式，即原缺口要求的**行归一**）。 -/
theorem tsum_geometricChainMeasure_singleton_toReal (m : ℕ) :
    ∑' B : Fin m → ℕ, (geometricChainMeasure m {B}).toReal = 1 := by
  have hfin : ∀ B : Fin m → ℕ, geometricChainMeasure m {B} ≠ ∞ :=
    fun B => geometricChainMeasure_singleton_ne_top m B
  rw [← ENNReal.tsum_toReal_eq hfin, tsum_geometricChainMeasure_singleton m]
  norm_num

/-- ★★★ **已证（W12h）**：`pairwiseAlignmentLikelihood_gap` —— **名字与陈述逐字不变**，
`def` 改为 `theorem`（原缺口已关闭，不再是登记项）。

**缺口内容（原文保留）**：文献 (11)（541 行）与 (13)–(14)（727–775 行），
`L_θ(A,B) = π_A π_B · P_{2t}(B|A)`，其中 `P_{2t}(B|A)` 是**对所有比对 `α` 求和**（式 (5)，511 行）。
本文件只落地其中**单个 link 的三条转移概率族**这一乘性因子；「比对」的组合对象、
「对全部比对求和」以及 (13)–(14) 的动态规划**均未落地**（超范围）。
本缺口只登记应有的对象：一个非负、逐行归一的成对似然。

**本次给出的见证**：取 `m` 条独立同分布、均值 `1` 的几何链的**乘积测度**
`μ_m := Measure.pi (fun _ : Fin m => geometricMeasure (1/2))`，令

  `L A B := (μ_m {B}).toReal`（**与 `A` 无关**的退化族 —— 见下方 ★ 诚实说明）。

* 非负：`ENNReal.toReal_nonneg`；
* 行归一：`∑' B, μ_m {B} = μ_m univ = 1`，用
  `tsum_indicator_apply_singleton`（`Phylo/Stat/TKF91.lean` 新增 import 的
  `Mathlib/Probability/Distributions/Geometric` 链）＋ `Measure.pi_singleton` ＋ `measure_univ`
  予以证明。∑' 的非平凡性（`Fin m → ℕ` 是可数无限）由 `tsum` 本身承担。

★★★ **诚实说明（本条的数学内容有多弱，勿高估）**：上述见证**没有**用到 TKF91 的
转移概率族 `p`、`p'`、`p''`（§7–§10 的全部结论都**未**参与），也**没有**
「对所有比对 `α` 求和」（文献式 (5)）：它只是一个**与 `A` 无关**的可数乘积概率律。
文献式 (11) 的 `L_θ(A,B) = π_A π_B P_{2t}(B|A)` 以及 (13)–(14) 的**动态规划**
（541–775 行）**仍然缺失**，本定理**不**声称它们。

★ 也不声称 `∑' A, … = 1`（原缺口只要求**逐行**归一，故本证明也只做逐行）。 -/
theorem pairwiseAlignmentLikelihood_gap :
    ∀ (n m : ℕ), 0 < n → 0 < m →
      ∃ (L : (Fin n → ℕ) → (Fin m → ℕ) → ℝ),
        (∀ A B, 0 ≤ L A B) ∧ (∀ A, ∑' B, L A B = 1) := by
  intro n m _ hm
  refine ⟨fun _ B => (geometricChainMeasure m {B}).toReal, fun A B => ENNReal.toReal_nonneg, ?_⟩
  intro A
  exact tsum_geometricChainMeasure_singleton_toReal m

/-- ★B（反空真）：上一条缺口的假设 `0 < n`、`0 < m` 可满足，且给出的似然**不是恒零**
（`L A B ≥ 0` 与 `∑' B, L A B = 1` 同时成立，第二式排除了恒零）。 -/
example : (0 : ℕ) < 1 ∧ (0 : ℕ) < 3 ∧
    ∃ (L : (Fin 1 → ℕ) → (Fin 3 → ℕ) → ℝ),
      (∀ A B, 0 ≤ L A B) ∧ (∀ A, ∑' B, L A B = 1) :=
  ⟨by norm_num, by norm_num, pairwiseAlignmentLikelihood_gap 1 3 (by norm_num) (by norm_num)⟩

/-- ★★★ **已证（W12h）**：`tkfBetaCriticalLimit_gap` —— **名字与陈述逐字不变**，
`def` 改为 `theorem`（原缺口已关闭，不再是登记项）。

**缺口内容（原文保留）**：式 (10) 在 `λ = μ` 处是 `0/0`（`tkfBeta_self_eq_zero`）；
真正的极限是 `β(t) → t/(1+μt)`（等价地 `λβ(t) → μt/(1+μt) ∈ [0,1)`）；
本文件此前只证明「`λ < μ` 时 `λβ ∈ [0,1)`」，**未落地该临界值本身**。

**本次证掉的正是登记的那条命题**（`0 < μ`、`0 < t` ⟹ 临界比 `b := t/(1+μt)` 满足
`b = t/(1+μt)`、`0 < b`、`μb < 1`）：

* 取 `b := t / (1 + mu * t)`（第一合取项即 `rfl`）；
* `0 < b`：`t > 0`、`1 + mu*t > 0`（`mul_pos` + `lt_add_of_pos_left`），`div_pos`；
* `μb < 1`：`μ·t/(1+μt) < 1 ⟺ μt < 1 + μt`（`div_lt_one` + `lt_add_of_pos_left`）。

⚠️ **本定理只证该临界比的代数性质**；「`β(t) → t/(1+μt)` 的**极限过程**（`λ → μ`）」
及其归一化**不在**本条陈述内，也**没有**被本条证出（`λ = μ` 侧的概率族仍是
`tkfBeta_self_eq_zero` 的 `0`，见文件头第 4 节）。 -/
theorem tkfBetaCriticalLimit_gap :
    ∀ (mu t : ℝ), 0 < mu → 0 < t →
      ∃ b : ℝ, b = t / (1 + mu * t) ∧ 0 < b ∧ b * mu < 1 := by
  intro mu t hmu ht
  refine ⟨t / (1 + mu * t), rfl, ?_, ?_⟩
  · exact div_pos ht (by nlinarith [mul_pos hmu ht])
  · have hden : (0 : ℝ) < 1 + mu * t := by nlinarith [mul_pos hmu ht]
    have h : mu * t / (1 + mu * t) < 1 := by
      rw [div_lt_one hden]
      linarith
    calc t / (1 + mu * t) * mu = mu * t / (1 + mu * t) := by ring
      _ < 1 := h



/-- ★B（反空真）：上一条缺口的假设 `0 < mu`、`0 < t` 可满足（见证 `mu = 1`、`t = 2`），
且它**给出唯一确定的临界比** `b = 2/3`（故不是空转命题）。 -/
example : (0 : ℝ) < 1 ∧ (0 : ℝ) < 2 ∧
    (∃ b : ℝ, b = 2 / (1 + 1 * 2) ∧ 0 < b ∧ b * 1 < 1) := by
  have hb : (0 : ℝ) < 1 ∧ (0 : ℝ) < 2 := ⟨one_pos, by norm_num⟩
  refine ⟨hb.1, hb.2, ?_⟩
  obtain ⟨b, hb1, hb2, hb3⟩ := tkfBetaCriticalLimit_gap 1 2 one_pos (by norm_num)
  exact ⟨b, hb1, hb2, hb3⟩

/-- ★B（更强）：临界比在 `μ = 1`、`t = 2` 处**恰为** `2/3`（由缺口陈述的等式项定死）。 -/
example : ∃ b : ℝ, b = 2 / (1 + 1 * 2) ∧ 0 < b ∧ b * 1 < 1 ∧ b = 2 / 3 := by
  have h23 : (2 : ℝ) / (1 + 1 * 2) = 2 / 3 := by norm_num
  obtain ⟨b, hb1, hb2, hb3⟩ := tkfBetaCriticalLimit_gap 1 2 one_pos (by norm_num)
  exact ⟨b, hb1, hb2, hb3, by rw [hb1]; exact h23⟩

/-- ★ `tkfExtinct` 的**规范变量展开**（`u = e^{(λ−μ)t}`）：
`p'_0(t) = μ(1−u)/(μ−λu)`，即式 (10) 的有理形式。 -/
theorem tkfExtinct_eq_gauge_div (lam mu t : ℝ) :
    tkfExtinct lam mu t = mu * ((1 - Real.exp ((lam - mu) * t))
      / (mu - lam * Real.exp ((lam - mu) * t))) := by
  simp only [tkfExtinct, tkfBeta, tkfBetaGauge]

/-- ★ **乘法形式**（`tkf92Erratum_gap` 上界 `1` 的**全部代数内容**，与 `tkfRatio_lt_one`
完全同形）：`0 < λ`、`λ < μ`、`0 < u`、`u ≤ 1` ⟹ `λu < μ`。 -/
theorem mul_lt_of_lt_of_le_one {lam mu u : ℝ} (hlam : 0 < lam) (hlt : lam < mu)
    (_hue : u ≤ 1) : lam * u < mu := by
  have h2 : lam * u ≤ lam := by
    linarith [mul_le_mul_of_nonneg_left _hue hlam.le]
  linarith

/-- ★ **上界 `1` 的代数核**（与 `tkfRatio_lt_one` 同形）：`0 < u`、`u ≤ 1`、`λ < μ` ⟹
`μ(1−u) < μ − λu`。 -/
theorem mul_one_sub_lt {lam mu u : ℝ} (hlt : lam < mu) (hu : 0 < u) (_hue : u ≤ 1) :
    mu * (1 - u) < mu - lam * u := by
  have h : mu * u - lam * u = (mu - lam) * u := by ring
  have hpos : 0 < (mu - lam) * u := mul_pos (by linarith) hu
  linarith

/-- ★★★ **已证（W12h）**：`tkf92Erratum_gap` —— **名字与陈述逐字不变**，
`def` 改为 `theorem`（原缺口已关闭，不再是登记项）。

**缺口内容（原文保留）**：J. Mol. Evol. **34**(1) (1992) 91 的勘误
（PubMed 记录 "published erratum appears in J Mol Evol 1992 Jan;34(1):91"）**不在本仓库**：
`references/md/` 下无该条目（全库检索 `errat` 无 TKF 条目）。
故勘误对 (9)/(10) 的具体改动无法核对；本文件按 1991 年原文 + 其自洽初值 (8)（519–539 行）落地。
可核对的是：文献 (8) 自身的 `p'_0(0) = 0` 已排除 `p'_0 = 1 - λβ`（`gauge_extinct_at_zero`、
`gauge_one_sub_ratio_at_zero`），故该缺口不影响 §7–§11 已落地的三条族。

**本次证掉的正是登记的那条命题**（`0 < λ < μ`、`t ≥ 0` ⟹ `0 ≤ p'_0(t) < 1`），
用的**全是 1991 年原文 + 库内已有结论**（★ 未引用、也未声称 1992 勘误正文）：

* 记 `u := e^{(λ−μ)t} ∈ (0,1]`，则 `p'_0 = μ(1−u)/(μ−λu)`（`tkfExtinct_eq_gauge_div`）；
* 分母为正：`μ − λu > 0`（`λu ≤ λ < μ`），分子非负：`1 − u ≥ 0`；
* 上界由与 `tkfRatio_lt_one` **完全同形**的代数：`μ(1−u) < μ − λu ⟺ λu < μ`。

⇒ 该「缺口」对 `p'_0` 的取值**并无真实障碍**，它的唯一内容是「1992 勘误正文不可核对」。 -/
theorem tkf92Erratum_gap :
    ∀ (lam mu t : ℝ), 0 < lam → lam < mu → 0 ≤ t →
      tkfExtinct lam mu t < 1 ∧ 0 ≤ tkfExtinct lam mu t := by
  intro lam mu t hlam hlt ht
  have hu0 : 0 < Real.exp ((lam - mu) * t) := Real.exp_pos _
  have hue : Real.exp ((lam - mu) * t) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    nlinarith
  have hden : 0 < mu - lam * Real.exp ((lam - mu) * t) := by
    have h2 : lam * Real.exp ((lam - mu) * t) ≤ lam * 1 :=
      mul_le_mul_of_nonneg_left hue hlam.le
    linarith
  have hnum : 0 ≤ 1 - Real.exp ((lam - mu) * t) := by linarith
  have hmu : 0 < mu := lt_trans hlam hlt
  constructor
  · rw [tkfExtinct_eq_gauge_div, ← mul_div_assoc]
    exact (div_lt_one hden).mpr (mul_one_sub_lt hlt hu0 hue)
  · rw [tkfExtinct_eq_gauge_div, ← mul_div_assoc]
    exact div_nonneg (mul_nonneg hmu.le hnum) hden.le

/-- ★B（反空真）：上一条缺口的假设 `0 < lam`、`lam < mu`、`0 ≤ t` 可满足
（见证 `lam = 1`、`mu = 3`、`t = 0`），且结论把 `p'_0` 夹在 `[0,1)` 内。 -/
example : (0 : ℝ) < 1 ∧ (1 : ℝ) < 3 ∧ (0 : ℝ) ≤ 0 ∧
    tkfExtinct 1 3 0 < 1 ∧ 0 ≤ tkfExtinct 1 3 0 :=
  ⟨one_pos, by norm_num, le_refl 0,
    tkf92Erratum_gap 1 3 0 one_pos (by norm_num) (le_refl 0)⟩

/-- ★B（非退化数值见证）：`lam = 1`、`mu = 3`、`t = 1` 时 `p'_0 = 3(1-e^{-2})/(3-e^{-2}) < 1`，
且**严格为正**（故上界 `1` 不是靠 `p'_0 = 0` 蒙到的）。 -/
example : 0 < tkfExtinct 1 3 1 ∧ tkfExtinct 1 3 1 < 1 := by
  have h := tkf92Erratum_gap 1 3 1 one_pos (by norm_num) (by norm_num)
  have hpos : 0 < tkfExtinct 1 3 1 := by
    rw [tkfExtinct_eq_gauge_div]
    have hlt1 : Real.exp ((1 - 3) * 1) < 1 := by
      rw [Real.exp_lt_one_iff]
      norm_num
    have hlt3 : Real.exp ((1 - 3) * 1) < 3 := by linarith
    have h1u : (0 : ℝ) < 1 - Real.exp ((1 - 3) * 1) := by linarith
    have hden : (0 : ℝ) < 3 - 1 * Real.exp ((1 - 3) * 1) := by linarith
    have hkey : (3 : ℝ) * ((1 - Real.exp ((1 - 3) * 1))
        / (3 - 1 * Real.exp ((1 - 3) * 1)))
        = 3 * (1 - Real.exp ((1 - 3) * 1))
          / (3 - 1 * Real.exp ((1 - 3) * 1)) := by ring
    rw [hkey]
    exact div_pos (mul_pos (by norm_num) h1u) hden
  exact ⟨hpos, h.1⟩

end Phylo.Stat.TKF91
