/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Mathlib.Tactic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Phylo.Stat.CASTERWeights

/-!
# `Phylo.Stat.CASTERLM1` —— CASTER 的 LM1 模型：位点对权重与基因树层得分差闭式

文献：Zhang, Nielsen, Mirarab (2025), *Science* **387**(6737) eadk9688，
**Supplementary** `sm.tex`（本项目存于 `references/tex/Caster2025_Supplementary.tex`）：

| 内容 | `sm.tex` 行 |
|---|---|
| 权重表（LM1 行） | **367–375** |
| LM1 推导 | **1611–1700** |
| LM 可集总引理 | 303–330（陈述）/ 1161–1195（证明） |

本文件把附录 **LM1 模型下的命题 A**（基因树层的期望得分差闭式）
`E[w(ab|cd)] − E[w(ac|bd)] = 8 π_R²π_Y² e^{−λ L_T} (1 − e^{−2λ l_x})`
严格形式化并证明（★★★ `E_wLM1_ab_sub_ac`），并给出正性（★★ `E_wLM1_sub_pos`）。

代码里速率因子记作 `lam`（`λ` 是 Lean 4 的保留字），文档里写作 `λ`。

## 1. 记账方式（务必先读）

**LM1 是位点对（site pair）模型**：两个位点**独立**地沿基因树演化，
共用同一套平衡频率与转移矩阵（`sm.tex` 1623 行、1656–1662 行）。
附录的记号 `P(𝓁_a = RN)`（1623 行）表示
「物种 `a` 的**两个位点**的字母落在 `{A,G} × {A,G,C,T}` 里」，
即第一位点在 `R = {A,G}`、第二位点任意（`N` = 任意字母）。
因此一个「位点对模式」是 `SitePair = SitePat × SitePat`，
其中 `SitePat = Fin 4 → Fin 2` 是**单个位点**上四个叶的 `R/Y` 类模式
（`0 = R`、`1 = Y`）；两个分量是两个独立的位点。

## 2. 🔻 诚实边界：本文件的 `P1` 是 2 状态链的**集总**版本

* **生成元一侧**：LM1 的 4 状态率矩阵对 `R/Y` 分类**强可集总**
  （Kemeny–Snell Thm 6.3.2 判据）已由 `Phylo/Stat/LMLumping.lean` 证明
  （`Params.stronglyLumpable` / `rateRY` / `rateYR`，附录 `eq:reduced`）。
* **从生成元到转移半群的提升**（「强可集总 ⇒ `e^{Qt}` 可集总」）
  是标准结论（Kemeny–Snell Thm 6.3.2 的推论），本文件**不**重复证明它；
  本文件**以附录 `eq:reduced` 的 2 状态生成元 `Q* = λ[[−π_Y, π_Y],[π_R, −π_R]]`
  的转移矩阵闭式 `P2` 作为 2 状态链的定义**，并证明
  ★ `P2_stochastic`（随机性：行和 1 + 非负）、
  ★★ `P2_semigroup`（半群律 `P2(s+t) = P2 s * P2 t`）、
  ★ `P2_hasDerivAt`（生成元相容 `P2'(0) = λ Q*`）
  这三条作为「`P2` 确实是由 `Q*` 生成的 CTMC 的转移矩阵」的正当性证书。
* 因此本文件的结论**不是**从 4×4 矩阵指数推出来的，而是从
  「附录自己用的那套 2 状态记账」推出来的 —— 与附录 1611–1700 行的推导同一层。
* **`q`（单点位点四叶律）的定义**：基因树 `ab|cd` 的两个内部节点记作 `x`（叶 `a,b` 所在）
  与 `y`（叶 `c,d` 所在），内部边长 `l_x`。根在 `x` 处取平稳分布
  （`πm = (π_R, π_Y)`），则叶的联合类分布是树上 CTMC 的联合分布 —— 这是**定义**，
  不是假设；它的每一条边缘都由 ★★ `paste`（可逆性 + 半群律）算出。

## 3. 额外假设（逐条，均为附录自身的假设）

1. `Σπ = 1`，即 `π_R + π_Y = 1`（`hsum`）：`P2` 的行和、★★ `paste`、
   ★★ `q_sum` 以及附录 1690 行的化简都用到它。
   （⚠️ 与 `Phylo/Stat/LMLumping.lean` 不同：那里只用 `λ` 的**生成元**，不需要归一化；
   这里用到转移矩阵闭式，故**必须**归一化。）
2. `π_R > 0`、`π_Y > 0`（`hR`、`hY`）：附录全程假设平衡频率为正；
   正性结论 ★★ `E_wLM1_sub_pos` 需要 `π_R²π_Y² > 0`。
3. `λ > 0`：速率因子为正（附录 1643 行「for some constant `λ > 0`」）。
4. 枝长非负与 `l_x > 0`：闭式（★★★ `E_wLM1_ab_sub_ac`）本身**不**依赖枝长非负性
   （它是代数恒等式），但正性结论 ★★ `E_wLM1_sub_pos` 需要 `lam > 0` 与 `l_x > 0`
   来保证 `1 − e^{−2λ l_x} > 0`。

## 4. 本文件证的定理

* ★ `P2_row_sum` / `P2_nonneg` / `P2_stochastic`、★★ `P2_semigroup`、
  ★★ `P2_mul_entry`、★ `P2_hasDerivAt`；
* ★★ `sum_pi_four`、★★ `sum_q_pair_01/02/13/23`（坐标抽出引理）；
* ★★ `paste`、★★ `q_sum`、★★ `q_marginal_R`、★★ `q_diff_ab/cd/ac/bd`；
* ★★ `pairProb` 族（RY / YR / RR / YY 四种两位点联合概率的闭式）；
* ★★ `E_wLM1_ab_cd`、★★ `E_wLM1_ac_bd`（附录 1677–1700 行的两式）
  及其展开形式 `E_wLM1_ab_cd_expanded` / `E_wLM1_ac_bd_expanded`；
* ★★★ `E_wLM1_ab_sub_ac`（**命题 A**，基因树层得分差闭式）；
* ★★ `E_wLM1_sub_pos`（正性）。
-/

set_option maxHeartbeats 1600000

namespace Phylo.CASTERLM1

open Phylo.Stat.CASTERWeights (Topo)

noncomputable section

/-! ## 0. 平衡频率、集总类别与 `e^{−λt}` -/

/-- 嘌呤频率 `π_R = π_A + π_G`（字母表编号 `0 = A`、`1 = G`）。 -/
def piR (π : Fin 4 → ℝ) : ℝ := π 0 + π 1

/-- 嘧啶频率 `π_Y = π_C + π_T`（字母表编号 `2 = C`、`3 = T`）。 -/
def piY (π : Fin 4 → ℝ) : ℝ := π 2 + π 3

/-- 集总后 2 状态链的平稳分布：状态 `0 = R`、状态 `1 = Y`。 -/
def piCls (π : Fin 4 → ℝ) : Fin 2 → ℝ
  | 0 => piR π
  | 1 => piY π

@[simp] theorem piCls_zero (π : Fin 4 → ℝ) : piCls π 0 = piR π := rfl

@[simp] theorem piCls_one (π : Fin 4 → ℝ) : piCls π 1 = piY π := rfl

/-- `e^{−λ t}`（**不要**与 `Phylo.JC.e` 混淆：后者是 `e^{−(4/3)t}`）。 -/
def ee (lam t : ℝ) : ℝ := Real.exp (-(lam * t))

@[simp] theorem ee_zero (lam : ℝ) : ee lam 0 = 1 := by simp [ee]

@[simp] theorem ee_add (lam s t : ℝ) : ee lam (s + t) = ee lam s * ee lam t := by
  rw [ee, ee, ee, ← Real.exp_add]
  congr 1
  ring

theorem ee_pos (lam t : ℝ) : 0 < ee lam t := Real.exp_pos _

theorem ee_nonneg (lam t : ℝ) : 0 ≤ ee lam t := (ee_pos lam t).le

/-- `0 ≤ λ t → e^{−λ t} ≤ 1`。 -/
theorem ee_le_one {lam t : ℝ} (h : 0 ≤ lam * t) : ee lam t ≤ 1 := by
  have h' : -(lam * t) ≤ 0 := by linarith
  calc ee lam t = Real.exp (-(lam * t)) := rfl
    _ ≤ Real.exp 0 := Real.exp_le_exp.mpr h'
    _ = 1 := Real.exp_zero

/-- `0 < λ t → e^{−λ t} < 1`（★ `E_wLM1_sub_pos` 用）。 -/
theorem ee_lt_one {lam t : ℝ} (h : 0 < lam * t) : ee lam t < 1 := by
  have h' : -(lam * t) < 0 := by linarith
  calc ee lam t = Real.exp (-(lam * t)) := rfl
    _ < Real.exp 0 := Real.exp_lt_exp.mpr h'
    _ = 1 := Real.exp_zero

/-! ## 1. 集总后 2 状态链的转移矩阵 `P2`（附录 `eq:reduced`）

附录的生成元是 `Q* = λ [[−π_Y, π_Y], [π_R, −π_R]]`，其转移矩阵（用 `π_R + π_Y = 1`）为

```
P2 lam t = !![π_R + π_Y e^{−λt},  π_Y (1 − e^{−λt});
             π_R (1 − e^{−λt}),  π_Y + π_R e^{−λt}]
```

（代码里写成 `Matrix.of` 的分情况定义，与上式逐元素相同。） -/

/-- **集总后 2 状态链的转移矩阵**（附录 `eq:reduced`；见文件头 §2 的记账方式说明）。 -/
def P2 (π : Fin 4 → ℝ) (lam t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of fun
    | 0, 0 => piR π + piY π * ee lam t
    | 0, 1 => piY π * (1 - ee lam t)
    | 1, 0 => piR π * (1 - ee lam t)
    | 1, 1 => piY π + piR π * ee lam t

/-- **集总后 2 状态链的生成元** `Q* = [[−π_Y, π_Y], [π_R, −π_R]]`（附录 `eq:reduced`；差因子 `λ`）。 -/
def Qstar (π : Fin 4 → ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of fun
    | 0, 0 => -(piY π)
    | 0, 1 => piY π
    | 1, 0 => piR π
    | 1, 1 => -(piR π)

@[simp] theorem P2_apply_zero_zero (π : Fin 4 → ℝ) (lam t : ℝ) :
    P2 π lam t 0 0 = piR π + piY π * ee lam t := rfl

@[simp] theorem P2_apply_zero_one (π : Fin 4 → ℝ) (lam t : ℝ) :
    P2 π lam t 0 1 = piY π * (1 - ee lam t) := rfl

@[simp] theorem P2_apply_one_zero (π : Fin 4 → ℝ) (lam t : ℝ) :
    P2 π lam t 1 0 = piR π * (1 - ee lam t) := rfl

@[simp] theorem P2_apply_one_one (π : Fin 4 → ℝ) (lam t : ℝ) :
    P2 π lam t 1 1 = piY π + piR π * ee lam t := rfl

@[simp] theorem Qstar_apply_zero_zero (π : Fin 4 → ℝ) : Qstar π 0 0 = -(piY π) := rfl

@[simp] theorem Qstar_apply_zero_one (π : Fin 4 → ℝ) : Qstar π 0 1 = piY π := rfl

@[simp] theorem Qstar_apply_one_zero (π : Fin 4 → ℝ) : Qstar π 1 0 = piR π := rfl

@[simp] theorem Qstar_apply_one_one (π : Fin 4 → ℝ) : Qstar π 1 1 = -(piR π) := rfl

/-- ★ **`P2` 的每行和为 `1`**（需要 `π_R + π_Y = 1`）：行 `0` 的和是
`(π_R + π_Y e) + π_Y (1 − e) = π_R + π_Y`，行 `1` 同理。 -/
theorem P2_row_sum (π : Fin 4 → ℝ) (hsum : piR π + piY π = 1) (lam t : ℝ) (i : Fin 2) :
    ∑ j, P2 π lam t i j = 1 := by
  have hY : piY π = 1 - piR π := by linarith
  fin_cases i <;>
    · simp only [Fin.sum_univ_two, P2, Matrix.of_apply]
      rw [hY]
      ring

/-- ★ **`P2` 的元素非负**（需要 `λ ≥ 0`、`t ≥ 0`，使 `e^{−λt} ≤ 1`）。 -/
theorem P2_nonneg (π : Fin 4 → ℝ) (hR : 0 < piR π) (hY : 0 < piY π)
    {lam : ℝ} (hlam : 0 ≤ lam) {t : ℝ} (ht : 0 ≤ t) (i j : Fin 2) :
    0 ≤ P2 π lam t i j := by
  have hle : ee lam t ≤ 1 := ee_le_one (by nlinarith)
  have hp : 0 < ee lam t := ee_pos lam t
  fin_cases i <;> fin_cases j <;>
    simp only [P2, Matrix.of_apply] <;>
    nlinarith

/-- ★ **`P2` 是随机矩阵**：行和 `1`、元素非负。 -/
theorem P2_stochastic (π : Fin 4 → ℝ) (hsum : piR π + piY π = 1)
    (hR : 0 < piR π) (hY : 0 < piY π) {lam : ℝ} (hlam : 0 ≤ lam) {t : ℝ} (ht : 0 ≤ t) :
    (∀ i, ∑ j, P2 π lam t i j = 1) ∧ (∀ i j, 0 ≤ P2 π lam t i j) :=
  ⟨fun i => P2_row_sum π hsum lam t i, fun i j => P2_nonneg π hR hY hlam ht i j⟩

/-- ★★ **半群律（Chapman–Kolmogorov）**：`P2 lam (s+t) = P2 lam s * P2 lam t`。

`e^{−λ(s+t)} = e^{−λs}e^{−λt}` 与 `π_R + π_Y = 1` 是全部代数输入。 -/
theorem P2_semigroup (π : Fin 4 → ℝ) (hsum : piR π + piY π = 1)
    (lam s t : ℝ) : P2 π lam (s + t) = P2 π lam s * P2 π lam t := by
  have hY : piY π = 1 - piR π := by linarith
  ext i j
  fin_cases i <;> fin_cases j <;>
    · rw [Matrix.mul_apply, Fin.sum_univ_two]
      simp only [P2, Matrix.of_apply, ee_add]
      rw [hY]
      ring

/-- ★★ **矩阵乘法的逐元素形式**（★★ `P2_semigroup` 的推论；「树上两段路径合成一段」）。 -/
theorem P2_mul_entry (π : Fin 4 → ℝ) (hsum : piR π + piY π = 1)
    (lam s t : ℝ) (i j : Fin 2) :
    (∑ k, P2 π lam s i k * P2 π lam t k j) = P2 π lam (s + t) i j := by
  have h : P2 π lam (s + t) = P2 π lam s * P2 π lam t := P2_semigroup π hsum lam s t
  rw [h, Matrix.mul_apply]

/-- `d/dt e^{−λt} |_{t=0} = −λ`。 -/
theorem hasDerivAt_ee (lam : ℝ) : HasDerivAt (fun t : ℝ => ee lam t) (-lam) 0 := by
  have hbase : HasDerivAt (fun t : ℝ => (-lam) * t) (-lam) 0 := by
    simpa using (hasDerivAt_id' (0 : ℝ)).const_mul (-lam)
  have h := hbase.exp
  simpa [ee, mul_one] using h

/-- ★ **生成元相容**：`d/dt P2 lam t |_{t=0} = λ · Q*`。

即附录 `eq:reduced` 的 `Q*` 确实是 `P2` 在 `0` 处的（右）导数，
从而 `P2` 是由 `λ Q*` 生成的 CTMC 的转移矩阵（配合 ★★ `P2_semigroup`）。 -/
theorem P2_hasDerivAt (π : Fin 4 → ℝ) (lam : ℝ) (i j : Fin 2) :
    HasDerivAt (fun t => P2 π lam t i j) (lam * Qstar π i j) 0 := by
  have hee : HasDerivAt (fun t : ℝ => ee lam t) (-lam) 0 := hasDerivAt_ee lam
  have hone : HasDerivAt (fun t : ℝ => 1 - ee lam t) lam 0 := by
    have h := hee.const_sub (1 : ℝ)
    simpa using h
  have d00 : HasDerivAt (fun t : ℝ => piR π + piY π * ee lam t) (lam * -piY π) 0 := by
    have h := (hee.const_mul (piY π)).const_add (piR π)
    convert h using 1
    ring
  have d01 : HasDerivAt (fun t : ℝ => piY π * (1 - ee lam t)) (lam * piY π) 0 := by
    have h := hone.const_mul (piY π)
    convert h using 1
    ring
  have d10 : HasDerivAt (fun t : ℝ => piR π * (1 - ee lam t)) (lam * piR π) 0 := by
    have h := hone.const_mul (piR π)
    convert h using 1
    ring
  have d11 : HasDerivAt (fun t : ℝ => piY π + piR π * ee lam t) (lam * -piR π) 0 := by
    have h := (hee.const_mul (piR π)).const_add (piY π)
    convert h using 1
    ring
  fin_cases i <;> fin_cases j <;>
    · simp only [P2, Qstar, Matrix.of_apply]
      first
        | exact d00
        | exact d01
        | exact d10
        | exact d11

/-! ## 2. 位点模式与位点对模式 -/

/-- **单个位点**的四叶 `R/Y` 类模式：叶 `i` 的类别是 `p i`（`0 = R`、`1 = Y`）。 -/
abbrev SitePat := Fin 4 → Fin 2

/-- **位点对**（LM1 的观测）：两个**独立**位点的类模式。 -/
abbrev SitePair := SitePat × SitePat

/-- 显式等价 `SitePat ≃ Fin 2 × Fin 2 × Fin 2 × Fin 2`（`×` 右结合）。 -/
def piFinFourEquiv : SitePat ≃ (Fin 2 × Fin 2 × Fin 2 × Fin 2) where
  toFun f := (f 0, f 1, f 2, f 3)
  invFun t := ![t.1, t.2.1, t.2.2.1, t.2.2.2]
  left_inv f := by funext i; fin_cases i <;> rfl
  right_inv t := by rcases t with ⟨a, b, c, d⟩; rfl

@[simp] theorem piFinFourEquiv_symm_apply (a b c d : Fin 2) :
    piFinFourEquiv.symm (a, b, c, d) = ![a, b, c, d] := by
  funext i; fin_cases i <;> rfl

/-- ★★ **把 `SitePat` 上的和展开为四个坐标上的累次和**（后续所有「坐标求和」的入口）。 -/
theorem sum_pi_four (F : SitePat → ℝ) :
    (∑ p : SitePat, F p) = ∑ a, ∑ b, ∑ c, ∑ d, F ![a, b, c, d] := by
  rw [← Equiv.sum_comp piFinFourEquiv.symm F]
  rw [Fintype.sum_prod_type]
  conv_lhs => enter [2, t]; rw [Fintype.sum_prod_type]
  conv_lhs => enter [2, t, 2, u]; rw [Fintype.sum_prod_type]
  simp

/-! ### 2.1 逐模式权重用的指示函数 -/

/-- 指示函数 `1[P]`。 -/
def ind (P : Prop) [Decidable P] : ℝ := if P then 1 else 0

/-- 单点位点模式 `p` 在叶 `u`、`v` 上是 `(R, Y)`（附录 `RN` / `NR` 之类的核心约束）。 -/
abbrev isRY (p : SitePat) (u v : Fin 4) : Prop := p u = 0 ∧ p v = 1

/-- 单点位点模式 `p` 在叶 `u`、`v` 上是 `(Y, R)`。 -/
abbrev isYR (p : SitePat) (u v : Fin 4) : Prop := p u = 1 ∧ p v = 0

/-- 「`NN`」：两个叶都不受约束（附录里 `N` = 任意字母）。 -/
abbrev isNN (_ : SitePat) : Prop := True

/-- ★ **两个叶的类别不同 ⟺ `(R,Y)` 或 `(Y,R)`**（`Fin 2` 只有两个元素，
两个指示函数互斥，故相加）。 -/
theorem ind_ne_eq (p : SitePat) (u v : Fin 4) :
    ind (p u ≠ p v) = ind (isRY p u v) + ind (isYR p u v) := by
  have hu : p u = 0 ∨ p u = 1 := by omega
  have hv : p v = 0 ∨ p v = 1 := by omega
  rcases hu with h | h <;> rcases hv with h' | h' <;> simp [ind, isRY, isYR, h, h']

@[simp] theorem ind_nn (p : SitePat) : ind (isNN p) = 1 := by simp [ind, isNN]

/-! ## 3. 单点位点的四叶律 `q` 及其边缘

`q` 的定义就是「基因树 `ab|cd` 上、根在内部节点 `x` 处取平稳分布的 2 状态链」
的四叶类模式概率（文件头 §2 有说明）。 -/

/-- **单点位点的四叶类模式律**（基因树 `ab|cd`）：叶 `a,b` 挂在节点 `x` 上
（枝长 `la, lb`），叶 `c,d` 挂在节点 `y` 上（枝长 `lc, ld`），`x–y` 的内部边长 `lx`。
`m`、`n` 分别是 `x`、`y` 的类别；`x` 处取平稳分布 `πm = (π_R, π_Y)`。 -/
def q (π : Fin 4 → ℝ) (lam la lb lc ld lx : ℝ) (p : SitePat) : ℝ :=
  ∑ m : Fin 2, ∑ n : Fin 2,
    piCls π m * P2 π lam la m (p 0) * P2 π lam lb m (p 1) *
      P2 π lam lx m n * P2 π lam lc n (p 2) * P2 π lam ld n (p 3)

/-- ★★ **坐标抽出引理（约束在坐标 `(0,1)`）**：把 `q` 定义里的两个内部状态和提出去，
并把两个「自由叶」求和掉。证明是有限和重排 + `ring`（穷举 `Fin 2` 的全部取值）。 -/
theorem sum_q_pair_01 (W A B C D : Fin 2 → Fin 2 → ℝ) (f : Fin 2 → Fin 2 → ℝ) :
    (∑ p : SitePat, f (p 0) (p 1) * (∑ m, ∑ n,
        W m n * A m (p 0) * B m (p 1) * C n (p 2) * D n (p 3)))
      = ∑ m, ∑ n, W m n * (∑ i, ∑ j, f i j * A m i * B m j)
          * (∑ c, C n c) * (∑ d, D n d) := by
  simp_rw [Finset.mul_sum]
  rw [sum_pi_four]
  simp only [Fin.sum_univ_two]
  simp
  ring

/-- ★★ **坐标抽出引理（约束在坐标 `(0,2)`）**。 -/
theorem sum_q_pair_02 (W A B C D : Fin 2 → Fin 2 → ℝ) (f : Fin 2 → Fin 2 → ℝ) :
    (∑ p : SitePat, f (p 0) (p 2) * (∑ m, ∑ n,
        W m n * A m (p 0) * B m (p 1) * C n (p 2) * D n (p 3)))
      = ∑ m, ∑ n, W m n * (∑ i, ∑ j, f i j * A m i * C n j)
          * (∑ b, B m b) * (∑ d, D n d) := by
  simp_rw [Finset.mul_sum]
  rw [sum_pi_four]
  simp only [Fin.sum_univ_two]
  simp
  ring

/-- ★★ **坐标抽出引理（约束在坐标 `(1,3)`）**。 -/
theorem sum_q_pair_13 (W A B C D : Fin 2 → Fin 2 → ℝ) (f : Fin 2 → Fin 2 → ℝ) :
    (∑ p : SitePat, f (p 1) (p 3) * (∑ m, ∑ n,
        W m n * A m (p 0) * B m (p 1) * C n (p 2) * D n (p 3)))
      = ∑ m, ∑ n, W m n * (∑ a, A m a) * (∑ i, ∑ j, f i j * B m i * D n j)
          * (∑ c, C n c) := by
  simp_rw [Finset.mul_sum]
  rw [sum_pi_four]
  simp only [Fin.sum_univ_two]
  simp
  ring

/-- ★★ **坐标抽出引理（约束在坐标 `(2,3)`）**。 -/
theorem sum_q_pair_23 (W A B C D : Fin 2 → Fin 2 → ℝ) (f : Fin 2 → Fin 2 → ℝ) :
    (∑ p : SitePat, f (p 2) (p 3) * (∑ m, ∑ n,
        W m n * A m (p 0) * B m (p 1) * C n (p 2) * D n (p 3)))
      = ∑ m, ∑ n, W m n * (∑ a, A m a) * (∑ b, B m b)
          * (∑ i, ∑ j, f i j * C n i * D n j) := by
  simp_rw [Finset.mul_sum]
  rw [sum_pi_four]
  simp only [Fin.sum_univ_two]
  simp
  ring

/-- ★★ 把 `q` 的定义改写成 `sum_q_pair_01` 的输入形状。 -/
theorem q_eq_shape (π : Fin 4 → ℝ) (lam la lb lc ld lx : ℝ) (p : SitePat) :
    q π lam la lb lc ld lx p
      = ∑ m : Fin 2, ∑ n : Fin 2, (piCls π m * P2 π lam lx m n)
          * P2 π lam la m (p 0) * P2 π lam lb m (p 1)
          * P2 π lam lc n (p 2) * P2 π lam ld n (p 3) := by
  simp only [q]
  refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun n _ => ?_
  ring

/-- ★★ `q` 的 `(0,1)` 边缘（坐标抽出）。 -/
theorem sum_q_pair_01_q (π : Fin 4 → ℝ) (lam la lb lc ld lx : ℝ) (f : Fin 2 → Fin 2 → ℝ) :
    (∑ p : SitePat, f (p 0) (p 1) * q π lam la lb lc ld lx p)
      = ∑ m, ∑ n, (piCls π m * P2 π lam lx m n)
          * (∑ i, ∑ j, f i j * P2 π lam la m i * P2 π lam lb m j)
          * (∑ c, P2 π lam lc n c) * (∑ d, P2 π lam ld n d) := by
  simp only [q_eq_shape]
  exact sum_q_pair_01 _ _ _ _ _ f

/-- ★★ `q` 的 `(0,2)` 边缘（坐标抽出）。 -/
theorem sum_q_pair_02_q (π : Fin 4 → ℝ) (lam la lb lc ld lx : ℝ) (f : Fin 2 → Fin 2 → ℝ) :
    (∑ p : SitePat, f (p 0) (p 2) * q π lam la lb lc ld lx p)
      = ∑ m, ∑ n, (piCls π m * P2 π lam lx m n)
          * (∑ i, ∑ j, f i j * P2 π lam la m i * P2 π lam lc n j)
          * (∑ b, P2 π lam lb m b) * (∑ d, P2 π lam ld n d) := by
  simp only [q_eq_shape]
  exact sum_q_pair_02 _ _ _ _ _ f

/-- ★★ `q` 的 `(1,3)` 边缘（坐标抽出）。 -/
theorem sum_q_pair_13_q (π : Fin 4 → ℝ) (lam la lb lc ld lx : ℝ) (f : Fin 2 → Fin 2 → ℝ) :
    (∑ p : SitePat, f (p 1) (p 3) * q π lam la lb lc ld lx p)
      = ∑ m, ∑ n, (piCls π m * P2 π lam lx m n)
          * (∑ a, P2 π lam la m a)
          * (∑ i, ∑ j, f i j * P2 π lam lb m i * P2 π lam ld n j)
          * (∑ c, P2 π lam lc n c) := by
  simp only [q_eq_shape]
  exact sum_q_pair_13 _ _ _ _ _ f

/-- ★★ `q` 的 `(2,3)` 边缘（坐标抽出）。 -/
theorem sum_q_pair_23_q (π : Fin 4 → ℝ) (lam la lb lc ld lx : ℝ) (f : Fin 2 → Fin 2 → ℝ) :
    (∑ p : SitePat, f (p 2) (p 3) * q π lam la lb lc ld lx p)
      = ∑ m, ∑ n, (piCls π m * P2 π lam lx m n)
          * (∑ a, P2 π lam la m a) * (∑ b, P2 π lam lb m b)
          * (∑ i, ∑ j, f i j * P2 π lam lc n i * P2 π lam ld n j) := by
  simp only [q_eq_shape]
  exact sum_q_pair_23 _ _ _ _ _ f

/-- ★★ **`paste`（粘贴引理）**：`∑_m πm_m P2(A)_{mi} P2(B)_{mj} = πm_i P2(A+B)_{ij}`。

用可逆性 `πm_m P2(A)_{mi} = πm_i P2(A)_{im}` 与半群律把「树上两段路径」合成一段。 -/
theorem paste (π : Fin 4 → ℝ) (hsum : piR π + piY π = 1) (lam A B : ℝ) (i j : Fin 2) :
    (∑ m : Fin 2, piCls π m * P2 π lam A m i * P2 π lam B m j)
      = piCls π i * P2 π lam (A + B) i j := by
  have hY : piY π = 1 - piR π := by linarith
  fin_cases i <;> fin_cases j <;>
    · simp only [piCls, Fin.sum_univ_two, P2, Matrix.of_apply, ee_add]
      rw [hY]
      ring

/-- ★★ **`q` 是概率分布**：`∑_p q(p) = 1`。 -/
theorem q_sum (π : Fin 4 → ℝ) (hsum : piR π + piY π = 1) (lam la lb lc ld lx : ℝ) :
    (∑ p : SitePat, q π lam la lb lc ld lx p) = 1 := by
  have hY : piY π = 1 - piR π := by linarith
  have h := sum_q_pair_01_q π lam la lb lc ld lx (fun _ _ => (1 : ℝ))
  simp only [one_mul] at h
  rw [h]
  simp only [P2_row_sum π hsum lam lc, P2_row_sum π hsum lam ld, mul_one]
  simp only [Fin.sum_univ_two, P2, Matrix.of_apply, piCls]
  rw [hY]
  ring

/-- ★★ **两叶「类别不同」的概率**（`(a,b)` 对）：`2 π_Rπ_Y (1 − e^{−λ(l_a+l_b)})`。

即附录 1638 行的两个朝向 `(R,Y)` 与 `(Y,R)` 之和。 -/
theorem q_diff_ab (π : Fin 4 → ℝ) (hsum : piR π + piY π = 1) (lam la lb lc ld lx : ℝ) :
    (∑ p : SitePat, ind (p 0 ≠ p 1) * q π lam la lb lc ld lx p)
      = 2 * (piR π * piY π * (1 - ee lam (la + lb))) := by
  have hY : piY π = 1 - piR π := by linarith
  rw [sum_q_pair_01_q π lam la lb lc ld lx (fun i j => ind (i ≠ j))]
  simp only [P2_row_sum π hsum lam lc, P2_row_sum π hsum lam ld, mul_one]
  simp only [Fin.sum_univ_two, P2, Matrix.of_apply, piCls, ee_add]
  rw [hY]
  norm_num [ind]
  ring

/-- ★★ **两叶「类别不同」的概率**（`(c,d)` 对）：`2 π_Rπ_Y (1 − e^{−λ(l_c+l_d)})`。 -/
theorem q_diff_cd (π : Fin 4 → ℝ) (hsum : piR π + piY π = 1) (lam la lb lc ld lx : ℝ) :
    (∑ p : SitePat, ind (p 2 ≠ p 3) * q π lam la lb lc ld lx p)
      = 2 * (piR π * piY π * (1 - ee lam (lc + ld))) := by
  have hY : piY π = 1 - piR π := by linarith
  rw [sum_q_pair_23_q π lam la lb lc ld lx (fun i j => ind (i ≠ j))]
  simp only [P2_row_sum π hsum lam la, P2_row_sum π hsum lam lb, mul_one]
  simp only [Fin.sum_univ_two, P2, Matrix.of_apply, piCls, ee_add]
  rw [hY]
  norm_num [ind]
  ring

/-- ★★ **两叶「类别不同」的概率**（`(a,c)` 对）：`2 π_Rπ_Y (1 − e^{−λ(l_a+l_x+l_c)})`。

这是 `ac|bd` 那一侧的边缘（附录 1640 行）。 -/
theorem q_diff_ac (π : Fin 4 → ℝ) (hsum : piR π + piY π = 1) (lam la lb lc ld lx : ℝ) :
    (∑ p : SitePat, ind (p 0 ≠ p 2) * q π lam la lb lc ld lx p)
      = 2 * (piR π * piY π * (1 - ee lam (la + lx + lc))) := by
  have hY : piY π = 1 - piR π := by linarith
  rw [sum_q_pair_02_q π lam la lb lc ld lx (fun i j => ind (i ≠ j))]
  simp only [P2_row_sum π hsum lam lb, P2_row_sum π hsum lam ld, mul_one]
  simp only [Fin.sum_univ_two, P2, Matrix.of_apply, piCls, ee_add]
  rw [hY]
  norm_num [ind]
  ring

/-- ★★ **两叶「类别不同」的概率**（`(b,d)` 对）：`2 π_Rπ_Y (1 − e^{−λ(l_b+l_x+l_d)})`。 -/
theorem q_diff_bd (π : Fin 4 → ℝ) (hsum : piR π + piY π = 1) (lam la lb lc ld lx : ℝ) :
    (∑ p : SitePat, ind (p 1 ≠ p 3) * q π lam la lb lc ld lx p)
      = 2 * (piR π * piY π * (1 - ee lam (lb + lx + ld))) := by
  have hY : piY π = 1 - piR π := by linarith
  rw [sum_q_pair_13_q π lam la lb lc ld lx (fun i j => ind (i ≠ j))]
  simp only [P2_row_sum π hsum lam la, P2_row_sum π hsum lam lc, mul_one]
  simp only [Fin.sum_univ_two, P2, Matrix.of_apply, piCls, ee_add]
  rw [hY]
  norm_num [ind]
  ring

/-- ★★ **单叶边缘**：`P(叶 a ∈ R) = π_R`（附录 1623 行的记号；`Σπ = 1` 下必然）。 -/
theorem q_marginal_R (π : Fin 4 → ℝ) (hsum : piR π + piY π = 1) (lam la lb lc ld lx : ℝ) :
    (∑ p : SitePat, ind (p 0 = 0) * q π lam la lb lc ld lx p) = piR π := by
  have hY : piY π = 1 - piR π := by linarith
  rw [sum_q_pair_01_q π lam la lb lc ld lx (fun i _ => ind (i = 0))]
  simp only [P2_row_sum π hsum lam lc, P2_row_sum π hsum lam ld, mul_one]
  simp only [Fin.sum_univ_two, P2, Matrix.of_apply, piCls]
  rw [hY]
  norm_num [ind]
  ring

/-- ★★ **`(a,b)` 上单个朝向的边缘**：`P(𝓁_a = R, 𝓁_b = Y) = π_Rπ_Y (1 − e^{−λ(l_a+l_b)})`
（附录 1638 行的原式；两个朝向相同，故 ★★ `q_diff_ab` 是它的两倍）。 -/
theorem q_RY_ab (π : Fin 4 → ℝ) (hsum : piR π + piY π = 1) (lam la lb lc ld lx : ℝ) :
    (∑ p : SitePat, ind (isRY p 0 1) * q π lam la lb lc ld lx p)
      = piR π * piY π * (1 - ee lam (la + lb)) := by
  have hY : piY π = 1 - piR π := by linarith
  rw [sum_q_pair_01_q π lam la lb lc ld lx (fun i j => ind (i = 0 ∧ j = 1))]
  simp only [P2_row_sum π hsum lam lc, P2_row_sum π hsum lam ld, mul_one]
  simp only [Fin.sum_univ_two, P2, Matrix.of_apply, piCls, ee_add]
  rw [hY]
  norm_num [ind]
  ring

/-- ★★ **`(c,d)` 上单个朝向的边缘**：`P(𝓁_c = R, 𝓁_d = Y) = π_Rπ_Y (1 − e^{−λ(l_c+l_d)})`。 -/
theorem q_RY_cd (π : Fin 4 → ℝ) (hsum : piR π + piY π = 1) (lam la lb lc ld lx : ℝ) :
    (∑ p : SitePat, ind (isRY p 2 3) * q π lam la lb lc ld lx p)
      = piR π * piY π * (1 - ee lam (lc + ld)) := by
  have hY : piY π = 1 - piR π := by linarith
  rw [sum_q_pair_23_q π lam la lb lc ld lx (fun i j => ind (i = 0 ∧ j = 1))]
  simp only [P2_row_sum π hsum lam la, P2_row_sum π hsum lam lb, mul_one]
  simp only [Fin.sum_univ_two, P2, Matrix.of_apply, piCls, ee_add]
  rw [hY]
  norm_num [ind]
  ring

/- 注：附录 1661 行的「两位点独立 ⇒ 四叶位点对的联合概率」是 ★★ `q_RY_ab_RY_cd`，
   它需要 ★★ `sum_pair_prod`，故定义在 §5 里（`sum_pair_prod` 之后）。 -/

/-- ★★ **`pairProb`：两叶 `(R, Y)` 的联合概率闭式**（附录 1638 行）。

若叶 `u`、`v` 的路径长和为 `d`，则 `P(𝓁_u = R, 𝓁_v = Y) = π_R π_Y (1 − e^{−λ d})`。 -/
theorem pairProb (π : Fin 4 → ℝ) (lam d : ℝ) (i j : Fin 2) (hij : i ≠ j) :
    piCls π i * P2 π lam d i j = piCls π i * piCls π j * (1 - ee lam d) := by
  have hi : i = 0 ∨ i = 1 := by omega
  have hj : j = 0 ∨ j = 1 := by omega
  rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
  · exact (hij rfl).elim
  · simp only [P2, Matrix.of_apply, piCls]; ring
  · simp only [P2, Matrix.of_apply, piCls]; ring
  · exact (hij rfl).elim

/-- ★★ **两叶同为 `R` 的概率**：`P(𝓁_u = R, 𝓁_v = R) = π_R² + π_Rπ_Y e^{−λ d}`。 -/
theorem pairProb_RR (π : Fin 4 → ℝ) (lam d : ℝ) :
    piCls π 0 * P2 π lam d 0 0 = (piR π) ^ 2 + piR π * piY π * ee lam d := by
  simp only [P2, Matrix.of_apply, piCls]
  ring

/-- ★★ **两叶同为 `Y` 的概率**：`P(𝓁_u = Y, 𝓁_v = Y) = π_Y² + π_Rπ_Y e^{−λ d}`。 -/
theorem pairProb_YY (π : Fin 4 → ℝ) (lam d : ℝ) :
    piCls π 1 * P2 π lam d 1 1 = (piY π) ^ 2 + piR π * piY π * ee lam d := by
  simp only [P2, Matrix.of_apply, piCls]
  ring

/-- ★★ **两叶 `(Y, R)`**：`P(𝓁_u = Y, 𝓁_v = R) = π_R π_Y (1 − e^{−λ d})`。 -/
theorem pairProb_YR (π : Fin 4 → ℝ) (lam d : ℝ) :
    piCls π 1 * P2 π lam d 1 0 = piR π * piY π * (1 - ee lam d) := by
  simp only [P2, Matrix.of_apply, piCls]
  ring

/-! ## 4. LM1 的位点对权重表（附录 367–375 行）

基准拓扑 `ab|cd`；记一个位点对模式 `σ = (p₁, p₂)`（`p₁` 是第一个位点）。

12 个模式类（`sm.tex` 367–375；`N` = 任意字母）：

| 权重 | 模式 | 本文件的写法 |
|---|---|---|
| `+1` | `RN YN│NR NY` | `isRY p₁ a b ∧ isRY p₂ c d` |
| `+1` | `RN YN│NY NR` | `isRY p₁ a b ∧ isYR p₂ c d` |
| `+1` | `YN RN│NR NY` | `isYR p₁ a b ∧ isRY p₂ c d` |
| `+1` | `YN RN│NY NR` | `isYR p₁ a b ∧ isYR p₂ c d` |
| `+1` | `NR NY│RN YN` | `isRY p₁ c d ∧ isRY p₂ a b` |
| `+1` | `NR NY│YN RN` | `isRY p₁ c d ∧ isYR p₂ a b` |
| `+1` | `NY NR│RN YN` | `isYR p₁ c d ∧ isRY p₂ a b` |
| `+1` | `NY NR│YN RN` | `isYR p₁ c d ∧ isYR p₂ a b` |
| `−4π_Rπ_Y` | `RN YN│NN NN` | `isRY p₁ a b ∧ isNN p₂` |
| `−4π_Rπ_Y` | `YN RN│NN NN` | `isYR p₁ a b ∧ isNN p₂` |
| `−4π_Rπ_Y` | `NN NN│RN YN` | `isRY p₁ c d ∧ isNN p₂` |
| `−4π_Rπ_Y` | `NN NN│YN RN` | `isYR p₁ c d ∧ isNN p₂` |

⚠️ 模式类**可以重叠**（附录脚注 3：`RN YN│RN YN` 同时命中 `+1` 行与 `−4π_Rπ_Y` 行），
此时权重**相加** —— 这正是把权重写成「逐模式类的指示函数之和」而不是「互斥分类」的原因。 -/

/-- **LM1 逐模式权重（基准拓扑 `ab|cd`）**：12 个模式类的指示函数 × 权重之和
（见上面的表；重叠处权重相加）。 -/
def wLM1Base (π : Fin 4 → ℝ) (σ : SitePair) : ℝ :=
    ind (isRY σ.1 0 1) * ind (isRY σ.2 2 3)
  + ind (isRY σ.1 0 1) * ind (isYR σ.2 2 3)
  + ind (isYR σ.1 0 1) * ind (isRY σ.2 2 3)
  + ind (isYR σ.1 0 1) * ind (isYR σ.2 2 3)
  + ind (isRY σ.1 2 3) * ind (isRY σ.2 0 1)
  + ind (isRY σ.1 2 3) * ind (isYR σ.2 0 1)
  + ind (isYR σ.1 2 3) * ind (isRY σ.2 0 1)
  + ind (isYR σ.1 2 3) * ind (isYR σ.2 0 1)
  - 4 * piR π * piY π * ind (isRY σ.1 0 1) * ind (isNN σ.2)
  - 4 * piR π * piY π * ind (isYR σ.1 0 1) * ind (isNN σ.2)
  - 4 * piR π * piY π * ind (isRY σ.1 2 3) * ind (isNN σ.2)
  - 4 * piR π * piY π * ind (isYR σ.1 2 3) * ind (isNN σ.2)

/-- 「叶 `u`、`v` 的类别不同」的指示函数（两个朝向的合并写法）。 -/
def fDiff (u v : Fin 4) (p : SitePat) : ℝ := ind (p u ≠ p v)

@[simp] theorem fDiff_zero_one (p : SitePat) : fDiff 0 1 p = ind (p 0 ≠ p 1) := rfl

@[simp] theorem fDiff_two_three (p : SitePat) : fDiff 2 3 p = ind (p 2 ≠ p 3) := rfl

@[simp] theorem fDiff_zero_two (p : SitePat) : fDiff 0 2 p = ind (p 0 ≠ p 2) := rfl

@[simp] theorem fDiff_one_three (p : SitePat) : fDiff 1 3 p = ind (p 1 ≠ p 3) := rfl

/-- `NN`（任意字母）的实值指示（恒为 `1`）。 -/
def wNN (p : SitePat) : ℝ := ind (isNN p)

/-- 背景项 `−4π_Rπ_Y` 的因子：一侧两叶「类别不同」的指示 × `4π_Rπ_Y`。 -/
def wBg (π : Fin 4 → ℝ) (u v : Fin 4) (p : SitePat) : ℝ := 4 * piR π * piY π * fDiff u v p

@[simp] theorem wNN_apply (p : SitePat) : wNN p = 1 := by simp [wNN]

/-- ★★ **权重表的紧凑形式**（与 `wLM1Base` 的 12 项之和等价，由 ★ `ind_ne_eq` 得到）：
`fDiff` 是同一侧两个朝向的指示函数之和，故 8 个 `+1` 类合并为两项、
4 个背景类合并为两项。 -/
theorem wLM1Base_eq (π : Fin 4 → ℝ) (σ : SitePair) :
    wLM1Base π σ
      = fDiff 0 1 σ.1 * fDiff 2 3 σ.2 + fDiff 2 3 σ.1 * fDiff 0 1 σ.2
        - wBg π 0 1 σ.1 * wNN σ.2 - wBg π 2 3 σ.1 * wNN σ.2 := by
  simp only [wLM1Base, wBg, wNN, fDiff]
  rw [ind_ne_eq σ.1 0 1, ind_ne_eq σ.1 2 3, ind_ne_eq σ.2 2 3, ind_ne_eq σ.2 0 1]
  ring

/-- **拓扑 `T` 的 LM1 逐模式权重**：把 `T` 的两侧搬回基准拓扑 `ab|cd`
（用 `Phylo.Stat.CASTERWeights.perm`，与 JC69 权重表同一约定）。 -/
def wLM1 (π : Fin 4 → ℝ) (T : Topo) (σ : SitePair) : ℝ :=
  wLM1Base π (fun i => σ.1 (Phylo.Stat.CASTERWeights.perm T i),
              fun i => σ.2 (Phylo.Stat.CASTERWeights.perm T i))

@[simp] theorem perm_ab_cd : Phylo.Stat.CASTERWeights.perm Topo.ab_cd = 1 := rfl

@[simp] theorem swap12_apply_zero : (Equiv.swap (1 : Fin 4) 2) 0 = 0 := by decide

@[simp] theorem swap12_apply_one : (Equiv.swap (1 : Fin 4) 2) 1 = 2 := by decide

@[simp] theorem swap12_apply_two : (Equiv.swap (1 : Fin 4) 2) 2 = 1 := by decide

@[simp] theorem swap12_apply_three : (Equiv.swap (1 : Fin 4) 2) 3 = 3 := by decide

/-- ★★ **`ab|cd` 的紧凑权重**。 -/
theorem wLM1_ab_cd (π : Fin 4 → ℝ) (σ : SitePair) :
    wLM1 π .ab_cd σ
      = fDiff 0 1 σ.1 * fDiff 2 3 σ.2 + fDiff 2 3 σ.1 * fDiff 0 1 σ.2
        - wBg π 0 1 σ.1 * wNN σ.2 - wBg π 2 3 σ.1 * wNN σ.2 := by
  simp only [wLM1, perm_ab_cd]
  have h : (fun i => σ.1 ((1 : Equiv.Perm (Fin 4)) i),
            fun i => σ.2 ((1 : Equiv.Perm (Fin 4)) i)) = σ := by
    refine Prod.ext ?_ ?_ <;> funext i <;> simp
  rw [h, wLM1Base_eq]

/-- ★★ **`ac|bd` 的紧凑权重**：`perm .ac_bd = swap 1 2` 把基准的两侧
`(0,1)`、`(2,3)` 搬到 `(a,c)`、`(b,d)`。 -/
theorem wLM1_ac_bd (π : Fin 4 → ℝ) (σ : SitePair) :
    wLM1 π .ac_bd σ
      = fDiff 0 2 σ.1 * fDiff 1 3 σ.2 + fDiff 1 3 σ.1 * fDiff 0 2 σ.2
        - wBg π 0 2 σ.1 * wNN σ.2 - wBg π 1 3 σ.1 * wNN σ.2 := by
  simp only [wLM1, Phylo.Stat.CASTERWeights.perm, wLM1Base_eq, wBg, wNN,
    fDiff, swap12_apply_zero, swap12_apply_one, swap12_apply_two, swap12_apply_three]

/-! ## 5. 期望得分 `E[w]` 与主定理 -/

/-- **基因树层（拓扑 `ab|cd`）的期望得分**：
`E[w(T)] = ∑_σ w(T)(σ) · PairProb(σ)`，其中
`PairProb(σ) = q(σ.1) · q(σ.2)` 是「两位点独立」的位点对概率。 -/
def E (π : Fin 4 → ℝ) (T : Topo) (lam la lb lc ld lx : ℝ) : ℝ :=
  ∑ σ : SitePair, wLM1 π T σ * (q π lam la lb lc ld lx σ.1 * q π lam la lb lc ld lx σ.2)

/-- `M(f) = ∑_p f(p) q(p)`：单点位点上的期望。 -/
def M (π : Fin 4 → ℝ) (lam la lb lc ld lx : ℝ) (f : SitePat → ℝ) : ℝ :=
  ∑ p : SitePat, f p * q π lam la lb lc ld lx p

/-- ★★ **位点对上的双线性分解**：两个位点独立 ⇒ 逐项分解为两个单点位点期望之积。 -/
theorem sum_pair_prod (π : Fin 4 → ℝ) (lam la lb lc ld lx : ℝ) (f g : SitePat → ℝ) :
    (∑ σ : SitePair,
        (f σ.1 * g σ.2) * (q π lam la lb lc ld lx σ.1 * q π lam la lb lc ld lx σ.2))
      = (∑ p : SitePat, f p * q π lam la lb lc ld lx p)
        * (∑ p : SitePat, g p * q π lam la lb lc ld lx p) := by
  rw [Fintype.sum_prod_type]
  have h : ∀ x y : SitePat, (f x * g y) * (q π lam la lb lc ld lx x * q π lam la lb lc ld lx y)
      = (f x * q π lam la lb lc ld lx x) * (g y * q π lam la lb lc ld lx y) :=
    fun x y => by ring
  simp only [h]
  exact (Fintype.sum_mul_sum (fun x : SitePat => f x * q π lam la lb lc ld lx x)
    (fun x : SitePat => g x * q π lam la lb lc ld lx x)).symm

/-- ★★ **两位点独立：四叶位点对的联合概率**（附录 1661 行）

`P(𝓁_a = RN, 𝓁_b = YN, 𝓁_c = NR, 𝓁_d = NY) = π_R²π_Y² (1 − u)(1 − v)`，
`u = e^{−λ(l_a+l_b)}`、`v = e^{−λ(l_c+l_d)}`：
`q_RY_ab_RY_cd` 由 ★★ `sum_pair_prod`（两位点独立）与 ★★ `q_RY_ab` / ★★ `q_RY_cd` 相乘得到。 -/
theorem q_RY_ab_RY_cd (π : Fin 4 → ℝ) (hsum : piR π + piY π = 1)
    (lam la lb lc ld lx : ℝ) :
    (∑ σ : SitePair, ind (isRY σ.1 0 1) * ind (isRY σ.2 2 3)
        * (q π lam la lb lc ld lx σ.1 * q π lam la lb lc ld lx σ.2))
      = piR π ^ 2 * piY π ^ 2 * (1 - ee lam (la + lb)) * (1 - ee lam (lc + ld)) := by
  rw [Fintype.sum_prod_type]
  have h : ∀ x y : SitePat,
      ind (isRY x 0 1) * ind (isRY y 2 3)
          * (q π lam la lb lc ld lx x * q π lam la lb lc ld lx y)
        = (ind (isRY x 0 1) * q π lam la lb lc ld lx x)
          * (ind (isRY y 2 3) * q π lam la lb lc ld lx y) := fun x y => by ring
  simp only [h]
  rw [← Fintype.sum_mul_sum]
  rw [q_RY_ab π hsum lam la lb lc ld lx, q_RY_cd π hsum lam la lb lc ld lx]
  ring

/-- ★★ **`M(1) = 1`**（`q` 是概率分布）。 -/
theorem M_one (π : Fin 4 → ℝ) (hsum : piR π + piY π = 1) (lam la lb lc ld lx : ℝ) :
    M π lam la lb lc ld lx wNN = 1 := by
  simp only [M, wNN_apply, one_mul]
  exact q_sum π hsum lam la lb lc ld lx

/-- ★★ **`M(c·f) = c · M(f)`**。 -/
theorem M_const_mul (π : Fin 4 → ℝ) (lam la lb lc ld lx c : ℝ) (f : SitePat → ℝ) :
    M π lam la lb lc ld lx (fun p => c * f p) = c * M π lam la lb lc ld lx f := by
  simp only [M]
  simp only [mul_assoc]
  rw [← Finset.mul_sum]

/-- ★★ **背景项因子的期望**：`M(wBg u v) = 4π_Rπ_Y · M(fDiff u v)`。 -/
theorem M_wBg (π : Fin 4 → ℝ) (lam la lb lc ld lx : ℝ) (u v : Fin 4) :
    M π lam la lb lc ld lx (wBg π u v)
      = (4 * piR π * piY π) * M π lam la lb lc ld lx (fDiff u v) := by
  simp only [M, wBg]
  rw [show (∑ p : SitePat, 4 * piR π * piY π * fDiff u v p * q π lam la lb lc ld lx p)
        = ∑ p : SitePat, (4 * piR π * piY π)
            * (fDiff u v p * q π lam la lb lc ld lx p)
      from Finset.sum_congr rfl fun p _ => by ring]
  rw [Finset.mul_sum]

/-- ★★ **`E[w(ab|cd)]` 的「四项分解」**（把 `wLM1_ab_cd` 与 `sum_pair_prod` 合起来）。 -/
theorem E_ab_decomp (π : Fin 4 → ℝ) (lam la lb lc ld lx : ℝ) :
    E π .ab_cd lam la lb lc ld lx
      = M π lam la lb lc ld lx (fDiff 0 1) * M π lam la lb lc ld lx (fDiff 2 3)
        + M π lam la lb lc ld lx (fDiff 2 3) * M π lam la lb lc ld lx (fDiff 0 1)
        - M π lam la lb lc ld lx (wBg π 0 1) * M π lam la lb lc ld lx wNN
        - M π lam la lb lc ld lx (wBg π 2 3) * M π lam la lb lc ld lx wNN := by
  simp only [E, M]
  simp only [wLM1_ab_cd]
  simp only [add_mul, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp only [sum_pair_prod]

/-- ★★ **`E[w(ac|bd)]` 的「四项分解」**。 -/
theorem E_ac_decomp (π : Fin 4 → ℝ) (lam la lb lc ld lx : ℝ) :
    E π .ac_bd lam la lb lc ld lx
      = M π lam la lb lc ld lx (fDiff 0 2) * M π lam la lb lc ld lx (fDiff 1 3)
        + M π lam la lb lc ld lx (fDiff 1 3) * M π lam la lb lc ld lx (fDiff 0 2)
        - M π lam la lb lc ld lx (wBg π 0 2) * M π lam la lb lc ld lx wNN
        - M π lam la lb lc ld lx (wBg π 1 3) * M π lam la lb lc ld lx wNN := by
  simp only [E, M]
  simp only [wLM1_ac_bd]
  simp only [add_mul, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp only [sum_pair_prod]

/-- ★★ **`E[w(ab|cd)]`**（附录 1677–1692 行的化简式）：
`8 π_R²π_Y² e^{−λ L_T} − 8 π_R²π_Y²`，其中 `L_T = l_a+l_b+l_c+l_d`。 -/
theorem E_wLM1_ab_cd (π : Fin 4 → ℝ) (hsum : piR π + piY π = 1)
    (lam la lb lc ld lx : ℝ) :
    E π .ab_cd lam la lb lc ld lx
      = 8 * piR π ^ 2 * piY π ^ 2 * (ee lam (la + lb + lc + ld) - 1) := by
  rw [E_ab_decomp, M_one π hsum, M_wBg, M_wBg]
  rw [show M π lam la lb lc ld lx (fDiff 0 1)
        = 2 * (piR π * piY π * (1 - ee lam (la + lb)))
      from q_diff_ab π hsum lam la lb lc ld lx]
  rw [show M π lam la lb lc ld lx (fDiff 2 3)
        = 2 * (piR π * piY π * (1 - ee lam (lc + ld)))
      from q_diff_cd π hsum lam la lb lc ld lx]
  have he : ee lam (la + lb + lc + ld) = ee lam (la + lb) * ee lam (lc + ld) := by
    rw [show la + lb + lc + ld = (la + lb) + (lc + ld) by ring, ee_add]
  rw [he]
  ring

/-- ★★ **`E[w(ac|bd)]`**（附录 1697 行的化简式）：
`8 π_R²π_Y² e^{−λ(L_T+2 l_x)} − 8 π_R²π_Y²`。 -/
theorem E_wLM1_ac_bd (π : Fin 4 → ℝ) (hsum : piR π + piY π = 1)
    (lam la lb lc ld lx : ℝ) :
    E π .ac_bd lam la lb lc ld lx
      = 8 * piR π ^ 2 * piY π ^ 2 * (ee lam (la + lb + lc + ld + 2 * lx) - 1) := by
  rw [E_ac_decomp, M_one π hsum, M_wBg, M_wBg]
  rw [show M π lam la lb lc ld lx (fDiff 0 2)
        = 2 * (piR π * piY π * (1 - ee lam (la + lx + lc)))
      from q_diff_ac π hsum lam la lb lc ld lx]
  rw [show M π lam la lb lc ld lx (fDiff 1 3)
        = 2 * (piR π * piY π * (1 - ee lam (lb + lx + ld)))
      from q_diff_bd π hsum lam la lb lc ld lx]
  have he : ee lam (la + lb + lc + ld + 2 * lx)
      = ee lam (la + lx + lc) * ee lam (lb + lx + ld) := by
    rw [show la + lb + lc + ld + 2 * lx = (la + lx + lc) + (lb + lx + ld) by ring, ee_add]
  rw [he]
  ring

/-- ★★ **`E[w(ab|cd)]` 的展开形式**（与附录 1677–1689 行逐字对应）：
`8π_R²π_Y²(1−u)(1−v) − 8π_R²π_Y²(1−u) − 8π_R²π_Y²(1−v)`，
`u = e^{−λ(l_a+l_b)}`、`v = e^{−λ(l_c+l_d)}`。 -/
theorem E_wLM1_ab_cd_expanded (π : Fin 4 → ℝ) (hsum : piR π + piY π = 1)
    (lam la lb lc ld lx : ℝ) :
    E π .ab_cd lam la lb lc ld lx
      = 8 * piR π ^ 2 * piY π ^ 2 * (1 - ee lam (la + lb)) * (1 - ee lam (lc + ld))
        - 8 * piR π ^ 2 * piY π ^ 2 * (1 - ee lam (la + lb))
        - 8 * piR π ^ 2 * piY π ^ 2 * (1 - ee lam (lc + ld)) := by
  rw [E_wLM1_ab_cd π hsum lam la lb lc ld lx]
  have he : ee lam (la + lb + lc + ld) = ee lam (la + lb) * ee lam (lc + ld) := by
    rw [show la + lb + lc + ld = (la + lb) + (lc + ld) by ring, ee_add]
  rw [he]
  ring

/-- ★★ **`E[w(ac|bd)]` 的展开形式**（与附录 1690–1697 行逐字对应）。 -/
theorem E_wLM1_ac_bd_expanded (π : Fin 4 → ℝ) (hsum : piR π + piY π = 1)
    (lam la lb lc ld lx : ℝ) :
    E π .ac_bd lam la lb lc ld lx
      = 8 * piR π ^ 2 * piY π ^ 2 * (1 - ee lam (la + lx + lc))
          * (1 - ee lam (lb + lx + ld))
        - 8 * piR π ^ 2 * piY π ^ 2 * (1 - ee lam (la + lx + lc))
        - 8 * piR π ^ 2 * piY π ^ 2 * (1 - ee lam (lb + lx + ld)) := by
  rw [E_wLM1_ac_bd π hsum lam la lb lc ld lx]
  have he : ee lam (la + lb + lc + ld + 2 * lx)
      = ee lam (la + lx + lc) * ee lam (lb + lx + ld) := by
    rw [show la + lb + lc + ld + 2 * lx = (la + lx + lc) + (lb + lx + ld) by ring, ee_add]
  rw [he]
  ring

/-- ★★★ **命题 A（基因树层得分差闭式）**（附录 1699–1700 行）：

`E[w(ab|cd)] − E[w(ac|bd)] = 8 π_R²π_Y² e^{−λ L_T} (1 − e^{−2λ l_x})`，
其中 `L_T = l_a+l_b+l_c+l_d` 是基因树的总枝长（以替换单位计）。

这是 CASTER 主定理（LM1 模型下）的**基因树层**核心：右端对任意枝长均 `≥ 0`，
且仅当 `l_x = 0` 时取 `0` ⇒ 真物种树拓扑在期望意义下得分最高。 -/
theorem E_wLM1_ab_sub_ac (π : Fin 4 → ℝ) (hsum : piR π + piY π = 1)
    (lam la lb lc ld lx : ℝ) :
    E π .ab_cd lam la lb lc ld lx - E π .ac_bd lam la lb lc ld lx
      = 8 * piR π ^ 2 * piY π ^ 2 * ee lam (la + lb + lc + ld) * (1 - ee lam (2 * lx)) := by
  rw [E_wLM1_ab_cd π hsum lam la lb lc ld lx, E_wLM1_ac_bd π hsum lam la lb lc ld lx]
  have he : ee lam (la + lb + lc + ld + 2 * lx)
      = ee lam (la + lb + lc + ld) * ee lam (2 * lx) := by
    rw [show la + lb + lc + ld + 2 * lx = (la + lb + lc + ld) + 2 * lx by ring, ee_add]
  rw [he]
  ring

/-- ★★ **正性**：树内边长为正（`l_x > 0`）且 `λ > 0`、`π_R, π_Y > 0` 时，
真拓扑的期望得分**严格大于**错拓扑。 -/
theorem E_wLM1_sub_pos (π : Fin 4 → ℝ) (hsum : piR π + piY π = 1)
    (hR : 0 < piR π) (hY : 0 < piY π) {lam : ℝ} (hlam : 0 < lam)
    {la lb lc ld lx : ℝ} (hlx : 0 < lx) :
    0 < E π .ab_cd lam la lb lc ld lx - E π .ac_bd lam la lb lc ld lx := by
  rw [E_wLM1_ab_sub_ac π hsum lam la lb lc ld lx]
  have h1 : 0 < piR π ^ 2 := pow_pos hR 2
  have h2 : 0 < piY π ^ 2 := pow_pos hY 2
  have h3 : 0 < ee lam (la + lb + lc + ld) := ee_pos _ _
  have h4 : ee lam (2 * lx) < 1 := ee_lt_one (by nlinarith)
  have h5 : 0 < 1 - ee lam (2 * lx) := by linarith
  have h8 : (0 : ℝ) < 8 := by norm_num
  exact mul_pos (mul_pos (mul_pos (mul_pos h8 h1) h2) h3) h5

end

end Phylo.CASTERLM1
