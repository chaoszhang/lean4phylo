/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Mathlib.Tactic

/-!
# `Phylo.Stat.LMLumping` —— CASTER 的 LM 模型「可集总」引理

文献：Zhang, Nielsen, Mirarab (2025), *Science* **387**(6737) eadk9688,
**Supplementary** `sm.tex` 的 **Lemma `lemma:LM`**（陈述 **303–330** 行，证明 **1161–1195** 行）。

## 数学内容

LM1 是 GTR 的特例。字母表 `{A,G,C,T}`（`Fin 4` 编号 `0=A, 1=G, 2=C, 3=T`）。
把状态**集总**为两类：嘌呤 `R = {A,G}` 与嘧啶 `Y = {C,T}`。
**强集总（strong lumpability，Kemeny–Snell Thm 6.3.2）判据**是：

> 同类内的任意两个状态 `i, i'`，对**每个**类 `b`，到 `b` 的总转移率相等。

既然 `Q` 每行和为 `0`，每个类只需核对**一条**恒等式（另一条由行和相减得到）：

* `q^{AY} = q^{GY}` —— A 与 G 到嘧啶的总率相等（★★ `qAY_eq_qGY`）；
* `q^{CR} = q^{TR}` —— C 与 T 到嘌呤的总率相等（★★ `qCR_eq_qTR`）。

由这两条 + 行和为 `0`，★★★ `stronglyLumpable` 给出附录 Lemma 的判据。
再给出集总后 2 状态链的显式率矩阵（附录式 `eq:reduced`：★★ `rateRY_eq_qAY` / `rateYR_eq_qCR`）
与它自己的平稳性（★ `lumped_stationary`）。

## 关键代数（只用 `Ω`、`Φ` 的定义，**不需要**任何归一化假设）

记 `D_R = π_A+π_G`、`D_Y = π_C+π_T`。四条恒等式是全部证明的发动机
（`Ω`、`Φ` 的分母都是 `D_R·D_Y`，所以只需 `D_R·D_Y ≠ 0`）：

| 引理 | 恒等式 |
|---|---|
| ★ `Omega_add_Phi` | `D_Y (Ω+Φ) = 2(π_C−π_T)` |
| ★ `Omega_sub_Phi` | `D_R (Ω−Φ) = 2(π_A−π_G)` |
| ★ `pi_Omega_sub_pi_Phi` | `π_A Ω − π_G Φ = 2 π_C (π_A−π_G) / D_Y` |
| ★ `pi_Omega_add_pi_Phi` | `π_C Ω + π_T Φ = 2 π_A (π_C−π_T) / D_R` |

⚠️ **不需要 `Σπ = 1`** —— 这一点很重要：附录把 `π_C+π_T−1` 写成 `−(π_A+π_G)` 时
偷偷用了归一化，而本文件的四条恒等式与集总结论都**不依赖**它。

## 🔻 诚实边界

* 本文件只做**率矩阵（生成元）**一侧。附录 Lemma 的结论是「CTMC 可集总」；
  把生成元的集总提升为**转移半群** `e^{Qt}` 的集总需要矩阵指数 / CTMC 存在性那一层
  （`Matrix.exp`），本批**没有**做 —— 那属于概率层，与 `Phylo/Stat/Coalescent.lean` 同一层。
* **LM2 / LM3**（把 LM1 矩阵里的 `G↔T`、`G↔C` 对换）**留给后续批次**：
  它们的 `Q` 是 LM1 的 `Q` 在字母置换下的拉回，相应分类是 `R/Y` 在置换下的像
  （`swap G T` 下 `W = {A,T}` / `S = {C,G}`；`swap G C` 下 `M = {A,C}` / `K = {G,T}`）。
  要把本文件的判据搬过去，需要一个「`StronglyLumpable` 沿字母置换搬运」的引理
  （含对角元那条的 `Equiv.sum_comp` 重指标）—— 本批没做，**故不声称 LM2 / LM3 已证**。 -/

noncomputable section

namespace Phylo.Stat.LM

open Finset

/-- **LM1 模型的参数**：`pi` 是四个字母的平衡频率，`alpha beta gamma delta` 是替换率参数。

（附录 `sm.tex` 264 行起。`π` 的归一化不是本文件任何结论的前提。） -/
structure Params where
  /-- 平衡频率 `π_A, π_G, π_C, π_T`。 -/
  pi : Fin 4 → ℝ
  /-- 替换率参数 `α`。 -/
  alpha : ℝ
  /-- 替换率参数 `β`。 -/
  beta : ℝ
  /-- 替换率参数 `γ`。 -/
  gamma : ℝ
  /-- 替换率参数 `δ`。 -/
  delta : ℝ

namespace Params

variable (M : Params)

/-- **`Ω`**（附录 `sm.tex` 289 行）：`2(π_Aπ_C − π_Gπ_T) / (D_R D_Y)`。 -/
def Omega : ℝ :=
  2 * (M.pi 0 * M.pi 2 - M.pi 1 * M.pi 3) / ((M.pi 0 + M.pi 1) * (M.pi 2 + M.pi 3))

/-- **`Φ`**（附录 `sm.tex` 289 行）：`2(π_Gπ_C − π_Aπ_T) / (D_R D_Y)`。 -/
def Phi : ℝ :=
  2 * (M.pi 1 * M.pi 2 - M.pi 0 * M.pi 3) / ((M.pi 0 + M.pi 1) * (M.pi 2 + M.pi 3))

/-! ### 四条关键代数恒等式 -/

/-- ★ **`D_Y (Ω+Φ) = 2(π_C−π_T)`**（分子里 `π_Aπ_C+π_Gπ_C = D_R π_C`、`π_Gπ_T+π_Aπ_T = D_R π_T`）。 -/
theorem Omega_add_Phi (hden : (M.pi 0 + M.pi 1) * (M.pi 2 + M.pi 3) ≠ 0) :
    (M.pi 2 + M.pi 3) * (M.Omega + M.Phi) = 2 * (M.pi 2 - M.pi 3) := by
  have hR : M.pi 0 + M.pi 1 ≠ 0 := fun hz => hden (by rw [hz, zero_mul])
  have hY : M.pi 2 + M.pi 3 ≠ 0 := fun hz => hden (by rw [hz, mul_zero])
  have h : (M.pi 0 + M.pi 1) * (M.pi 2 + M.pi 3)
      * ((M.pi 2 + M.pi 3) * (M.Omega + M.Phi) - 2 * (M.pi 2 - M.pi 3)) = 0 := by
    simp only [Omega, Phi]
    field_simp
    ring
  have h2 := (mul_eq_zero.mp h).resolve_left hden
  linarith

/-- ★ **`D_R (Ω−Φ) = 2(π_A−π_G)`**。 -/
theorem Omega_sub_Phi (hden : (M.pi 0 + M.pi 1) * (M.pi 2 + M.pi 3) ≠ 0) :
    (M.pi 0 + M.pi 1) * (M.Omega - M.Phi) = 2 * (M.pi 0 - M.pi 1) := by
  have hR : M.pi 0 + M.pi 1 ≠ 0 := fun hz => hden (by rw [hz, zero_mul])
  have hY : M.pi 2 + M.pi 3 ≠ 0 := fun hz => hden (by rw [hz, mul_zero])
  have h : (M.pi 0 + M.pi 1) * (M.pi 2 + M.pi 3)
      * ((M.pi 0 + M.pi 1) * (M.Omega - M.Phi) - 2 * (M.pi 0 - M.pi 1)) = 0 := by
    simp only [Omega, Phi]
    field_simp
    ring
  have h2 := (mul_eq_zero.mp h).resolve_left hden
  linarith

/-- ★ **`π_A Ω − π_G Φ = 2 π_C (π_A−π_G) / D_Y`**。 -/
theorem pi_Omega_sub_pi_Phi (hden : (M.pi 0 + M.pi 1) * (M.pi 2 + M.pi 3) ≠ 0) :
    M.pi 0 * M.Omega - M.pi 1 * M.Phi
      = 2 * M.pi 2 * (M.pi 0 - M.pi 1) / (M.pi 2 + M.pi 3) := by
  have hR : M.pi 0 + M.pi 1 ≠ 0 := fun hz => hden (by rw [hz, zero_mul])
  have hY : M.pi 2 + M.pi 3 ≠ 0 := fun hz => hden (by rw [hz, mul_zero])
  have h : (M.pi 2 + M.pi 3)
      * (M.pi 0 * M.Omega - M.pi 1 * M.Phi
          - 2 * M.pi 2 * (M.pi 0 - M.pi 1) / (M.pi 2 + M.pi 3)) = 0 := by
    simp only [Omega, Phi]
    field_simp
    ring
  have h2 := (mul_eq_zero.mp h).resolve_left hY
  linarith

/-- ★ **`π_C Ω + π_T Φ = 2 π_A (π_C−π_T) / D_R`**。 -/
theorem pi_Omega_add_pi_Phi (hden : (M.pi 0 + M.pi 1) * (M.pi 2 + M.pi 3) ≠ 0) :
    M.pi 2 * M.Omega + M.pi 3 * M.Phi
      = 2 * M.pi 0 * (M.pi 2 - M.pi 3) / (M.pi 0 + M.pi 1) := by
  have hR : M.pi 0 + M.pi 1 ≠ 0 := fun hz => hden (by rw [hz, zero_mul])
  have hY : M.pi 2 + M.pi 3 ≠ 0 := fun hz => hden (by rw [hz, mul_zero])
  have h : (M.pi 0 + M.pi 1)
      * (M.pi 2 * M.Omega + M.pi 3 * M.Phi
          - 2 * M.pi 0 * (M.pi 2 - M.pi 3) / (M.pi 0 + M.pi 1)) = 0 := by
    simp only [Omega, Phi]
    field_simp
    ring
  have h2 := (mul_eq_zero.mp h).resolve_left hR
  linarith

/-! ### LM1 的率矩阵 -/

/-- **LM1 的完整率矩阵 `Q`**（附录 `sm.tex` 264–281 行）。
对角元取「该行非对角元之和」的相反数，故每行和为 `0`（★ `q_row_sum`）。 -/
def q : Fin 4 → Fin 4 → ℝ
  | 0, 0 => -(M.pi 1 * M.gamma + M.pi 2 * (M.alpha - M.beta + M.Omega * M.beta)
      + M.pi 3 * (M.alpha + M.beta + M.Phi * M.beta))
  | 0, 1 => M.pi 1 * M.gamma
  | 0, 2 => M.pi 2 * (M.alpha - M.beta + M.Omega * M.beta)
  | 0, 3 => M.pi 3 * (M.alpha + M.beta + M.Phi * M.beta)
  | 1, 0 => M.pi 0 * M.gamma
  | 1, 1 => -(M.pi 0 * M.gamma + M.pi 2 * (M.alpha + M.beta - M.Phi * M.beta)
      + M.pi 3 * (M.alpha - M.beta - M.Omega * M.beta))
  | 1, 2 => M.pi 2 * (M.alpha + M.beta - M.Phi * M.beta)
  | 1, 3 => M.pi 3 * (M.alpha - M.beta - M.Omega * M.beta)
  | 2, 0 => M.pi 0 * (M.alpha - M.beta + M.Omega * M.beta)
  | 2, 1 => M.pi 1 * (M.alpha + M.beta - M.Phi * M.beta)
  | 2, 2 => -(M.pi 0 * (M.alpha - M.beta + M.Omega * M.beta)
      + M.pi 1 * (M.alpha + M.beta - M.Phi * M.beta) + M.pi 3 * M.delta)
  | 2, 3 => M.pi 3 * M.delta
  | 3, 0 => M.pi 0 * (M.alpha + M.beta + M.Phi * M.beta)
  | 3, 1 => M.pi 1 * (M.alpha - M.beta - M.Omega * M.beta)
  | 3, 2 => M.pi 2 * M.delta
  | 3, 3 => -(M.pi 0 * (M.alpha + M.beta + M.Phi * M.beta)
      + M.pi 1 * (M.alpha - M.beta - M.Omega * M.beta) + M.pi 2 * M.delta)
  | _, _ => 0

/-- ★ **率矩阵每行和为 `0`**（对角元按定义即负的非对角元和）。 -/
theorem q_row_sum (i : Fin 4) : ∑ j : Fin 4, M.q i j = 0 := by
  fin_cases i <;> rw [Fin.sum_univ_four] <;> simp [q] <;> ring

/-! ### 集总后的聚合率（附录 `eq:reduced`） -/

/-- `R → Y` 的总率 `q^{AY} = q(A,C) + q(A,T)`。 -/
def qAY : ℝ := M.q 0 2 + M.q 0 3

/-- `G → Y` 的总率 `q^{GY} = q(G,C) + q(G,T)`。 -/
def qGY : ℝ := M.q 1 2 + M.q 1 3

/-- `C → R` 的总率 `q^{CR} = q(C,A) + q(C,G)`。 -/
def qCR : ℝ := M.q 2 0 + M.q 2 1

/-- `T → R` 的总率 `q^{TR} = q(T,A) + q(T,G)`。 -/
def qTR : ℝ := M.q 3 0 + M.q 3 1

/-- ★★ **集总判据之一**：`q^{AY} = q^{GY}`（A 与 G 到嘧啶的总率相等）。

展开后两边之差是 `β[(D_Y)(Ω+Φ) + 2(π_T−π_C)]`，由 ★ `Omega_add_Phi` 归零。 -/
theorem qAY_eq_qGY (hden : (M.pi 0 + M.pi 1) * (M.pi 2 + M.pi 3) ≠ 0) :
    M.qAY = M.qGY := by
  have h := M.Omega_add_Phi hden
  have hq : M.qAY - M.qGY
      = ((M.pi 2 + M.pi 3) * (M.Omega + M.Phi) - 2 * (M.pi 2 - M.pi 3)) * M.beta := by
    simp only [qAY, qGY, q]; ring
  have hz : M.qAY - M.qGY = 0 := by rw [hq, h]; ring
  linarith

/-- ★★ **集总判据之二**：`q^{CR} = q^{TR}`（C 与 T 到嘌呤的总率相等）。

展开后两边之差是 `β[(D_R)(Ω−Φ) + 2(π_G−π_A)]`，由 ★ `Omega_sub_Phi` 归零。 -/
theorem qCR_eq_qTR (hden : (M.pi 0 + M.pi 1) * (M.pi 2 + M.pi 3) ≠ 0) :
    M.qCR = M.qTR := by
  have h := M.Omega_sub_Phi hden
  have hq : M.qCR - M.qTR
      = ((M.pi 0 + M.pi 1) * (M.Omega - M.Phi) - 2 * (M.pi 0 - M.pi 1)) * M.beta := by
    simp only [qCR, qTR, q]; ring
  have hz : M.qCR - M.qTR = 0 := by rw [hq, h]; ring
  linarith

/-- **状态集总**：`R = {A,G} ↦ 0`、`Y = {C,T} ↦ 1`。 -/
def cls : Fin 4 → Fin 2
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | 3 => 1
  | _ => 1

theorem filter_cls_zero : (Finset.univ.filter (fun j : Fin 4 => cls j = 0)) = {0, 1} := by
  decide

theorem filter_cls_one : (Finset.univ.filter (fun j : Fin 4 => cls j = 1)) = {2, 3} := by
  decide

/-- **强集总（Kemeny–Snell）**：`cls` 把 4 个状态分成两类；若同一类内任意两状态
到**每个类**的行和都相等，则 `Q` 对 `cls` **强可集总**。

（`Q` 的行和必须为 `0`，即 `Q` 是某个 CTMC 的生成元。） -/
def StronglyLumpable (cls : Fin 4 → Fin 2) (Q : Fin 4 → Fin 4 → ℝ) : Prop :=
  (∀ i i' : Fin 4, cls i = cls i' →
      (∑ j ∈ Finset.univ.filter (fun j => cls j = 0), Q i j)
        = ∑ j ∈ Finset.univ.filter (fun j => cls j = 0), Q i' j) ∧
    (∀ i i' : Fin 4, cls i = cls i' →
      (∑ j ∈ Finset.univ.filter (fun j => cls j = 1), Q i j)
        = ∑ j ∈ Finset.univ.filter (fun j => cls j = 1), Q i' j)

/-- **判据化简**：行和为 `0` 时，只要两条聚合率等式成立，`Q` 就对 `R/Y` 分类强可集总。

四个「类内行和」等式中，类 `R` 的两条由行和相减得到（`Q i 0 + Q i 1 = −(Q i 2 + Q i 3)`），
类 `Y` 的两条一条是假设、一条由行和相减得到。 -/
theorem stronglyLumpable_of (Q : Fin 4 → Fin 4 → ℝ)
    (hrow : ∀ i, Q i 0 + Q i 1 + Q i 2 + Q i 3 = 0)
    (h1 : Q 0 2 + Q 0 3 = Q 1 2 + Q 1 3)
    (h2 : Q 2 0 + Q 2 1 = Q 3 0 + Q 3 1) :
    StronglyLumpable cls Q := by
  have hR : ∀ k : Fin 4,
      (∑ j ∈ Finset.univ.filter (fun j : Fin 4 => cls j = 0), Q k j) = Q k 0 + Q k 1 := by
    intro k; rw [filter_cls_zero, Finset.sum_pair (by decide)]
  have hY : ∀ k : Fin 4,
      (∑ j ∈ Finset.univ.filter (fun j : Fin 4 => cls j = 1), Q k j) = Q k 2 + Q k 3 := by
    intro k; rw [filter_cls_one, Finset.sum_pair (by decide)]
  constructor
  · intro i i' _
    rw [hR i, hR i']
    fin_cases i <;> fin_cases i' <;> simp_all [cls] <;>
      linarith [hrow 0, hrow 1, hrow 2, hrow 3, h1, h2]
  · intro i i' _
    rw [hY i, hY i']
    fin_cases i <;> fin_cases i' <;> simp_all [cls] <;>
      linarith [hrow 0, hrow 1, hrow 2, hrow 3, h1, h2]

/-- ★★★ **LM1 对 `R = {A,G}` / `Y = {C,T}` 分类强可集总**
（附录 Lemma `lemma:LM`；Kemeny–Snell Thm 6.3.2 的判据）。

由 ★★ `qAY_eq_qGY` + ★★ `qCR_eq_qTR` + ★ `q_row_sum` 经 `stronglyLumpable_of` 得到。 -/
theorem stronglyLumpable (hden : (M.pi 0 + M.pi 1) * (M.pi 2 + M.pi 3) ≠ 0) :
    StronglyLumpable cls M.q := by
  refine stronglyLumpable_of M.q (fun i => ?_) ?_ ?_
  · simpa [Fin.sum_univ_four] using M.q_row_sum i
  · simpa only [qAY, qGY, q] using M.qAY_eq_qGY hden
  · simpa only [qCR, qTR, q] using M.qCR_eq_qTR hden

/-! ### 集总后的 2 状态链（附录 `eq:reduced`） -/

/-- **集总后的 `R → Y` 率**：`D_Y α + (π_A−π_G)(π_C−π_T)β / D_R`。 -/
def rateRY : ℝ :=
  (M.pi 2 + M.pi 3) * M.alpha
    + (M.pi 0 - M.pi 1) * (M.pi 2 - M.pi 3) / (M.pi 0 + M.pi 1) * M.beta

/-- **集总后的 `Y → R` 率**：`D_R α + (π_A−π_G)(π_C−π_T)β / D_Y`。 -/
def rateYR : ℝ :=
  (M.pi 0 + M.pi 1) * M.alpha
    + (M.pi 0 - M.pi 1) * (M.pi 2 - M.pi 3) / (M.pi 2 + M.pi 3) * M.beta

/-- ★★ **附录 `eq:reduced` 的右上角就是聚合率 `q^{AY}`**。 -/
theorem rateRY_eq_qAY (hden : (M.pi 0 + M.pi 1) * (M.pi 2 + M.pi 3) ≠ 0) :
    M.rateRY = M.qAY := by
  have hR : M.pi 0 + M.pi 1 ≠ 0 := fun hz => hden (by rw [hz, zero_mul])
  have hY : M.pi 2 + M.pi 3 ≠ 0 := fun hz => hden (by rw [hz, mul_zero])
  have h := M.pi_Omega_add_pi_Phi hden
  have hq : M.qAY = (M.pi 2 + M.pi 3) * M.alpha + (M.pi 3 - M.pi 2) * M.beta
      + (M.pi 2 * M.Omega + M.pi 3 * M.Phi) * M.beta := by
    simp only [qAY, q]; ring
  rw [hq, h, rateRY]
  field_simp
  ring

/-- ★★ **附录 `eq:reduced` 的左下角就是聚合率 `q^{CR}`**。 -/
theorem rateYR_eq_qCR (hden : (M.pi 0 + M.pi 1) * (M.pi 2 + M.pi 3) ≠ 0) :
    M.rateYR = M.qCR := by
  have hR : M.pi 0 + M.pi 1 ≠ 0 := fun hz => hden (by rw [hz, zero_mul])
  have hY : M.pi 2 + M.pi 3 ≠ 0 := fun hz => hden (by rw [hz, mul_zero])
  have h := M.pi_Omega_sub_pi_Phi hden
  have hq : M.qCR = (M.pi 0 + M.pi 1) * M.alpha + (M.pi 1 - M.pi 0) * M.beta
      + (M.pi 0 * M.Omega - M.pi 1 * M.Phi) * M.beta := by
    simp only [qCR, q]; ring
  rw [hq, h, rateYR]
  field_simp
  ring

/-- ★ **集总链的平稳性**：`D_R · rateRY = D_Y · rateYR`（`π_R = D_R`、`π_Y = D_Y`）。

两边都等于 `D_R D_Y α + (π_A−π_G)(π_C−π_T) β`。 -/
theorem lumped_stationary (hden : (M.pi 0 + M.pi 1) * (M.pi 2 + M.pi 3) ≠ 0) :
    (M.pi 0 + M.pi 1) * M.rateRY = (M.pi 2 + M.pi 3) * M.rateYR := by
  have hR : M.pi 0 + M.pi 1 ≠ 0 := fun hz => hden (by rw [hz, zero_mul])
  have hY : M.pi 2 + M.pi 3 ≠ 0 := fun hz => hden (by rw [hz, mul_zero])
  simp only [rateRY, rateYR]
  field_simp
  try ring

end Params

end Phylo.Stat.LM
