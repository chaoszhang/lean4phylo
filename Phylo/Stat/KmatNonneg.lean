/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.Stat.CASTERF84
import Mathlib.Tactic

/-!
# `Phylo.Stat.KmatNonneg` —— `Kmat` 元素的**非负性与上界**（W13l 目标 2）

## 1. 要证什么

`Phylo/Stat/CASTERF84.lean:178` 定义 F84 转移核

```
Kmat pi kap lam t i j
  = pi j + sm lam t * (Bmat pi i j - pi j) + rm lam kap t * (δ_ij - Bmat pi i j)
sm lam t     = exp(-(lam * t))
rm lam kap t = exp(-(lam * (1 + kap) * t))
```

该文件 §2 明写「★ 随机性（行和）：`Kmat_row_sum`。**元素非负性未证**」，其 §6 缺口清单
（`CASTERF84PropA.lean` 之前的那份）与 `W13_SPEC.md` §6.1 #1 都把「`Kmat` 元素非负性」
登记为**未证缺口**。本文件补上它。

## 2. 三分情形（★D 真值判定：**条件面就是这三条**）

`Bmat` 是**逐元素字面写死**的（`CASTERF84.lean:143–160`）：同类内 `B_ij = π_j/p_cl ∈ [0,1]`，
**跨类** `B_ij = 0`。于是 `K_ij` 只有三种形状：

| 情形 | 形状 | 用到哪条假设 |
|---|---|---|
| **A 跨类**（如 `0,2`） | `K_ij = π_j·(1 − sm)` | **`lam*t ≥ 0`**（`sm ≤ 1`）——**唯一**用到它处，故它是**必要**的 |
| **B 对角**（`i = j`） | `K_ii = π_i(1 − sm) + sm(π_i/p_cl) + rm(1 − π_i/p_cl)` | 三项各自 `≥ 0`（**不需要** `kap`） |
| **C 同类非对角**（如 `0,1`） | `K_ij = π_j(1 − sm) + (sm − rm)·π_j/p_cl` | 还需 **`sm ≥ rm`** ⟺ `lam·kap·t ≥ 0`，即 **`kap ≥ 0`** |

⇒ 最终假设面 = `π > 0`（`Bmat` 的分母 `π_R`/`π_Y` 要非零）＋ `0 ≤ lam` ＋ `0 ≤ kap` ＋ `0 ≤ t`。
**反例（★D）**：

* `t < 0`（或 `lam < 0`）⇒ 情形 A 的 `π_j(1 − sm) < 0` ⇒ **非负性假**（该条件是必要的）；
* `kap < -1` 且 `lam·t > 0` ⇒ 情形 C 的 `sm − rm < 0` ⇒ **可为负**；
* `π` 有零分量（如 `π_2 = π_3 = 0`）⇒ `Bmat` 出现 `0/0`（Lean 约定为 `0`）⇒ 形状失真。

## 3. 上界 `Kmat ≤ 1`

`Kmat_row_sum`（行和 `= 1`）＋ 上面的元素非负性 ⇒ 第 `j` 项 `≤` 整行和 `= 1`。
（不需要 `π` 上界以外的任何新条件；`π` 只需非负即可。）

## 4. 退化一致性

* `t = 0` ⇒ `Kmat = I`：库内 `Kmat_zero`（`CASTERF84.lean:212`）已证，本文件另给**逐元素**形式；
* `kap = 0` ⇒ `rm = sm` ⇒ 情形 C 化为 `π_j(1 − sm)`（**F81** 形，只有 `π` 偏好）；本文件给出
  `Kmat_kap_zero`；
* `π ≡ (1/4)⁴` ⇒ `π_R = π_Y = 1/2` ⇒ **JC69** 的对称形（`Phylo.JC` 一族对照）。

## 5. 诚实边界

* 本文件**不改** `CASTERF84.lean` / `CASTERF84PropA.lean`（★C：只新增文件）；
* `Kmat` 是**自由 `lam`** 口径（与 `CASTERF84.lean` §3 边界 (a) 一致），
  不涉及 `lamF84 π κ` 的闭式（那是 `CASTERF84Pos.lean` 的范围）；
* 无占位证明、无新公理、无编译器求值捷径。
-/

set_option autoImplicit false

noncomputable section

open Finset

namespace Phylo.Stat.KmatNonneg

open Phylo.CASTERF84

/-! ## §0. 两条纯标量引理 -/

/-- `0 ≤ lam·t` ⇒ `sm lam t ≤ 1`。 -/
theorem sm_le_one {lam t : ℝ} (h : 0 ≤ lam * t) : sm lam t ≤ 1 := by
  unfold sm
  rw [Real.exp_le_one_iff]
  linarith

/-- `0 ≤ lam·kap·t` ⇒ `rm lam kap t ≤ sm lam t`（同底指数比较）。 -/
theorem rm_le_sm {lam kap t : ℝ} (h : 0 ≤ lam * kap * t) : rm lam kap t ≤ sm lam t := by
  unfold rm sm
  exact Real.exp_le_exp.mpr (by nlinarith)

/-- `π > 0` ⇒ `π_R > 0`。 -/
theorem piR_pos {pi : Fin 4 → ℝ} (hpos : ∀ i : Fin 4, 0 < pi i) : 0 < piR pi := by
  have h : 0 < pi 0 + pi 1 := add_pos (hpos 0) (hpos 1)
  simpa only [piR] using h

/-- `π > 0` ⇒ `π_Y > 0`。 -/
theorem piY_pos {pi : Fin 4 → ℝ} (hpos : ∀ i : Fin 4, 0 < pi i) : 0 < piY pi := by
  have h : 0 < pi 2 + pi 3 := add_pos (hpos 2) (hpos 3)
  simpa only [piY] using h

/-! ## §1. ★★★ 非负性（16 格 `fin_cases` 穷举，三种形状各自收口） -/

/-- ★★★ **W13_SPEC §6.1 #1 的缺口补完**：`0 ≤ Kmat π κ λ t i j`。

假设面 = `π > 0`（`Bmat` 分母）＋ `0 ≤ λ` ＋ `0 ≤ κ` ＋ `0 ≤ t`。
**不需要** `Σπ = 1`（非负性用不到归一化）。 -/
theorem Kmat_nonneg (pi : Fin 4 → ℝ) (kap lam t : ℝ) (i j : Fin 4)
    (hpos : ∀ i : Fin 4, 0 < pi i) (hlam : 0 ≤ lam) (hkap : 0 ≤ kap) (ht : 0 ≤ t) :
    0 ≤ Kmat pi kap lam t i j := by
  have hlt : 0 ≤ lam * t := mul_nonneg hlam ht
  have hs : sm lam t ≤ 1 := sm_le_one hlt
  have hrs : rm lam kap t ≤ sm lam t := rm_le_sm (mul_nonneg (mul_nonneg hlam hkap) ht)
  have hsm : 0 ≤ sm lam t := (sm_pos lam t).le
  have hrm : 0 ≤ rm lam kap t := (rm_pos lam kap t).le
  have hR : 0 < pi 0 + pi 1 := add_pos (hpos 0) (hpos 1)
  have hY : 0 < pi 2 + pi 3 := add_pos (hpos 2) (hpos 3)
  have g0 : 0 ≤ pi 0 / (pi 0 + pi 1) := div_nonneg (hpos 0).le hR.le
  have g1 : 0 ≤ pi 1 / (pi 0 + pi 1) := div_nonneg (hpos 1).le hR.le
  have g2 : 0 ≤ pi 2 / (pi 2 + pi 3) := div_nonneg (hpos 2).le hY.le
  have g3 : 0 ≤ pi 3 / (pi 2 + pi 3) := div_nonneg (hpos 3).le hY.le
  have e01 : (0 : Fin 4) ≠ 1 := by decide
  have e02 : (0 : Fin 4) ≠ 2 := by decide
  have e03 : (0 : Fin 4) ≠ 3 := by decide
  have e10 : (1 : Fin 4) ≠ 0 := by decide
  have e12 : (1 : Fin 4) ≠ 2 := by decide
  have e13 : (1 : Fin 4) ≠ 3 := by decide
  have e20 : (2 : Fin 4) ≠ 0 := by decide
  have e21 : (2 : Fin 4) ≠ 1 := by decide
  have e23 : (2 : Fin 4) ≠ 3 := by decide
  have e30 : (3 : Fin 4) ≠ 0 := by decide
  have e31 : (3 : Fin 4) ≠ 1 := by decide
  have e32 : (3 : Fin 4) ≠ 2 := by decide
  rw [Kmat_apply]
  fin_cases i <;> fin_cases j <;>
    simp only [Bmat, piR, piY, Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
      reduceIte, ite_eq_right e01, ite_eq_right e02, ite_eq_right e03, ite_eq_right e10,
      ite_eq_right e12, ite_eq_right e13, ite_eq_right e20, ite_eq_right e21,
      ite_eq_right e23, ite_eq_right e30, ite_eq_right e31, ite_eq_right e32,
      mul_zero, sub_self] <;>
    first
      | (nlinarith [hpos 0, hpos 1, hpos 2, hpos 3, hsm, hrm, hs, hrs, g0, g1, g2, g3])

/-! ## §2. ★★ 上界 `Kmat ≤ 1`（行和 ＋ 非负性） -/

/-- ★★ **`Kmat π κ λ t i j ≤ 1`**：由行和 `= 1` 与元素非负性（互补项非负）。 -/
theorem Kmat_le_one (pi : Fin 4 → ℝ) (kap lam t : ℝ) (i j : Fin 4)
    (hpos : ∀ i : Fin 4, 0 < pi i) (hsum : piR pi + piY pi = 1)
    (hlam : 0 ≤ lam) (hkap : 0 ≤ kap) (ht : 0 ≤ t) :
    Kmat pi kap lam t i j ≤ 1 := by
  have hnn : ∀ k : Fin 4, 0 ≤ Kmat pi kap lam t i k :=
    fun k => Kmat_nonneg pi kap lam t i k hpos hlam hkap ht
  have hrow := Kmat_row_sum pi hsum (ne_of_gt (piR_pos hpos)) (ne_of_gt (piY_pos hpos))
    kap lam t i
  have hsplit := Finset.add_sum_erase (Finset.univ : Finset (Fin 4))
    (fun k => Kmat pi kap lam t i k) (Finset.mem_univ j)
  have hrest : 0 ≤ ∑ k ∈ (Finset.univ.erase j), Kmat pi kap lam t i k :=
    Finset.sum_nonneg (fun k _ => hnn k)

  linarith

/-! ## §3. 退化一致性 -/

/-- ★★ **`t = 0` ⇒ 单位阵**（与库内 `Kmat_zero` 同内容，此处给 `≤`／`=` 的逐元素形式）。 -/
theorem Kmat_at_zero (pi : Fin 4 → ℝ) (kap lam : ℝ) (i j : Fin 4) :
    Kmat pi kap lam 0 i j = if i = j then 1 else 0 :=
  Kmat_zero pi kap lam i j

/-- ★★ **`kap = 0` ⇒ F81 形**（`rm = sm`，情形 C 化为 `π_j(1 − sm)`）——
   即「只有 `π` 偏好、无 transition/transversion 之分」的退化。 -/
theorem Kmat_kap_zero (pi : Fin 4 → ℝ) (lam t : ℝ) (i j : Fin 4) :
    Kmat pi 0 lam t i j = pi j + sm lam t * (Bmat pi i j - pi j)
      + sm lam t * ((if i = j then (1 : ℝ) else 0) - Bmat pi i j) := by
  rw [Kmat_apply]
  unfold rm sm
  ring_nf

/-- ★★ **等频退化（JC69 口径）**：`π ≡ 1/4` ⇒ `π_R = π_Y = 1/2`、`Bmat` 的两类内项都 `= 1/2`，
    于是 `sm` 与 `rm` 分别只乘在「类内」与「类外」——
    这里只落最常用的一条：`π_R = π_Y = 1/2`。 -/
theorem piR_piY_const_quarter :
    piR (fun _ : Fin 4 => (1 / 4 : ℝ)) = 1 / 2 ∧
      piY (fun _ : Fin 4 => (1 / 4 : ℝ)) = 1 / 2 := by
  constructor <;> norm_num [piR, piY]

end Phylo.Stat.KmatNonneg
