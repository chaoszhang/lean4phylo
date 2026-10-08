/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.Stat.CASTERF84Events

/-!
# `Phylo.Stat.CASTERF84Scaffold` —— F84 命题 A 的**推导脚手架**与三条主恒等式

规格：`CASTER_F84_PROPASPEC.md` §3.1。只依赖 `Phylo.Stat.CASTERF84Events`。

## 内容

* §2 有限和重排（把 `patt4` 的 `∑_{p,q}` 提到模式指标求和之外）；
* §3 脚手架 `Bmat_class_sum_R/Y`、`Kmat_col_R/Y`、`Kmat_class_sum_R/Y`、`Kmat_pair_sum_R/Y`
  —— 先把内层（模式指标）求和收成 `S_U(p,t)`、`D_U(p,q;t,t')`，**避免直接展开 16×4 重和**；
* §4 12 个侧向事件（对角 4 + `A` 4 + `B` 4）的闭式；
* §5 三条主恒等式 `Ew_diag` / `EwA_zero` / `EwB_zero`。

`sm lam t = e^{−λt}`、`rm lam kap t = e^{−λ(1+κ)t}` 在本文件中**只作原子**：
这三条恒等式是 `π_j` 与 `sm,rm` 的**有理函数恒等式**，不需要任何指数运算律。
-/

set_option maxHeartbeats 3200000
set_option maxRecDepth 100000

noncomputable section

namespace Phylo.Stat.CASTERF84Scaffold

open Finset
open Phylo.CASTERF84
open Phylo.Stat.CASTERF84Events

/-! ## §1 记号 -/

/-- 类频率 `p_U = ∑_{i∈U} π_i`。 -/
def pU (pi : Fin 4 → ℝ) (U : Finset (Fin 4)) : ℝ := ∑ i ∈ U, pi i

/-- 类内平方和 `q_U = ∑_{i∈U} π_i²`。 -/
def qU (pi : Fin 4 → ℝ) (U : Finset (Fin 4)) : ℝ := ∑ i ∈ U, pi i ^ 2

/-- `Kmat_col` 里的系数 `α`。 -/
def alphaU (pi : Fin 4 → ℝ) (kap lam : ℝ) (U : Finset (Fin 4)) (t : ℝ) (p : Fin 4) : ℝ :=
  (1 - sm lam t) + (if p ∈ U then 1 else 0) * (sm lam t - rm lam kap t) / pU pi U

/-- 类求和 `S_U(p,t) = ∑_{i∈U} K(t)_{p,i}`。 -/
def S (pi : Fin 4 → ℝ) (kap lam : ℝ) (U : Finset (Fin 4)) (p : Fin 4) (t : ℝ) : ℝ :=
  ∑ i ∈ U, Kmat pi kap lam t p i

/-- 配对和 `D_U(p,q;t,t') = ∑_{i∈U} K(t)_{p,i}·K(t')_{q,i}`。 -/
def D (pi : Fin 4 → ℝ) (kap lam : ℝ) (U : Finset (Fin 4)) (p q : Fin 4) (t t' : ℝ) : ℝ :=
  ∑ i ∈ U, Kmat pi kap lam t p i * Kmat pi kap lam t' q i

theorem pU_Rset (pi : Fin 4 → ℝ) : pU pi Rset = piR pi := by simp [pU, Rset, piR]

theorem pU_Yset (pi : Fin 4 → ℝ) : pU pi Yset = piY pi := by simp [pU, Yset, piY]

theorem qU_Rset (pi : Fin 4 → ℝ) : qU pi Rset = sqR pi := by simp [qU, Rset, sqR]

theorem qU_Yset (pi : Fin 4 → ℝ) : qU pi Yset = sqY pi := by simp [qU, Yset, sqY]

/-! ## §2 有限和重排：把 `∑_{p,q}` 提到模式指标求和之外 -/

/-- `∑_x ∑_p ∑_q → ∑_p ∑_q ∑_x`。 -/
theorem sum_comm_middle {ι : Type*} (s : Finset ι) (F : ι → Fin 4 → Fin 4 → ℝ) :
    (∑ x ∈ s, ∑ p : Fin 4, ∑ q : Fin 4, F x p q)
      = ∑ p : Fin 4, ∑ q : Fin 4, ∑ x ∈ s, F x p q := by
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun p _ => Finset.sum_comm)

/-- `∑_i ∑_j ∑_p ∑_q → ∑_p ∑_q ∑_i ∑_j`。 -/
theorem sum4_comm (U V : Finset (Fin 4)) (F : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) :
    (∑ i ∈ U, ∑ j ∈ V, ∑ p : Fin 4, ∑ q : Fin 4, F i j p q)
      = ∑ p : Fin 4, ∑ q : Fin 4, ∑ i ∈ U, ∑ j ∈ V, F i j p q := by
  rw [show (∑ i ∈ U, ∑ j ∈ V, ∑ p : Fin 4, ∑ q : Fin 4, F i j p q)
      = ∑ i ∈ U, ∑ p : Fin 4, ∑ j ∈ V, ∑ q : Fin 4, F i j p q from
    Finset.sum_congr rfl (fun i _ => Finset.sum_comm)]
  rw [show (∑ i ∈ U, ∑ p : Fin 4, ∑ j ∈ V, ∑ q : Fin 4, F i j p q)
      = ∑ p : Fin 4, ∑ i ∈ U, ∑ j ∈ V, ∑ q : Fin 4, F i j p q from Finset.sum_comm]
  rw [show (∑ p : Fin 4, ∑ i ∈ U, ∑ j ∈ V, ∑ q : Fin 4, F i j p q)
      = ∑ p : Fin 4, ∑ i ∈ U, ∑ q : Fin 4, ∑ j ∈ V, F i j p q from
    Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun i _ => Finset.sum_comm))]
  rw [show (∑ p : Fin 4, ∑ i ∈ U, ∑ q : Fin 4, ∑ j ∈ V, F i j p q)
      = ∑ p : Fin 4, ∑ q : Fin 4, ∑ i ∈ U, ∑ j ∈ V, F i j p q from
    Finset.sum_congr rfl (fun p _ => Finset.sum_comm)]

/-- `∑_i ∑_j ∑_p ∑_q → ∑_p ∑_q ∑_j ∑_i`（`mon` 家族用）。 -/
theorem perm_mon (U V : Finset (Fin 4)) (F : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) :
    (∑ i ∈ U, ∑ j ∈ V, ∑ p : Fin 4, ∑ q : Fin 4, F i j p q)
      = ∑ p : Fin 4, ∑ q : Fin 4, ∑ j ∈ V, ∑ i ∈ U, F i j p q := by
  rw [sum4_comm]
  exact Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => Finset.sum_comm))

/-- `∑_i ∑_j ∑_k ∑_p ∑_q → ∑_p ∑_q ∑_k ∑_j ∑_i`（`pureMon` 家族用）。 -/
theorem perm_pureMon (U V : Finset (Fin 4)) (F : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) :
    (∑ i ∈ U, ∑ j ∈ U, ∑ k ∈ V, ∑ p : Fin 4, ∑ q : Fin 4, F i j k p q)
      = ∑ p : Fin 4, ∑ q : Fin 4, ∑ k ∈ V, ∑ j ∈ U, ∑ i ∈ U, F i j k p q := by
  rw [show (∑ i ∈ U, ∑ j ∈ U, ∑ k ∈ V, ∑ p : Fin 4, ∑ q : Fin 4, F i j k p q)
      = ∑ i ∈ U, ∑ j ∈ U, ∑ p : Fin 4, ∑ q : Fin 4, ∑ k ∈ V, F i j k p q from
    Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => sum_comm_middle V _))]
  rw [sum4_comm U U (fun i j p q => ∑ k ∈ V, F i j k p q)]
  rw [show (∑ p : Fin 4, ∑ q : Fin 4, ∑ i ∈ U, ∑ j ∈ U, ∑ k ∈ V, F i j k p q)
      = ∑ p : Fin 4, ∑ q : Fin 4, ∑ i ∈ U, ∑ k ∈ V, ∑ j ∈ U, F i j k p q from
    Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ =>
      Finset.sum_congr rfl (fun i _ => Finset.sum_comm)))]
  rw [show (∑ p : Fin 4, ∑ q : Fin 4, ∑ i ∈ U, ∑ k ∈ V, ∑ j ∈ U, F i j k p q)
      = ∑ p : Fin 4, ∑ q : Fin 4, ∑ k ∈ V, ∑ i ∈ U, ∑ j ∈ U, F i j k p q from
    Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => Finset.sum_comm))]
  rw [show (∑ p : Fin 4, ∑ q : Fin 4, ∑ k ∈ V, ∑ i ∈ U, ∑ j ∈ U, F i j k p q)
      = ∑ p : Fin 4, ∑ q : Fin 4, ∑ k ∈ V, ∑ j ∈ U, ∑ i ∈ U, F i j k p q from
    Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ =>
      Finset.sum_congr rfl (fun k _ => Finset.sum_comm)))]

/-- `∑_i ∑_k ∑_l ∑_p ∑_q → ∑_p ∑_q ∑_l ∑_k ∑_i`（`monPure` 家族用）。 -/
theorem perm_monPure (U V : Finset (Fin 4)) (F : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) :
    (∑ i ∈ U, ∑ k ∈ V, ∑ l ∈ V, ∑ p : Fin 4, ∑ q : Fin 4, F i k l p q)
      = ∑ p : Fin 4, ∑ q : Fin 4, ∑ l ∈ V, ∑ k ∈ V, ∑ i ∈ U, F i k l p q := by
  rw [show (∑ i ∈ U, ∑ k ∈ V, ∑ l ∈ V, ∑ p : Fin 4, ∑ q : Fin 4, F i k l p q)
      = ∑ i ∈ U, ∑ k ∈ V, ∑ p : Fin 4, ∑ q : Fin 4, ∑ l ∈ V, F i k l p q from
    Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun k _ => sum_comm_middle V _))]
  rw [sum4_comm U V (fun i k p q => ∑ l ∈ V, F i k l p q)]
  rw [show (∑ p : Fin 4, ∑ q : Fin 4, ∑ i ∈ U, ∑ k ∈ V, ∑ l ∈ V, F i k l p q)
      = ∑ p : Fin 4, ∑ q : Fin 4, ∑ i ∈ U, ∑ l ∈ V, ∑ k ∈ V, F i k l p q from
    Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ =>
      Finset.sum_congr rfl (fun i _ => Finset.sum_comm)))]
  rw [show (∑ p : Fin 4, ∑ q : Fin 4, ∑ i ∈ U, ∑ l ∈ V, ∑ k ∈ V, F i k l p q)
      = ∑ p : Fin 4, ∑ q : Fin 4, ∑ l ∈ V, ∑ i ∈ U, ∑ k ∈ V, F i k l p q from
    Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => Finset.sum_comm))]
  rw [show (∑ p : Fin 4, ∑ q : Fin 4, ∑ l ∈ V, ∑ i ∈ U, ∑ k ∈ V, F i k l p q)
      = ∑ p : Fin 4, ∑ q : Fin 4, ∑ l ∈ V, ∑ k ∈ V, ∑ i ∈ U, F i k l p q from
    Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ =>
      Finset.sum_congr rfl (fun l _ => Finset.sum_comm)))]

/-- `∑_i ∑_j ∑_k ∑_l ∑_p ∑_q → ∑_p ∑_q ∑_l ∑_k ∑_j ∑_i`（`pureAll` 家族用）。 -/
theorem perm_pureAll (U V : Finset (Fin 4))
    (F : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) :
    (∑ i ∈ U, ∑ j ∈ U, ∑ k ∈ V, ∑ l ∈ V, ∑ p : Fin 4, ∑ q : Fin 4, F i j k l p q)
      = ∑ p : Fin 4, ∑ q : Fin 4, ∑ l ∈ V, ∑ k ∈ V, ∑ j ∈ U, ∑ i ∈ U, F i j k l p q := by
  rw [show (∑ i ∈ U, ∑ j ∈ U, ∑ k ∈ V, ∑ l ∈ V, ∑ p : Fin 4, ∑ q : Fin 4, F i j k l p q)
      = ∑ i ∈ U, ∑ j ∈ U, ∑ k ∈ V, ∑ p : Fin 4, ∑ q : Fin 4, ∑ l ∈ V, F i j k l p q from
    Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ =>
      Finset.sum_congr rfl (fun k _ => sum_comm_middle V _)))]
  rw [show (∑ i ∈ U, ∑ j ∈ U, ∑ k ∈ V, ∑ p : Fin 4, ∑ q : Fin 4, ∑ l ∈ V, F i j k l p q)
      = ∑ i ∈ U, ∑ j ∈ U, ∑ p : Fin 4, ∑ q : Fin 4, ∑ k ∈ V, ∑ l ∈ V, F i j k l p q from
    Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ =>
      sum_comm_middle V (fun k p q => ∑ l ∈ V, F i j k l p q)))]
  rw [sum4_comm U U (fun i j p q => ∑ k ∈ V, ∑ l ∈ V, F i j k l p q)]
  rw [show (∑ p : Fin 4, ∑ q : Fin 4, ∑ i ∈ U, ∑ j ∈ U, ∑ k ∈ V, ∑ l ∈ V, F i j k l p q)
      = ∑ p : Fin 4, ∑ q : Fin 4, ∑ i ∈ U, ∑ j ∈ U, ∑ l ∈ V, ∑ k ∈ V, F i j k l p q from
    Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ =>
      Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => Finset.sum_comm))))]
  rw [show (∑ p : Fin 4, ∑ q : Fin 4, ∑ i ∈ U, ∑ j ∈ U, ∑ l ∈ V, ∑ k ∈ V, F i j k l p q)
      = ∑ p : Fin 4, ∑ q : Fin 4, ∑ i ∈ U, ∑ l ∈ V, ∑ j ∈ U, ∑ k ∈ V, F i j k l p q from
    Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ =>
      Finset.sum_congr rfl (fun i _ => Finset.sum_comm)))]
  rw [show (∑ p : Fin 4, ∑ q : Fin 4, ∑ i ∈ U, ∑ l ∈ V, ∑ j ∈ U, ∑ k ∈ V, F i j k l p q)
      = ∑ p : Fin 4, ∑ q : Fin 4, ∑ l ∈ V, ∑ i ∈ U, ∑ j ∈ U, ∑ k ∈ V, F i j k l p q from
    Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => Finset.sum_comm))]
  rw [show (∑ p : Fin 4, ∑ q : Fin 4, ∑ l ∈ V, ∑ i ∈ U, ∑ j ∈ U, ∑ k ∈ V, F i j k l p q)
      = ∑ p : Fin 4, ∑ q : Fin 4, ∑ l ∈ V, ∑ i ∈ U, ∑ k ∈ V, ∑ j ∈ U, F i j k l p q from
    Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ =>
      Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun i _ => Finset.sum_comm))))]
  rw [show (∑ p : Fin 4, ∑ q : Fin 4, ∑ l ∈ V, ∑ i ∈ U, ∑ k ∈ V, ∑ j ∈ U, F i j k l p q)
      = ∑ p : Fin 4, ∑ q : Fin 4, ∑ l ∈ V, ∑ k ∈ V, ∑ i ∈ U, ∑ j ∈ U, F i j k l p q from
    Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ =>
      Finset.sum_congr rfl (fun l _ => Finset.sum_comm)))]
  rw [show (∑ p : Fin 4, ∑ q : Fin 4, ∑ l ∈ V, ∑ k ∈ V, ∑ i ∈ U, ∑ j ∈ U, F i j k l p q)
      = ∑ p : Fin 4, ∑ q : Fin 4, ∑ l ∈ V, ∑ k ∈ V, ∑ j ∈ U, ∑ i ∈ U, F i j k l p q from
    Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ =>
      Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun k _ => Finset.sum_comm))))]

/-! ## §3 脚手架 -/

/-- 类集合 `Rset` 上 `Bmat` 的列和。 -/
theorem Bmat_class_sum_R (pi : Fin 4 → ℝ) (hR : piR pi ≠ 0) (p : Fin 4) :
    ∑ i ∈ Rset, Bmat pi p i = if p ∈ Rset then (1 : ℝ) else 0 := by
  simp only [piR] at hR
  fin_cases p <;> simp [Rset, Bmat, piR] <;> field_simp

/-- 类集合 `Yset` 上 `Bmat` 的列和。 -/
theorem Bmat_class_sum_Y (pi : Fin 4 → ℝ) (hY : piY pi ≠ 0) (p : Fin 4) :
    ∑ i ∈ Yset, Bmat pi p i = if p ∈ Yset then (1 : ℝ) else 0 := by
  simp only [piY] at hY
  fin_cases p <;> simp [Yset, Bmat, piY] <;> field_simp

/-- ★ **`Kmat` 的列分解**（`Rset` 侧）。 -/
theorem Kmat_col_R (pi : Fin 4 → ℝ) (kap lam : ℝ) (hR : piR pi ≠ 0)
    {p i : Fin 4} (hi : i ∈ Rset) (t : ℝ) :
    Kmat pi kap lam t p i
      = pi i * ((1 - sm lam t)
          + (if p ∈ Rset then (1 : ℝ) else 0) * (sm lam t - rm lam kap t) / piR pi)
        + rm lam kap t * (if p = i then (1 : ℝ) else 0) := by
  simp only [piR] at hR
  fin_cases p <;> fin_cases i <;>
    simp_all [Rset, Bmat, P0, P1, P2, Kmat, piR] <;> field_simp <;> ring

/-- ★ **`Kmat` 的列分解**（`Yset` 侧）。 -/
theorem Kmat_col_Y (pi : Fin 4 → ℝ) (kap lam : ℝ) (hY : piY pi ≠ 0)
    {p i : Fin 4} (hi : i ∈ Yset) (t : ℝ) :
    Kmat pi kap lam t p i
      = pi i * ((1 - sm lam t)
          + (if p ∈ Yset then (1 : ℝ) else 0) * (sm lam t - rm lam kap t) / piY pi)
        + rm lam kap t * (if p = i then (1 : ℝ) else 0) := by
  simp only [piY] at hY
  fin_cases p <;> fin_cases i <;>
    simp_all [Yset, Bmat, P0, P1, P2, Kmat, piY] <;> field_simp <;> ring

/-- ★ **`Kmat` 的类求和闭式**（`Rset` 侧）。 -/
theorem Kmat_class_sum_R (pi : Fin 4 → ℝ) (kap lam : ℝ) (hR : piR pi ≠ 0)
    (p : Fin 4) (t : ℝ) :
    ∑ i ∈ Rset, Kmat pi kap lam t p i
      = sm lam t * (if p ∈ Rset then (1 : ℝ) else 0) + (1 - sm lam t) * piR pi := by
  simp only [piR] at hR
  fin_cases p <;> simp [Rset, Bmat, P0, P1, P2, Kmat, piR] <;> field_simp <;> ring

/-- ★ **`Kmat` 的类求和闭式**（`Yset` 侧）。 -/
theorem Kmat_class_sum_Y (pi : Fin 4 → ℝ) (kap lam : ℝ) (hY : piY pi ≠ 0)
    (p : Fin 4) (t : ℝ) :
    ∑ i ∈ Yset, Kmat pi kap lam t p i
      = sm lam t * (if p ∈ Yset then (1 : ℝ) else 0) + (1 - sm lam t) * piY pi := by
  simp only [piY] at hY
  fin_cases p <;> simp [Yset, Bmat, P0, P1, P2, Kmat, piY] <;> field_simp <;> ring

/-- ★★ **`Kmat` 的类配对和闭式**（`Rset` 侧）。 -/
theorem Kmat_pair_sum_R (pi : Fin 4 → ℝ) (kap lam : ℝ) (hR : piR pi ≠ 0)
    (p q : Fin 4) (t t' : ℝ) :
    ∑ i ∈ Rset, Kmat pi kap lam t p i * Kmat pi kap lam t' q i
      = ((1 - sm lam t)
            + (if p ∈ Rset then (1 : ℝ) else 0) * (sm lam t - rm lam kap t) / piR pi)
          * ((1 - sm lam t')
            + (if q ∈ Rset then (1 : ℝ) else 0) * (sm lam t' - rm lam kap t') / piR pi)
          * sqR pi
        + ((1 - sm lam t')
            + (if q ∈ Rset then (1 : ℝ) else 0) * (sm lam t' - rm lam kap t') / piR pi)
          * rm lam kap t * (if p ∈ Rset then pi p else 0)
        + ((1 - sm lam t)
            + (if p ∈ Rset then (1 : ℝ) else 0) * (sm lam t - rm lam kap t) / piR pi)
          * rm lam kap t' * (if q ∈ Rset then pi q else 0)
        + rm lam kap t * rm lam kap t'
          * (if p = q ∧ p ∈ Rset then (1 : ℝ) else 0) := by
  simp only [piR] at hR
  fin_cases p <;> fin_cases q <;>
    simp [Rset, Bmat, P0, P1, P2, Kmat, piR, sqR] <;> field_simp <;> ring

/-- ★★ **`Kmat` 的类配对和闭式**（`Yset` 侧）。 -/
theorem Kmat_pair_sum_Y (pi : Fin 4 → ℝ) (kap lam : ℝ) (hY : piY pi ≠ 0)
    (p q : Fin 4) (t t' : ℝ) :
    ∑ i ∈ Yset, Kmat pi kap lam t p i * Kmat pi kap lam t' q i
      = ((1 - sm lam t)
            + (if p ∈ Yset then (1 : ℝ) else 0) * (sm lam t - rm lam kap t) / piY pi)
          * ((1 - sm lam t')
            + (if q ∈ Yset then (1 : ℝ) else 0) * (sm lam t' - rm lam kap t') / piY pi)
          * sqY pi
        + ((1 - sm lam t')
            + (if q ∈ Yset then (1 : ℝ) else 0) * (sm lam t' - rm lam kap t') / piY pi)
          * rm lam kap t * (if p ∈ Yset then pi p else 0)
        + ((1 - sm lam t)
            + (if p ∈ Yset then (1 : ℝ) else 0) * (sm lam t - rm lam kap t) / piY pi)
          * rm lam kap t' * (if q ∈ Yset then pi q else 0)
        + rm lam kap t * rm lam kap t'
          * (if p = q ∧ p ∈ Yset then (1 : ℝ) else 0) := by
  simp only [piY] at hY
  fin_cases p <;> fin_cases q <;>
    simp [Yset, Bmat, P0, P1, P2, Kmat, piY, sqY] <;> field_simp <;> ring

/-! ### §3.1 `S`/`D` 形式的改写（供 §4/§5 直接使用） -/

theorem S_Rset (pi : Fin 4 → ℝ) (kap lam : ℝ) (hR : piR pi ≠ 0) (p : Fin 4) (t : ℝ) :
    S pi kap lam Rset p t
      = sm lam t * (if p ∈ Rset then (1 : ℝ) else 0) + (1 - sm lam t) * pU pi Rset := by
  rw [S, Kmat_class_sum_R pi kap lam hR p t, pU_Rset]

theorem S_Yset (pi : Fin 4 → ℝ) (kap lam : ℝ) (hY : piY pi ≠ 0) (p : Fin 4) (t : ℝ) :
    S pi kap lam Yset p t
      = sm lam t * (if p ∈ Yset then (1 : ℝ) else 0) + (1 - sm lam t) * pU pi Yset := by
  rw [S, Kmat_class_sum_Y pi kap lam hY p t, pU_Yset]

theorem D_Rset (pi : Fin 4 → ℝ) (kap lam : ℝ) (hR : piR pi ≠ 0) (p q : Fin 4) (t t' : ℝ) :
    D pi kap lam Rset p q t t'
      = ((1 - sm lam t)
            + (if p ∈ Rset then (1 : ℝ) else 0) * (sm lam t - rm lam kap t) / piR pi)
          * ((1 - sm lam t')
            + (if q ∈ Rset then (1 : ℝ) else 0) * (sm lam t' - rm lam kap t') / piR pi)
          * sqR pi
        + ((1 - sm lam t')
            + (if q ∈ Rset then (1 : ℝ) else 0) * (sm lam t' - rm lam kap t') / piR pi)
          * rm lam kap t * (if p ∈ Rset then pi p else 0)
        + ((1 - sm lam t)
            + (if p ∈ Rset then (1 : ℝ) else 0) * (sm lam t - rm lam kap t) / piR pi)
          * rm lam kap t' * (if q ∈ Rset then pi q else 0)
        + rm lam kap t * rm lam kap t'
          * (if p = q ∧ p ∈ Rset then (1 : ℝ) else 0) := by
  rw [D, Kmat_pair_sum_R pi kap lam hR p q t t']

theorem D_Yset (pi : Fin 4 → ℝ) (kap lam : ℝ) (hY : piY pi ≠ 0) (p q : Fin 4) (t t' : ℝ) :
    D pi kap lam Yset p q t t'
      = ((1 - sm lam t)
            + (if p ∈ Yset then (1 : ℝ) else 0) * (sm lam t - rm lam kap t) / piY pi)
          * ((1 - sm lam t')
            + (if q ∈ Yset then (1 : ℝ) else 0) * (sm lam t' - rm lam kap t') / piY pi)
          * sqY pi
        + ((1 - sm lam t')
            + (if q ∈ Yset then (1 : ℝ) else 0) * (sm lam t' - rm lam kap t') / piY pi)
          * rm lam kap t * (if p ∈ Yset then pi p else 0)
        + ((1 - sm lam t)
            + (if p ∈ Yset then (1 : ℝ) else 0) * (sm lam t - rm lam kap t) / piY pi)
          * rm lam kap t' * (if q ∈ Yset then pi q else 0)
        + rm lam kap t * rm lam kap t'
          * (if p = q ∧ p ∈ Yset then (1 : ℝ) else 0) := by
  rw [D, Kmat_pair_sum_Y pi kap lam hY p q t t']

/-! ## §4 12 个侧向事件的闭式（对角 4 + `A` 4 + `B` 4） -/

/-- ★★ **`mon` 的闭式**（对角分组）。 -/
theorem mon_closed (pi : Fin 4 → ℝ) (kap lam t1 t2 tx t3 t4 : ℝ) (U V : Finset (Fin 4)) :
    mon pi kap lam t1 t2 tx t3 t4 U V
      = ∑ p : Fin 4, ∑ q : Fin 4,
          (pi p * Kmat pi kap lam tx p q)
            * (D pi kap lam U p p t1 t2 * D pi kap lam V q q t3 t4) := by
  have h : mon pi kap lam t1 t2 tx t3 t4 U V
      = ∑ p : Fin 4, ∑ q : Fin 4, ∑ j ∈ V, ∑ i ∈ U,
          (pi p * Kmat pi kap lam tx p q)
            * ((Kmat pi kap lam t1 p i * Kmat pi kap lam t2 p i)
               * (Kmat pi kap lam t3 q j * Kmat pi kap lam t4 q j)) := by
    simp only [mon, patt4]
    rw [perm_mon]
    refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => ?_))
    refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun i _ => ?_))
    ring
  rw [h]
  refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => ?_))
  simp only [D, Finset.mul_sum, Finset.sum_mul]

/-- ★★ **`pureMon` 的闭式**（对角分组）。 -/
theorem pureMon_closed (pi : Fin 4 → ℝ) (kap lam t1 t2 tx t3 t4 : ℝ) (U V : Finset (Fin 4)) :
    pureMon pi kap lam t1 t2 tx t3 t4 U V
      = ∑ p : Fin 4, ∑ q : Fin 4,
          (pi p * Kmat pi kap lam tx p q)
            * (S pi kap lam U p t1 * S pi kap lam U p t2 * D pi kap lam V q q t3 t4) := by
  have h : pureMon pi kap lam t1 t2 tx t3 t4 U V
      = ∑ p : Fin 4, ∑ q : Fin 4, ∑ k ∈ V, ∑ j ∈ U, ∑ i ∈ U,
          (pi p * Kmat pi kap lam tx p q)
            * ((Kmat pi kap lam t1 p i * Kmat pi kap lam t2 p j)
               * (Kmat pi kap lam t3 q k * Kmat pi kap lam t4 q k)) := by
    simp only [pureMon, patt4]
    rw [perm_pureMon]
    refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => ?_))
    refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun j _ =>
      Finset.sum_congr rfl (fun i _ => ?_)))
    ring
  rw [h]
  refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => ?_))
  simp only [S, D, Finset.mul_sum, Finset.sum_mul]

/-- ★★ **`monPure` 的闭式**（对角分组）。 -/
theorem monPure_closed (pi : Fin 4 → ℝ) (kap lam t1 t2 tx t3 t4 : ℝ) (U V : Finset (Fin 4)) :
    monPure pi kap lam t1 t2 tx t3 t4 U V
      = ∑ p : Fin 4, ∑ q : Fin 4,
          (pi p * Kmat pi kap lam tx p q)
            * (D pi kap lam U p p t1 t2 * S pi kap lam V q t3 * S pi kap lam V q t4) := by
  have h : monPure pi kap lam t1 t2 tx t3 t4 U V
      = ∑ p : Fin 4, ∑ q : Fin 4, ∑ l ∈ V, ∑ k ∈ V, ∑ i ∈ U,
          (pi p * Kmat pi kap lam tx p q)
            * ((Kmat pi kap lam t1 p i * Kmat pi kap lam t2 p i)
               * (Kmat pi kap lam t3 q k * Kmat pi kap lam t4 q l)) := by
    simp only [monPure, patt4]
    rw [perm_monPure]
    refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => ?_))
    refine Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun k _ =>
      Finset.sum_congr rfl (fun i _ => ?_)))
    ring
  rw [h]
  refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => ?_))
  simp only [S, D, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun k _ =>
    Finset.sum_congr rfl (fun i _ => ?_)))
  ring

/-- ★★ **`pureAll` 的闭式**（对角分组）。 -/
theorem pureAll_closed (pi : Fin 4 → ℝ) (kap lam t1 t2 tx t3 t4 : ℝ) (U V : Finset (Fin 4)) :
    pureAll pi kap lam t1 t2 tx t3 t4 U V
      = ∑ p : Fin 4, ∑ q : Fin 4,
          (pi p * Kmat pi kap lam tx p q)
            * (S pi kap lam U p t1 * S pi kap lam U p t2
               * (S pi kap lam V q t3 * S pi kap lam V q t4)) := by
  have h : pureAll pi kap lam t1 t2 tx t3 t4 U V
      = ∑ p : Fin 4, ∑ q : Fin 4, ∑ l ∈ V, ∑ k ∈ V, ∑ j ∈ U, ∑ i ∈ U,
          (pi p * Kmat pi kap lam tx p q)
            * ((Kmat pi kap lam t1 p i * Kmat pi kap lam t2 p j)
               * (Kmat pi kap lam t3 q k * Kmat pi kap lam t4 q l)) := by
    simp only [pureAll, patt4]
    rw [perm_pureAll]
    refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => ?_))
    refine Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun k _ =>
      Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun i _ => ?_))))
    ring
  rw [h]
  refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => ?_))
  simp only [S, Finset.mul_sum, Finset.sum_mul]

/-- ★★ **`monA` 的闭式**（跨结点分组 `{0,2}/{1,3}`）。 -/
theorem monA_closed (pi : Fin 4 → ℝ) (kap lam t1 t2 tx t3 t4 : ℝ) (U V : Finset (Fin 4)) :
    monA pi kap lam t1 t2 tx t3 t4 U V
      = ∑ p : Fin 4, ∑ q : Fin 4,
          (pi p * Kmat pi kap lam tx p q)
            * (D pi kap lam U p q t1 t3 * D pi kap lam V p q t2 t4) := by
  have h : monA pi kap lam t1 t2 tx t3 t4 U V
      = ∑ p : Fin 4, ∑ q : Fin 4, ∑ j ∈ V, ∑ i ∈ U,
          (pi p * Kmat pi kap lam tx p q)
            * ((Kmat pi kap lam t1 p i * Kmat pi kap lam t3 q i)
               * (Kmat pi kap lam t2 p j * Kmat pi kap lam t4 q j)) := by
    simp only [monA, patt4]
    rw [perm_mon]
    refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => ?_))
    refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun i _ => ?_))
    ring
  rw [h]
  refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => ?_))
  simp only [D, Finset.mul_sum, Finset.sum_mul]

/-- ★★ **`pureMonA` 的闭式**。 -/
theorem pureMonA_closed (pi : Fin 4 → ℝ) (kap lam t1 t2 tx t3 t4 : ℝ) (U V : Finset (Fin 4)) :
    pureMonA pi kap lam t1 t2 tx t3 t4 U V
      = ∑ p : Fin 4, ∑ q : Fin 4,
          (pi p * Kmat pi kap lam tx p q)
            * (S pi kap lam U p t1 * S pi kap lam U q t3 * D pi kap lam V p q t2 t4) := by
  have h : pureMonA pi kap lam t1 t2 tx t3 t4 U V
      = ∑ p : Fin 4, ∑ q : Fin 4, ∑ k ∈ V, ∑ j ∈ U, ∑ i ∈ U,
          (pi p * Kmat pi kap lam tx p q)
            * ((Kmat pi kap lam t1 p i * Kmat pi kap lam t3 q j)
               * (Kmat pi kap lam t2 p k * Kmat pi kap lam t4 q k)) := by
    simp only [pureMonA, patt4]
    rw [perm_pureMon]
    refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => ?_))
    refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun j _ =>
      Finset.sum_congr rfl (fun i _ => ?_)))
    ring
  rw [h]
  refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => ?_))
  simp only [S, D, Finset.mul_sum, Finset.sum_mul]

/-- ★★ **`monPureA` 的闭式**。 -/
theorem monPureA_closed (pi : Fin 4 → ℝ) (kap lam t1 t2 tx t3 t4 : ℝ) (U V : Finset (Fin 4)) :
    monPureA pi kap lam t1 t2 tx t3 t4 U V
      = ∑ p : Fin 4, ∑ q : Fin 4,
          (pi p * Kmat pi kap lam tx p q)
            * (D pi kap lam U p q t1 t3 * S pi kap lam V p t2 * S pi kap lam V q t4) := by
  have h : monPureA pi kap lam t1 t2 tx t3 t4 U V
      = ∑ p : Fin 4, ∑ q : Fin 4, ∑ l ∈ V, ∑ k ∈ V, ∑ i ∈ U,
          (pi p * Kmat pi kap lam tx p q)
            * ((Kmat pi kap lam t1 p i * Kmat pi kap lam t3 q i)
               * (Kmat pi kap lam t2 p k * Kmat pi kap lam t4 q l)) := by
    simp only [monPureA, patt4]
    rw [perm_monPure]
    refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => ?_))
    refine Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun k _ =>
      Finset.sum_congr rfl (fun i _ => ?_)))
    ring
  rw [h]
  refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => ?_))
  simp only [S, D, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun k _ =>
    Finset.sum_congr rfl (fun i _ => ?_)))
  ring

/-- ★★ **`pureAllA` 的闭式**。 -/
theorem pureAllA_closed (pi : Fin 4 → ℝ) (kap lam t1 t2 tx t3 t4 : ℝ) (U V : Finset (Fin 4)) :
    pureAllA pi kap lam t1 t2 tx t3 t4 U V
      = ∑ p : Fin 4, ∑ q : Fin 4,
          (pi p * Kmat pi kap lam tx p q)
            * (S pi kap lam U p t1 * S pi kap lam U q t3
               * (S pi kap lam V p t2 * S pi kap lam V q t4)) := by
  have h : pureAllA pi kap lam t1 t2 tx t3 t4 U V
      = ∑ p : Fin 4, ∑ q : Fin 4, ∑ l ∈ V, ∑ k ∈ V, ∑ j ∈ U, ∑ i ∈ U,
          (pi p * Kmat pi kap lam tx p q)
            * ((Kmat pi kap lam t1 p i * Kmat pi kap lam t3 q j)
               * (Kmat pi kap lam t2 p k * Kmat pi kap lam t4 q l)) := by
    simp only [pureAllA, patt4]
    rw [perm_pureAll]
    refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => ?_))
    refine Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun k _ =>
      Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun i _ => ?_))))
    ring
  rw [h]
  refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => ?_))
  simp only [S, Finset.mul_sum, Finset.sum_mul]

/-- ★★ **`monB` 的闭式**（跨结点分组 `{0,3}/{1,2}`）。 -/
theorem monB_closed (pi : Fin 4 → ℝ) (kap lam t1 t2 tx t3 t4 : ℝ) (U V : Finset (Fin 4)) :
    monB pi kap lam t1 t2 tx t3 t4 U V
      = ∑ p : Fin 4, ∑ q : Fin 4,
          (pi p * Kmat pi kap lam tx p q)
            * (D pi kap lam U p q t1 t4 * D pi kap lam V p q t2 t3) := by
  have h : monB pi kap lam t1 t2 tx t3 t4 U V
      = ∑ p : Fin 4, ∑ q : Fin 4, ∑ j ∈ V, ∑ i ∈ U,
          (pi p * Kmat pi kap lam tx p q)
            * ((Kmat pi kap lam t1 p i * Kmat pi kap lam t4 q i)
               * (Kmat pi kap lam t2 p j * Kmat pi kap lam t3 q j)) := by
    simp only [monB, patt4]
    rw [perm_mon]
    refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => ?_))
    refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun i _ => ?_))
    ring
  rw [h]
  refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => ?_))
  simp only [D, Finset.mul_sum, Finset.sum_mul]

/-- ★★ **`pureMonB` 的闭式**。 -/
theorem pureMonB_closed (pi : Fin 4 → ℝ) (kap lam t1 t2 tx t3 t4 : ℝ) (U V : Finset (Fin 4)) :
    pureMonB pi kap lam t1 t2 tx t3 t4 U V
      = ∑ p : Fin 4, ∑ q : Fin 4,
          (pi p * Kmat pi kap lam tx p q)
            * (S pi kap lam U p t1 * S pi kap lam U q t4 * D pi kap lam V p q t2 t3) := by
  have h : pureMonB pi kap lam t1 t2 tx t3 t4 U V
      = ∑ p : Fin 4, ∑ q : Fin 4, ∑ k ∈ V, ∑ j ∈ U, ∑ i ∈ U,
          (pi p * Kmat pi kap lam tx p q)
            * ((Kmat pi kap lam t1 p i * Kmat pi kap lam t4 q j)
               * (Kmat pi kap lam t2 p k * Kmat pi kap lam t3 q k)) := by
    simp only [pureMonB, patt4]
    rw [perm_pureMon]
    refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => ?_))
    refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun j _ =>
      Finset.sum_congr rfl (fun i _ => ?_)))
    ring
  rw [h]
  refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => ?_))
  simp only [S, D, Finset.mul_sum, Finset.sum_mul]

/-- ★★ **`monPureB` 的闭式**。 -/
theorem monPureB_closed (pi : Fin 4 → ℝ) (kap lam t1 t2 tx t3 t4 : ℝ) (U V : Finset (Fin 4)) :
    monPureB pi kap lam t1 t2 tx t3 t4 U V
      = ∑ p : Fin 4, ∑ q : Fin 4,
          (pi p * Kmat pi kap lam tx p q)
            * (D pi kap lam U p q t1 t4 * S pi kap lam V p t2 * S pi kap lam V q t3) := by
  have h : monPureB pi kap lam t1 t2 tx t3 t4 U V
      = ∑ p : Fin 4, ∑ q : Fin 4, ∑ l ∈ V, ∑ k ∈ V, ∑ i ∈ U,
          (pi p * Kmat pi kap lam tx p q)
            * ((Kmat pi kap lam t1 p i * Kmat pi kap lam t4 q i)
               * (Kmat pi kap lam t2 p k * Kmat pi kap lam t3 q l)) := by
    simp only [monPureB, patt4]
    rw [perm_monPure]
    refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => ?_))
    refine Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun k _ =>
      Finset.sum_congr rfl (fun i _ => ?_)))
    ring
  rw [h]
  refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => ?_))
  simp only [S, D, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun k _ =>
    Finset.sum_congr rfl (fun i _ => ?_)))
  ring

/-- ★★ **`pureAllB` 的闭式**。 -/
theorem pureAllB_closed (pi : Fin 4 → ℝ) (kap lam t1 t2 tx t3 t4 : ℝ) (U V : Finset (Fin 4)) :
    pureAllB pi kap lam t1 t2 tx t3 t4 U V
      = ∑ p : Fin 4, ∑ q : Fin 4,
          (pi p * Kmat pi kap lam tx p q)
            * (S pi kap lam U p t1 * S pi kap lam U q t4
               * (S pi kap lam V p t2 * S pi kap lam V q t3)) := by
  have h : pureAllB pi kap lam t1 t2 tx t3 t4 U V
      = ∑ p : Fin 4, ∑ q : Fin 4, ∑ l ∈ V, ∑ k ∈ V, ∑ j ∈ U, ∑ i ∈ U,
          (pi p * Kmat pi kap lam tx p q)
            * ((Kmat pi kap lam t1 p i * Kmat pi kap lam t4 q j)
               * (Kmat pi kap lam t2 p k * Kmat pi kap lam t3 q l)) := by
    simp only [pureAllB, patt4]
    rw [perm_pureAll]
    refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => ?_))
    refine Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun k _ =>
      Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun i _ => ?_))))
    ring
  rw [h]
  refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => ?_))
  simp only [S, Finset.mul_sum, Finset.sum_mul]

/-! ## §5 三条主恒等式

🔻 **本批未完成**（不给 `sorry` 占位）：`Ew_diag` / `EwA_zero` / `EwB_zero` 的**最终求值**
（把 §4 的 8 个二重和收成数）。规格与已验证的路线见 `CASTER_F84_PROPASPEC.md` §3.1(c) 与
给协调侧的交接说明；本文件已把所需的**全部前置件**（§2 重排、§3 脚手架、§4 12 条闭式）交付完毕。

⚠️ 实测教训：**不要**把 §4 的 8 条闭式代入后一次性 `simp [Kmat,Bmat,…] <;> field_simp <;> ring`
（16×8 项、每项 4 个 `S`/`D` 因子展开后 ≈10⁴–10⁵ 单项式，实测被 OOM 杀死，退出码 137）。
正确路线见文件末注释。 -/

end Phylo.Stat.CASTERF84Scaffold

end
