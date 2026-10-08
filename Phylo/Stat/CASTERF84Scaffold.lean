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

/-! ## §5 三条主恒等式（本条注释是**实现路线**的总览）

三条目标（`lam` 自由、只需 `piR pi ≠ 0`、`piY pi ≠ 0`）：

* ★★★ `Ew_diag`：`Ew = 2·π0π2π1π3·piR·piY·(1 − sm lx)·rm t1·rm t2·rm t3·rm t4`；
* ★★★ `EwA_zero`、`EwB_zero`：两个跨结点分组恒为 `0`。

**（对角）路线**：`Ew_factor`（把 §4 的 8 个二重和合并成 `Ffac` 的一个二重和）
→ `Ew_diag_sum`（按 `Rset ∪ Yset` 分四块：同类块由 `g` 的类外归零为 0，
跨类块由 `Kmat_cross_*` 与 `Finset.sum_mul_sum` 化归类求和，再用 `sum_pi_g*`）
→ `Ew_diag`（`ring`）。

**（跨结点）路线**：`EwA_factor`/`EwB_factor` → `EwA_sum`/`EwB_sum`
（同类块由 `GA_zero_of_not_mem` 为 0；跨类块由混合闭式 `GA_mixed_*` 提出
`(p_cπ_p − q_c)`，再用 `sum_pi_mixed_*` 相消）→ `EwA_zero`/`EwB_zero`。

⚠️ **实测教训**（别再踩）：把 §4 的 8 条闭式代入后**一次性**
`simp [Kmat,Bmat,…] <;> field_simp <;> ring` 会得到 16×8 项、每项 4 个 `S`/`D` 因子
（≈10⁴–10⁵ 单项式），实测被 OOM 杀死（退出码 137）。**必须先合并成单个二重和、再逐项 `ring`。** -/

/-! ### §5.1 对角分组：逐项因子 `gR`/`gY` 与类求和 -/

/-- 对角 `R` 侧因子 `g_R(p) = piR²·D_R(p,p;t1,t2) − sqR·S_R(p,t1)·S_R(p,t2)`。 -/
def gR (pi : Fin 4 → ℝ) (kap lam t1 t2 : ℝ) (p : Fin 4) : ℝ :=
  piR pi ^ 2 * D pi kap lam Rset p p t1 t2
    - sqR pi * S pi kap lam Rset p t1 * S pi kap lam Rset p t2

/-- 对角 `Y` 侧因子 `g_Y(q)`。 -/
def gY (pi : Fin 4 → ℝ) (kap lam t3 t4 : ℝ) (q : Fin 4) : ℝ :=
  piY pi ^ 2 * D pi kap lam Yset q q t3 t4
    - sqY pi * S pi kap lam Yset q t3 * S pi kap lam Yset q t4

/-- 类 `Y` 的因子，长度取 `(t1,t2)`（即 `(Y,R)` 组里挂在 `p` 上的那一侧）。 -/
def gY12 (pi : Fin 4 → ℝ) (kap lam t1 t2 : ℝ) (p : Fin 4) : ℝ :=
  piY pi ^ 2 * D pi kap lam Yset p p t1 t2
    - sqY pi * S pi kap lam Yset p t1 * S pi kap lam Yset p t2

/-- 类 `R` 的因子，长度取 `(t3,t4)`（即 `(Y,R)` 组里挂在 `q` 上的那一侧）。 -/
def gR34 (pi : Fin 4 → ℝ) (kap lam t3 t4 : ℝ) (q : Fin 4) : ℝ :=
  piR pi ^ 2 * D pi kap lam Rset q q t3 t4
    - sqR pi * S pi kap lam Rset q t3 * S pi kap lam Rset q t4

/-- 对角分组下逐 `(p,q)` 的被加项。

⚠️ 第二项的**长度归属**必须是 `gY12 p * gR34 q`（`(Y,R)` 组的两个因子）：
`(0)` 是**逐 `(p,q)`** 恒等式（证明靠 `Finset.sum_congr` + `ring`），
而 `gY q * gR p` 那种写法只在**求和之后**才相等（要用细致平衡换名），逐项并不相等。 -/
def Ffac (pi : Fin 4 → ℝ) (kap lam t1 t2 lx t3 t4 : ℝ) (p q : Fin 4) : ℝ :=
  pi p * Kmat pi kap lam lx p q
    * (gR pi kap lam t1 t2 p * gY pi kap lam t3 t4 q
        + gY12 pi kap lam t1 t2 p * gR34 pi kap lam t3 t4 q)

/-- `Fin 4` 上的求和按 `Rset ∪ Yset` 拆分。 -/
theorem sum_univ_split (f : Fin 4 → ℝ) :
    (∑ p : Fin 4, f p) = ∑ p ∈ Rset, f p + ∑ p ∈ Yset, f p := by
  have hU : (Finset.univ : Finset (Fin 4)) = Rset ∪ Yset := by
    ext x; fin_cases x <;> simp [Rset, Yset]
  have hd : Disjoint Rset Yset := by
    rw [Finset.disjoint_iff_ne]; intro a ha b hb
    fin_cases a <;> fin_cases b <;> simp_all [Rset, Yset]
  rw [hU, Finset.sum_union hd]

/-- ★ **(B) 左**：`p ∉ Rset ⟹ g_R(p) = 0`。 -/
theorem gR_eq_zero_of_not_mem (pi : Fin 4 → ℝ) (kap lam t1 t2 : ℝ)
    (_hR : piR pi ≠ 0) (_hY : piY pi ≠ 0) {p : Fin 4} (hp : p ∉ Rset) :
    gR pi kap lam t1 t2 p = 0 := by
  fin_cases p <;>
    simp_all [Rset, gR, S, D, Kmat, P0, P1, P2, Bmat, piR, piY, sqR,
      Finset.sum_insert, Finset.sum_singleton,
      Finset.mem_insert, Finset.mem_singleton, reduceIte] <;>
    field_simp <;> ring

/-- ★ **(B) 右**：`q ∉ Yset ⟹ g_Y(q) = 0`。 -/
theorem gY_eq_zero_of_not_mem (pi : Fin 4 → ℝ) (kap lam t3 t4 : ℝ)
    (_hR : piR pi ≠ 0) (_hY : piY pi ≠ 0) {q : Fin 4} (hq : q ∉ Yset) :
    gY pi kap lam t3 t4 q = 0 := by
  fin_cases q <;>
    simp_all [Yset, gY, S, D, Kmat, P0, P1, P2, Bmat, piR, piY, sqY,
      Finset.sum_insert, Finset.sum_singleton,
      Finset.mem_insert, Finset.mem_singleton, reduceIte] <;>
    field_simp <;> ring

/-- ★ **(B) `Y₁₂`**：`p ∉ Yset ⟹ gY12(p) = 0`。 -/
theorem gY12_eq_zero_of_not_mem (pi : Fin 4 → ℝ) (kap lam t1 t2 : ℝ)
    (_hR : piR pi ≠ 0) (_hY : piY pi ≠ 0) {p : Fin 4} (hp : p ∉ Yset) :
    gY12 pi kap lam t1 t2 p = 0 := by
  fin_cases p <;>
    simp_all [Yset, gY12, S, D, Kmat, P0, P1, P2, Bmat, piR, piY, sqY,
      Finset.sum_insert, Finset.sum_singleton,
      Finset.mem_insert, Finset.mem_singleton, reduceIte] <;>
    field_simp <;> ring

/-- ★ **(B) `R₃₄`**：`q ∉ Rset ⟹ gR34(q) = 0`。 -/
theorem gR34_eq_zero_of_not_mem (pi : Fin 4 → ℝ) (kap lam t3 t4 : ℝ)
    (_hR : piR pi ≠ 0) (_hY : piY pi ≠ 0) {q : Fin 4} (hq : q ∉ Rset) :
    gR34 pi kap lam t3 t4 q = 0 := by
  fin_cases q <;>
    simp_all [Rset, gR34, S, D, Kmat, P0, P1, P2, Bmat, piR, piY, sqR,
      Finset.sum_insert, Finset.sum_singleton,
      Finset.mem_insert, Finset.mem_singleton, reduceIte] <;>
    field_simp <;> ring

/-- ★ **(C) 左**：`∑_{p∈Rset} π_p·g_R(p) = piR·(piR² − sqR)·rm t1·rm t2`。 -/
theorem sum_pi_gR (pi : Fin 4 → ℝ) (kap lam t1 t2 : ℝ)
    (hR : piR pi ≠ 0) (_hY : piY pi ≠ 0) :
    ∑ p ∈ Rset, pi p * gR pi kap lam t1 t2 p
      = piR pi * (piR pi ^ 2 - sqR pi) * (rm lam kap t1 * rm lam kap t2) := by
  simp only [piR] at hR
  rw [show (∑ p ∈ Rset, pi p * gR pi kap lam t1 t2 p)
      = pi 0 * gR pi kap lam t1 t2 0 + pi 1 * gR pi kap lam t1 t2 1 from by simp [Rset]]
  simp [gR, S, D, Rset, Kmat, P0, P1, P2, Bmat, piR, piY, sqR,
    Finset.sum_insert, Finset.sum_singleton,
    Finset.mem_singleton, reduceIte]
  field_simp
  ring

/-- ★ **(C) 右**：`∑_{q∈Yset} π_q·g_Y(q) = piY·(piY² − sqY)·rm t3·rm t4`。 -/
theorem sum_pi_gY (pi : Fin 4 → ℝ) (kap lam t3 t4 : ℝ)
    (_hR : piR pi ≠ 0) (hY : piY pi ≠ 0) :
    ∑ q ∈ Yset, pi q * gY pi kap lam t3 t4 q
      = piY pi * (piY pi ^ 2 - sqY pi) * (rm lam kap t3 * rm lam kap t4) := by
  simp only [piY] at hY
  rw [show (∑ q ∈ Yset, pi q * gY pi kap lam t3 t4 q)
      = pi 2 * gY pi kap lam t3 t4 2 + pi 3 * gY pi kap lam t3 t4 3 from by simp [Yset]]
  simp [gY, S, D, Yset, Kmat, P0, P1, P2, Bmat, piR, piY, sqY,
    Finset.sum_insert, Finset.sum_singleton,
    Finset.mem_singleton, reduceIte]
  field_simp
  ring

/-- ★ **(C) `Y₁₂`**：`∑_{p∈Yset} π_p·gY12(p) = piY·(piY² − sqY)·rm t1·rm t2`。 -/
theorem sum_pi_gY12 (pi : Fin 4 → ℝ) (kap lam t1 t2 : ℝ)
    (_hR : piR pi ≠ 0) (hY : piY pi ≠ 0) :
    ∑ p ∈ Yset, pi p * gY12 pi kap lam t1 t2 p
      = piY pi * (piY pi ^ 2 - sqY pi) * (rm lam kap t1 * rm lam kap t2) := by
  simp only [piY] at hY
  rw [show (∑ p ∈ Yset, pi p * gY12 pi kap lam t1 t2 p)
      = pi 2 * gY12 pi kap lam t1 t2 2 + pi 3 * gY12 pi kap lam t1 t2 3 from by simp [Yset]]
  simp [gY12, S, D, Yset, Kmat, P0, P1, P2, Bmat, piR, piY, sqY,
    Finset.sum_insert, Finset.sum_singleton,
    Finset.mem_singleton, reduceIte]
  field_simp
  ring

/-- ★ **(C) `R₃₄`**：`∑_{q∈Rset} π_q·gR34(q) = piR·(piR² − sqR)·rm t3·rm t4`。 -/
theorem sum_pi_gR34 (pi : Fin 4 → ℝ) (kap lam t3 t4 : ℝ)
    (hR : piR pi ≠ 0) (_hY : piY pi ≠ 0) :
    ∑ q ∈ Rset, pi q * gR34 pi kap lam t3 t4 q
      = piR pi * (piR pi ^ 2 - sqR pi) * (rm lam kap t3 * rm lam kap t4) := by
  simp only [piR] at hR
  rw [show (∑ q ∈ Rset, pi q * gR34 pi kap lam t3 t4 q)
      = pi 0 * gR34 pi kap lam t3 t4 0 + pi 1 * gR34 pi kap lam t3 t4 1 from by simp [Rset]]
  simp [gR34, S, D, Rset, Kmat, P0, P1, P2, Bmat, piR, piY, sqR,
    Finset.sum_insert, Finset.sum_singleton,
    Finset.mem_singleton, reduceIte]
  field_simp
  ring

/-- ★ **(D) 跨类核元（`R → Y`）**：`p ∈ Rset`、`q ∈ Yset` ⟹ `Kx_{pq} = π_q(1 − sm lx)`。 -/
theorem Kmat_cross_RY (pi : Fin 4 → ℝ) (kap lam t : ℝ) {p q : Fin 4}
    (hp : p ∈ Rset) (hq : q ∈ Yset) : Kmat pi kap lam t p q = pi q * (1 - sm lam t) := by
  fin_cases p <;> fin_cases q <;>
    simp_all [Rset, Yset, Kmat, P0, P1, P2, Bmat] <;> ring

/-- ★ **(D) 跨类核元（`Y → R`）**。 -/
theorem Kmat_cross_YR (pi : Fin 4 → ℝ) (kap lam t : ℝ) {p q : Fin 4}
    (hp : p ∈ Yset) (hq : q ∈ Rset) : Kmat pi kap lam t p q = pi q * (1 - sm lam t) := by
  fin_cases p <;> fin_cases q <;>
    simp_all [Rset, Yset, Kmat, P0, P1, P2, Bmat] <;> ring

/-- ★★ **(0) 对角分组：把 `Ew` 的 8 个二重和合并成 `Ffac` 的**一个**二重和**。
（先合并、再在绑定变量下 `ring`；**不要**把 8 条闭式代进去后直接 `ring`——那是 OOM 的写法。） -/
theorem Ew_factor (pi : Fin 4 → ℝ) (kap lam t1 t2 lx t3 t4 : ℝ) :
    Ew pi kap lam t1 t2 lx t3 t4
      = (∑ p : Fin 4, ∑ q : Fin 4, Ffac pi kap lam t1 t2 lx t3 t4 p q) / 4 := by
  rw [Ew]
  congr 1
  simp only [mon_closed, pureMon_closed, monPure_closed, pureAll_closed]
  simp only [Finset.mul_sum, mul_add, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => ?_))
  simp only [Ffac, gR, gY, gY12, gR34]
  ring

/-- `q ∈ Rset ⟹ q ∉ Yset`（两个类集合都是字面量）。 -/
theorem not_mem_Yset_of_mem_Rset {q : Fin 4} (h : q ∈ Rset) : q ∉ Yset := by
  fin_cases q <;> simp_all [Rset, Yset]

/-- `p ∈ Yset ⟹ p ∉ Rset`。 -/
theorem not_mem_Rset_of_mem_Yset {p : Fin 4} (h : p ∈ Yset) : p ∉ Rset := by
  fin_cases p <;> simp_all [Rset, Yset]

/-- ★★★ **对角分组的求值**：把 `Ffac` 的二重和收成数。

四块（`R×R`、`Y×Y` 由 `g` 的类外归零逐项杀；`R×Y`、`Y×R` 由跨类核元闭式 + 类求和给出，
两块相等）⇒ `2(1 − sm lx)·piR·piY·(piR² − sqR)·(piY² − sqY)·rm t1·rm t2·rm t3·rm t4`。 -/
theorem Ew_diag_sum (pi : Fin 4 → ℝ) (hR : piR pi ≠ 0) (hY : piY pi ≠ 0)
    (kap lam t1 t2 lx t3 t4 : ℝ) :
    (∑ p : Fin 4, ∑ q : Fin 4, Ffac pi kap lam t1 t2 lx t3 t4 p q)
      = 2 * (1 - sm lam lx) * piR pi * piY pi * (piR pi ^ 2 - sqR pi) * (piY pi ^ 2 - sqY pi)
        * (rm lam kap t1 * rm lam kap t2 * rm lam kap t3 * rm lam kap t4) := by
  have hRR : (∑ p ∈ Rset, ∑ q ∈ Rset, Ffac pi kap lam t1 t2 lx t3 t4 p q) = 0 := by
    refine Finset.sum_eq_zero (fun p hp => Finset.sum_eq_zero (fun q hq => ?_))
    rw [Ffac, gY_eq_zero_of_not_mem pi kap lam t3 t4 hR hY (not_mem_Yset_of_mem_Rset hq),
      gY12_eq_zero_of_not_mem pi kap lam t1 t2 hR hY (not_mem_Yset_of_mem_Rset hp)]
    ring
  have hYY : (∑ p ∈ Yset, ∑ q ∈ Yset, Ffac pi kap lam t1 t2 lx t3 t4 p q) = 0 := by
    refine Finset.sum_eq_zero (fun p hp => Finset.sum_eq_zero (fun q hq => ?_))
    rw [Ffac, gR_eq_zero_of_not_mem pi kap lam t1 t2 hR hY (not_mem_Rset_of_mem_Yset hp),
      gR34_eq_zero_of_not_mem pi kap lam t3 t4 hR hY (not_mem_Rset_of_mem_Yset hq)]
    ring
  have hRY : (∑ p ∈ Rset, ∑ q ∈ Yset, Ffac pi kap lam t1 t2 lx t3 t4 p q)
      = (1 - sm lam lx) * (∑ p ∈ Rset, pi p * gR pi kap lam t1 t2 p)
        * (∑ q ∈ Yset, pi q * gY pi kap lam t3 t4 q) := by
    rw [show (∑ p ∈ Rset, ∑ q ∈ Yset, Ffac pi kap lam t1 t2 lx t3 t4 p q)
        = ∑ p ∈ Rset, ∑ q ∈ Yset,
            ((1 - sm lam lx) * (pi p * gR pi kap lam t1 t2 p))
              * (pi q * gY pi kap lam t3 t4 q) from by
      refine Finset.sum_congr rfl (fun p hp => Finset.sum_congr rfl (fun q hq => ?_))
      rw [Ffac, Kmat_cross_RY pi kap lam lx hp hq,
        gY12_eq_zero_of_not_mem pi kap lam t1 t2 hR hY (not_mem_Yset_of_mem_Rset hp)]
      ring]
    rw [← Finset.sum_mul_sum, ← Finset.mul_sum]
  have hYR : (∑ p ∈ Yset, ∑ q ∈ Rset, Ffac pi kap lam t1 t2 lx t3 t4 p q)
      = (1 - sm lam lx) * (∑ p ∈ Yset, pi p * gY12 pi kap lam t1 t2 p)
        * (∑ q ∈ Rset, pi q * gR34 pi kap lam t3 t4 q) := by
    rw [show (∑ p ∈ Yset, ∑ q ∈ Rset, Ffac pi kap lam t1 t2 lx t3 t4 p q)
        = ∑ p ∈ Yset, ∑ q ∈ Rset,
            ((1 - sm lam lx) * (pi p * gY12 pi kap lam t1 t2 p))
              * (pi q * gR34 pi kap lam t3 t4 q) from by
      refine Finset.sum_congr rfl (fun p hp => Finset.sum_congr rfl (fun q hq => ?_))
      rw [Ffac, Kmat_cross_YR pi kap lam lx hp hq,
        gR_eq_zero_of_not_mem pi kap lam t1 t2 hR hY (not_mem_Rset_of_mem_Yset hp)]
      ring]
    rw [← Finset.sum_mul_sum, ← Finset.mul_sum]
  simp only [sum_univ_split, Finset.sum_add_distrib]
  rw [hRR, hYY, hRY, hYR,
    sum_pi_gR pi kap lam t1 t2 hR hY, sum_pi_gY pi kap lam t3 t4 hR hY,
    sum_pi_gY12 pi kap lam t1 t2 hR hY, sum_pi_gR34 pi kap lam t3 t4 hR hY]
  ring

/-- ★★★ **(D) 对角分组的期望权重**（附录 1585 的常数）：
`Ew = 2·π_Aπ_Cπ_Gπ_T·π_Rπ_Y·(1 − sm lx)·rm t1·rm t2·rm t3·rm t4`。 -/
theorem Ew_diag (pi : Fin 4 → ℝ) (hR : piR pi ≠ 0) (hY : piY pi ≠ 0)
    (kap lam t1 t2 lx t3 t4 : ℝ) :
    Ew pi kap lam t1 t2 lx t3 t4
      = 2 * pi 0 * pi 2 * pi 1 * pi 3 * piR pi * piY pi * (1 - sm lam lx)
        * (rm lam kap t1 * rm lam kap t2 * rm lam kap t3 * rm lam kap t4) := by
  rw [Ew_factor, Ew_diag_sum pi hR hY kap lam t1 t2 lx t3 t4]
  simp only [piR, piY, sqR, sqY]
  ring

/-! ## §6 跨结点分组：`EwA = EwB = 0`

把 §4 的 `A`/`B` 族闭式按 `(C₁,C₂)` 的系数组合（与 §5 同样的合并手法），得到
`4·EwA = ΣpΣq π_pKx_{pq}·(G_R(p,q;t1,t3)·G_Y(p,q;t2,t4) + G_Y(p,q;t1,t3)·G_R(p,q;t2,t4))`
（`G_c(p,q;s,t) := p_c²D_c(p,q;s,t) − q_c·S_c(p,s)·S_c(q,t)`），`EwB` 把长度对换成 `(t1,t4)`/`(t2,t3)`。
按 `Rset ∪ Yset` 分四块：`R×R`、`Y×Y` 由 `G_c` 的类外归零恒等为 0；
`R×Y`、`Y×R` 由混合闭式提出 `(p_cπ_p − q_c)`，再用 `Σ_{p∈c}π_p(p_cπ_p − q_c) = 0` 相消。 -/

/-- 跨结点组合 `G_c(p,q;s,t) = p_c²·D_c(p,q;s,t) − q_c·S_c(p,s)·S_c(q,t)`。 -/
def GA (pi : Fin 4 → ℝ) (kap lam : ℝ) (c : Finset (Fin 4)) (p q : Fin 4) (s t : ℝ) : ℝ :=
  pU pi c ^ 2 * D pi kap lam c p q s t - qU pi c * S pi kap lam c p s * S pi kap lam c q t

/-- ★ **(ii)**：`p ∉ c` 且 `q ∉ c` ⟹ `G_c(p,q;s,t) = 0`。 -/
theorem GA_zero_of_not_mem (pi : Fin 4 → ℝ) (kap lam : ℝ) {c : Finset (Fin 4)}
    (hc : c = Rset ∨ c = Yset) {p q : Fin 4} (hp : p ∉ c) (hq : q ∉ c) (s t : ℝ) :
    GA pi kap lam c p q s t = 0 := by
  rcases hc with rfl | rfl
  · fin_cases p <;> fin_cases q <;>
      simp_all [Rset, GA, S, D, pU, qU, Kmat, P0, P1, P2, Bmat, piR, piY,
        Finset.sum_insert, Finset.sum_singleton, Finset.mem_insert, Finset.mem_singleton,
        reduceIte] <;> field_simp <;> ring
  · fin_cases p <;> fin_cases q <;>
      simp_all [Yset, GA, S, D, pU, qU, Kmat, P0, P1, P2, Bmat, piR, piY,
        Finset.sum_insert, Finset.sum_singleton, Finset.mem_insert, Finset.mem_singleton,
        reduceIte] <;> field_simp <;> ring

/-- ★ **(iii) 左混合**：`p ∈ c`、`q ∉ c` ⟹ `G_c(p,q;s,t) = p_c(1 − sm t)·rm s·(p_cπ_p − q_c)`。 -/
theorem GA_mixed_left (pi : Fin 4 → ℝ) (kap lam : ℝ) {c : Finset (Fin 4)}
    (hc : c = Rset ∨ c = Yset) (hR : piR pi ≠ 0) (hY : piY pi ≠ 0)
    {p q : Fin 4} (hp : p ∈ c) (hq : q ∉ c) (s t : ℝ) :
    GA pi kap lam c p q s t
      = pU pi c * (1 - sm lam t) * rm lam kap s * (pU pi c * pi p - qU pi c) := by
  rcases hc with rfl | rfl
  · fin_cases p <;> fin_cases q <;>
      simp_all [Rset, GA, S, D, pU, qU, Kmat, P0, P1, P2, Bmat, piR, piY,
        Finset.sum_insert, Finset.sum_singleton, Finset.mem_insert, Finset.mem_singleton,
        reduceIte] <;> field_simp <;> ring
  · fin_cases p <;> fin_cases q <;>
      simp_all [Yset, GA, S, D, pU, qU, Kmat, P0, P1, P2, Bmat, piR, piY,
        Finset.sum_insert, Finset.sum_singleton, Finset.mem_insert, Finset.mem_singleton,
        reduceIte] <;> field_simp <;> ring

/-- ★ **(iii) 右混合**：`p ∉ c`、`q ∈ c` ⟹ `G_c(p,q;s,t) = p_c(1 − sm s)·rm t·(p_cπ_q − q_c)`。 -/
theorem GA_mixed_right (pi : Fin 4 → ℝ) (kap lam : ℝ) {c : Finset (Fin 4)}
    (hc : c = Rset ∨ c = Yset) (hR : piR pi ≠ 0) (hY : piY pi ≠ 0)
    {p q : Fin 4} (hp : p ∉ c) (hq : q ∈ c) (s t : ℝ) :
    GA pi kap lam c p q s t
      = pU pi c * (1 - sm lam s) * rm lam kap t * (pU pi c * pi q - qU pi c) := by
  rcases hc with rfl | rfl
  · fin_cases p <;> fin_cases q <;>
      simp_all [Rset, GA, S, D, pU, qU, Kmat, P0, P1, P2, Bmat, piR, piY,
        Finset.sum_insert, Finset.sum_singleton, Finset.mem_insert, Finset.mem_singleton,
        reduceIte] <;> field_simp <;> ring
  · fin_cases p <;> fin_cases q <;>
      simp_all [Yset, GA, S, D, pU, qU, Kmat, P0, P1, P2, Bmat, piR, piY,
        Finset.sum_insert, Finset.sum_singleton, Finset.mem_insert, Finset.mem_singleton,
        reduceIte] <;> field_simp <;> ring

/-- ★ **(iv) `R` 侧**：`∑_{p∈Rset} π_p·(p_Rπ_p − q_R) = 0`。 -/
theorem sum_pi_mixed_Rset (pi : Fin 4 → ℝ) :
    ∑ p ∈ Rset, pi p * (pU pi Rset * pi p - qU pi Rset) = 0 := by
  simp [Rset, pU, qU]
  ring

/-- ★ **(iv) `Y` 侧**：`∑_{q∈Yset} π_q·(p_Yπ_q − q_Y) = 0`。 -/
theorem sum_pi_mixed_Yset (pi : Fin 4 → ℝ) :
    ∑ q ∈ Yset, pi q * (pU pi Yset * pi q - qU pi Yset) = 0 := by
  simp [Yset, pU, qU]
  ring

/-- 跨类块 `R×Y` 的通用归零（提出常数 `KK` 后由 (iv) 两侧相消）。 -/
theorem block_zero_RY (pi : Fin 4 → ℝ) (KK : ℝ) :
    (∑ p ∈ Rset, ∑ q ∈ Yset, (KK * (pi p * (pU pi Rset * pi p - qU pi Rset)))
        * (pi q * (pU pi Yset * pi q - qU pi Yset))) = 0 := by
  rw [← Finset.sum_mul_sum, ← Finset.mul_sum, sum_pi_mixed_Rset]
  ring

/-- 跨类块 `Y×R` 的通用归零。 -/
theorem block_zero_YR (pi : Fin 4 → ℝ) (KK : ℝ) :
    (∑ p ∈ Yset, ∑ q ∈ Rset, (KK * (pi p * (pU pi Yset * pi p - qU pi Yset)))
        * (pi q * (pU pi Rset * pi q - qU pi Rset))) = 0 := by
  rw [← Finset.sum_mul_sum, ← Finset.mul_sum, sum_pi_mixed_Yset]
  ring

/-- `EwA` 的逐 `(p,q)` 被加项。 -/
def FfacA (pi : Fin 4 → ℝ) (kap lam t1 t2 lx t3 t4 : ℝ) (p q : Fin 4) : ℝ :=
  pi p * Kmat pi kap lam lx p q
    * (GA pi kap lam Rset p q t1 t3 * GA pi kap lam Yset p q t2 t4
        + GA pi kap lam Yset p q t1 t3 * GA pi kap lam Rset p q t2 t4)

/-- ★★ **(0A)**：把 `EwA` 的 8 个二重和合并成 `FfacA` 的**一个**二重和。 -/
theorem EwA_factor (pi : Fin 4 → ℝ) (kap lam t1 t2 lx t3 t4 : ℝ) :
    EwA pi kap lam t1 t2 lx t3 t4
      = (∑ p : Fin 4, ∑ q : Fin 4, FfacA pi kap lam t1 t2 lx t3 t4 p q) / 4 := by
  rw [EwA]
  congr 1
  simp only [monA_closed, pureMonA_closed, monPureA_closed, pureAllA_closed]
  simp only [Finset.mul_sum, mul_add, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => ?_))
  simp only [FfacA, GA, pU_Rset pi, pU_Yset pi, qU_Rset pi, qU_Yset pi]
  ring

/-- ★★★ **(XA)**：`EwA` 的二重和为 0（四块皆 0）。 -/
theorem EwA_sum (pi : Fin 4 → ℝ) (hR : piR pi ≠ 0) (hY : piY pi ≠ 0)
    (kap lam t1 t2 lx t3 t4 : ℝ) :
    (∑ p : Fin 4, ∑ q : Fin 4, FfacA pi kap lam t1 t2 lx t3 t4 p q) = 0 := by
  have hRR : (∑ p ∈ Rset, ∑ q ∈ Rset, FfacA pi kap lam t1 t2 lx t3 t4 p q) = 0 := by
    refine Finset.sum_eq_zero (fun p hp => Finset.sum_eq_zero (fun q hq => ?_))
    rw [FfacA,
      GA_zero_of_not_mem pi kap lam (Or.inr rfl)
        (not_mem_Yset_of_mem_Rset hp) (not_mem_Yset_of_mem_Rset hq) t2 t4,
      GA_zero_of_not_mem pi kap lam (Or.inr rfl)
        (not_mem_Yset_of_mem_Rset hp) (not_mem_Yset_of_mem_Rset hq) t1 t3]
    ring
  have hYY : (∑ p ∈ Yset, ∑ q ∈ Yset, FfacA pi kap lam t1 t2 lx t3 t4 p q) = 0 := by
    refine Finset.sum_eq_zero (fun p hp => Finset.sum_eq_zero (fun q hq => ?_))
    rw [FfacA,
      GA_zero_of_not_mem pi kap lam (Or.inl rfl)
        (not_mem_Rset_of_mem_Yset hp) (not_mem_Rset_of_mem_Yset hq) t1 t3,
      GA_zero_of_not_mem pi kap lam (Or.inl rfl)
        (not_mem_Rset_of_mem_Yset hp) (not_mem_Rset_of_mem_Yset hq) t2 t4]
    ring
  have hRY : (∑ p ∈ Rset, ∑ q ∈ Yset, FfacA pi kap lam t1 t2 lx t3 t4 p q) = 0 := by
    rw [show (∑ p ∈ Rset, ∑ q ∈ Yset, FfacA pi kap lam t1 t2 lx t3 t4 p q)
        = ∑ p ∈ Rset, ∑ q ∈ Yset,
            (((1 - sm lam lx) * pU pi Rset * pU pi Yset
                * ((1 - sm lam t3) * (1 - sm lam t2) * (rm lam kap t1 * rm lam kap t4)
                   + (1 - sm lam t1) * (1 - sm lam t4)
                     * (rm lam kap t3 * rm lam kap t2)))
              * (pi p * (pU pi Rset * pi p - qU pi Rset)))
              * (pi q * (pU pi Yset * pi q - qU pi Yset)) from by
      refine Finset.sum_congr rfl (fun p hp => Finset.sum_congr rfl (fun q hq => ?_))
      rw [FfacA, Kmat_cross_RY pi kap lam lx hp hq,
        GA_mixed_left pi kap lam (Or.inl rfl) hR hY hp (not_mem_Rset_of_mem_Yset hq) t1 t3,
        GA_mixed_right pi kap lam (Or.inr rfl) hR hY (not_mem_Yset_of_mem_Rset hp) hq t2 t4,
        GA_mixed_right pi kap lam (Or.inr rfl) hR hY (not_mem_Yset_of_mem_Rset hp) hq t1 t3,
        GA_mixed_left pi kap lam (Or.inl rfl) hR hY hp (not_mem_Rset_of_mem_Yset hq) t2 t4]
      ring]
    exact block_zero_RY pi _
  have hYR : (∑ p ∈ Yset, ∑ q ∈ Rset, FfacA pi kap lam t1 t2 lx t3 t4 p q) = 0 := by
    rw [show (∑ p ∈ Yset, ∑ q ∈ Rset, FfacA pi kap lam t1 t2 lx t3 t4 p q)
        = ∑ p ∈ Yset, ∑ q ∈ Rset,
            (((1 - sm lam lx) * pU pi Rset * pU pi Yset
                * ((1 - sm lam t3) * (1 - sm lam t2) * (rm lam kap t1 * rm lam kap t4)
                   + (1 - sm lam t1) * (1 - sm lam t4)
                     * (rm lam kap t3 * rm lam kap t2)))
              * (pi p * (pU pi Yset * pi p - qU pi Yset)))
              * (pi q * (pU pi Rset * pi q - qU pi Rset)) from by
      refine Finset.sum_congr rfl (fun p hp => Finset.sum_congr rfl (fun q hq => ?_))
      rw [FfacA, Kmat_cross_YR pi kap lam lx hp hq,
        GA_mixed_right pi kap lam (Or.inl rfl) hR hY (not_mem_Rset_of_mem_Yset hp) hq t1 t3,
        GA_mixed_left pi kap lam (Or.inr rfl) hR hY hp (not_mem_Yset_of_mem_Rset hq) t2 t4,
        GA_mixed_left pi kap lam (Or.inr rfl) hR hY hp (not_mem_Yset_of_mem_Rset hq) t1 t3,
        GA_mixed_right pi kap lam (Or.inl rfl) hR hY (not_mem_Rset_of_mem_Yset hp) hq t2 t4]
      ring]
    exact block_zero_YR pi _
  simp only [sum_univ_split, Finset.sum_add_distrib]
  rw [hRR, hYY, hRY, hYR]
  ring

/-- ★★★ **(XA)** 跨结点分组 `{0,2}/{1,3}`（拓扑 `ac|bd`）的期望权重恰为 0。 -/
theorem EwA_zero (pi : Fin 4 → ℝ) (hR : piR pi ≠ 0) (hY : piY pi ≠ 0)
    (kap lam t1 t2 lx t3 t4 : ℝ) : EwA pi kap lam t1 t2 lx t3 t4 = 0 := by
  rw [EwA_factor, EwA_sum pi hR hY kap lam t1 t2 lx t3 t4]
  ring

/-- `EwB` 的逐 `(p,q)` 被加项（长度对为 `(t1,t4)`、`(t2,t3)`）。 -/
def FfacB (pi : Fin 4 → ℝ) (kap lam t1 t2 lx t3 t4 : ℝ) (p q : Fin 4) : ℝ :=
  pi p * Kmat pi kap lam lx p q
    * (GA pi kap lam Rset p q t1 t4 * GA pi kap lam Yset p q t2 t3
        + GA pi kap lam Yset p q t1 t4 * GA pi kap lam Rset p q t2 t3)

/-- ★★ **(0B)**：把 `EwB` 的 8 个二重和合并成 `FfacB` 的**一个**二重和。 -/
theorem EwB_factor (pi : Fin 4 → ℝ) (kap lam t1 t2 lx t3 t4 : ℝ) :
    EwB pi kap lam t1 t2 lx t3 t4
      = (∑ p : Fin 4, ∑ q : Fin 4, FfacB pi kap lam t1 t2 lx t3 t4 p q) / 4 := by
  rw [EwB]
  congr 1
  simp only [monB_closed, pureMonB_closed, monPureB_closed, pureAllB_closed]
  simp only [Finset.mul_sum, mul_add, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => ?_))
  simp only [FfacB, GA, pU_Rset pi, pU_Yset pi, qU_Rset pi, qU_Yset pi]
  ring

/-- ★★★ **(XB)**：`EwB` 的二重和为 0（四块皆 0）。 -/
theorem EwB_sum (pi : Fin 4 → ℝ) (hR : piR pi ≠ 0) (hY : piY pi ≠ 0)
    (kap lam t1 t2 lx t3 t4 : ℝ) :
    (∑ p : Fin 4, ∑ q : Fin 4, FfacB pi kap lam t1 t2 lx t3 t4 p q) = 0 := by
  have hRR : (∑ p ∈ Rset, ∑ q ∈ Rset, FfacB pi kap lam t1 t2 lx t3 t4 p q) = 0 := by
    refine Finset.sum_eq_zero (fun p hp => Finset.sum_eq_zero (fun q hq => ?_))
    rw [FfacB,
      GA_zero_of_not_mem pi kap lam (Or.inr rfl)
        (not_mem_Yset_of_mem_Rset hp) (not_mem_Yset_of_mem_Rset hq) t2 t3,
      GA_zero_of_not_mem pi kap lam (Or.inr rfl)
        (not_mem_Yset_of_mem_Rset hp) (not_mem_Yset_of_mem_Rset hq) t1 t4]
    ring
  have hYY : (∑ p ∈ Yset, ∑ q ∈ Yset, FfacB pi kap lam t1 t2 lx t3 t4 p q) = 0 := by
    refine Finset.sum_eq_zero (fun p hp => Finset.sum_eq_zero (fun q hq => ?_))
    rw [FfacB,
      GA_zero_of_not_mem pi kap lam (Or.inl rfl)
        (not_mem_Rset_of_mem_Yset hp) (not_mem_Rset_of_mem_Yset hq) t1 t4,
      GA_zero_of_not_mem pi kap lam (Or.inl rfl)
        (not_mem_Rset_of_mem_Yset hp) (not_mem_Rset_of_mem_Yset hq) t2 t3]
    ring
  have hRY : (∑ p ∈ Rset, ∑ q ∈ Yset, FfacB pi kap lam t1 t2 lx t3 t4 p q) = 0 := by
    rw [show (∑ p ∈ Rset, ∑ q ∈ Yset, FfacB pi kap lam t1 t2 lx t3 t4 p q)
        = ∑ p ∈ Rset, ∑ q ∈ Yset,
            (((1 - sm lam lx) * pU pi Rset * pU pi Yset
                * ((1 - sm lam t4) * (1 - sm lam t2) * (rm lam kap t1 * rm lam kap t3)
                   + (1 - sm lam t1) * (1 - sm lam t3)
                     * (rm lam kap t4 * rm lam kap t2)))
              * (pi p * (pU pi Rset * pi p - qU pi Rset)))
              * (pi q * (pU pi Yset * pi q - qU pi Yset)) from by
      refine Finset.sum_congr rfl (fun p hp => Finset.sum_congr rfl (fun q hq => ?_))
      rw [FfacB, Kmat_cross_RY pi kap lam lx hp hq,
        GA_mixed_left pi kap lam (Or.inl rfl) hR hY hp (not_mem_Rset_of_mem_Yset hq) t1 t4,
        GA_mixed_right pi kap lam (Or.inr rfl) hR hY (not_mem_Yset_of_mem_Rset hp) hq t2 t3,
        GA_mixed_right pi kap lam (Or.inr rfl) hR hY (not_mem_Yset_of_mem_Rset hp) hq t1 t4,
        GA_mixed_left pi kap lam (Or.inl rfl) hR hY hp (not_mem_Rset_of_mem_Yset hq) t2 t3]
      ring]
    exact block_zero_RY pi _
  have hYR : (∑ p ∈ Yset, ∑ q ∈ Rset, FfacB pi kap lam t1 t2 lx t3 t4 p q) = 0 := by
    rw [show (∑ p ∈ Yset, ∑ q ∈ Rset, FfacB pi kap lam t1 t2 lx t3 t4 p q)
        = ∑ p ∈ Yset, ∑ q ∈ Rset,
            (((1 - sm lam lx) * pU pi Rset * pU pi Yset
                * ((1 - sm lam t4) * (1 - sm lam t2) * (rm lam kap t1 * rm lam kap t3)
                   + (1 - sm lam t1) * (1 - sm lam t3)
                     * (rm lam kap t4 * rm lam kap t2)))
              * (pi p * (pU pi Yset * pi p - qU pi Yset)))
              * (pi q * (pU pi Rset * pi q - qU pi Rset)) from by
      refine Finset.sum_congr rfl (fun p hp => Finset.sum_congr rfl (fun q hq => ?_))
      rw [FfacB, Kmat_cross_YR pi kap lam lx hp hq,
        GA_mixed_right pi kap lam (Or.inl rfl) hR hY (not_mem_Rset_of_mem_Yset hp) hq t1 t4,
        GA_mixed_left pi kap lam (Or.inr rfl) hR hY hp (not_mem_Yset_of_mem_Rset hq) t2 t3,
        GA_mixed_left pi kap lam (Or.inr rfl) hR hY hp (not_mem_Yset_of_mem_Rset hq) t1 t4,
        GA_mixed_right pi kap lam (Or.inl rfl) hR hY (not_mem_Rset_of_mem_Yset hp) hq t2 t3]
      ring]
    exact block_zero_YR pi _
  simp only [sum_univ_split, Finset.sum_add_distrib]
  rw [hRR, hYY, hRY, hYR]
  ring

/-- ★★★ **(XB)** 跨结点分组 `{0,3}/{1,2}`（拓扑 `ad|bc`）的期望权重恰为 0。 -/
theorem EwB_zero (pi : Fin 4 → ℝ) (hR : piR pi ≠ 0) (hY : piY pi ≠ 0)
    (kap lam t1 t2 lx t3 t4 : ℝ) : EwB pi kap lam t1 t2 lx t3 t4 = 0 := by
  rw [EwB_factor, EwB_sum pi hR hY kap lam t1 t2 lx t3 t4]
  ring

end Phylo.Stat.CASTERF84Scaffold

end
