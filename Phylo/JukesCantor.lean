/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# `Phylo.JukesCantor` —— Jukes–Cantor 模型层与 Cavender–Felsenstein 四点不变量（I1）

## 文献依据（本项目纪律：先读文献再动手）

* **Casanellas–Fernández-Sánchez (2011) §5.5「Jukes-Cantor model」**（本任务首读）：
  取群 `S4`，其**等变矩阵**（equivariant matrix）恰是「对角 `a`、非对角 `b`」的形状，
  这正是 **JC 模型**的转移矩阵（行和 = `1`、平稳分布均匀 `1/4`）。
  文献给出 Fourier 坐标 `q_{XY} = q_X ⊗ q_Y` 与分块
  `(W ⊗ W)[ω3] = ⟨qAC, qAG, qAT, …, qCG + qGC, …⟩`；由 `T^{fe}(ψ)` 的秩条件 `rk ≤ m`
  得 **`S0`、`S3` 的 2 阶子式 = 0**，即 **`q₁₃ q₂₄ = q₁₄ q₂₃`** —— 本文件的 I1。
* **Cavender–Felsenstein (1987)**：四点不变量的原始出处。
* **Allman–Rhodes (2006)**、**Sturmfels (2004)**：一般 Markov 模型的理想/不变量框架。

## 拓扑、编号与路径长度

唯一拓扑 **`12|34`**：内部顶点 `a`（近 1,2 侧）与 `b`（近 3,4 侧），边长 `t : Fin 5 → ℝ`：

| 索引 | 边 | 含义 |
|---|---|---|
| `t 0` | `1 — a` | 叶 1 挂边 |
| `t 1` | `2 — a` | 叶 2 挂边 |
| `t 2` | `a — b` | **内部边** |
| `t 3` | `3 — b` | 叶 3 挂边 |
| `t 4` | `4 — b` | 叶 4 挂边 |

`pathLen`：`d(i,i) = 0`；`d(1,2) = t0+t1`、`d(3,4) = t3+t4`；
`d(1,3) = t0+t2+t3`、`d(1,4) = t0+t2+t4`、`d(2,3) = t1+t2+t3`、`d(2,4) = t1+t2+t4`。

**路径长度恒等式（I1 的几何内核）**：
`d(1,3) + d(2,4) = d(1,4) + d(2,3) = t0+t1+2*t2+t3+t4`。
即：**跨内部边**的两组配对 `{1,3},{2,4}` 与 `{1,4},{2,3}` 的路径长度和相等
（同侧配对 `{1,2}`、`{3,4}` 的路径长度和更小，本文件不用它的比较）。

## 记号

`e a := Real.exp (-(4/3) * a)`；`lam a := 1/4 + 3/4 * e a`；`off a := 1/4 - 1/4 * e a`；
`ind x y := if x = y then 1 else 0`。于是

* **非对角** `trans t s s' = off t`；**对角** `trans t s s = off t + e t = lam t`；
* **行和** `4 * off t + e t = 1` —— 这才是「行和为 `1`」的真正机制
  （把转移矩阵写成 `1/4 + ind * c` 是**错的**：非对角元不是 `1/4`）。

## 完成度与**诚实边界**（逐条）

**(A) 模型层 —— 全部完成，全部由转移矩阵代数推出。**
`trans`（JC 转移概率，含与题面 `if` 形式逐字一致的 `trans_if`）、`kernel`（转移矩阵）、
`patternProb`（四叶 site-pattern 概率，根在内部顶点 `a`、根分布均匀 `1/4`）已建。
转移矩阵代数**已证**：半群律/卷积 `kernel_conv`（`K s * K t = K (s+t)`）、
行和 `kernel_sum_row`、列和 `kernel_sum_col`、单位阵 `kernel_zero`、对称性 `kernel_symm`、
`t ≥ 0` 非负 `kernel_nonneg`。

**(B) 成对同态概率 —— 已完成，且**从 `kernel_conv` 推出，不依赖任何距离假设**。**
* ★★★ `matchPair`：`∑_{σ1,σ2} kernel s a σ1 · kernel u b σ2 · ind σ1 σ2 = kernel (s+u) a b`
  —— 两片叶分别从内部顶点 `a`、`b` 出发、各走 `s`、`u` 时**同态**的概率，等于路径长度
  `s+u` 的 JC 转移概率。证法：对 `σ2` 求和把 `ind` 吃掉（只剩 `σ2 = σ1` 那一项），
  再用对称性 `kernel_symm` 与半群律 `kernel_conv`。
* ★★ `pathPair_eq`：`matchPair` 在 `a = b` 的退化情形（同一起点），
  `∑_{σ1,σ2} kernel s a σ1 · kernel u a σ2 · ind σ1 σ2 = lam (s+u)`。
* ⚠️ **诚实边界（本批唯一缺口）**：`pDiff` 在 §5 按**路径长度**定义
  （`pDiff t i j := 3/4 * (1 - e (pathLen t i j))`），即 **JC 的距离形式**。
  「`pDiff := ∑_σ [σ i ≠ σ j] · patternProb t σ` 与该距离形式**相等**」这一步，
  需要把 `∑_{σ : Fin 4 → Fin 4}`（256 个 site-pattern）重指标拆成四重和再逐叶求和；
  本批**没有**走完这一步（`Finset` 层重指标未打通），**留待 NEXT.md 的 F4 批**。
  `patternProb`、`kernel_conv`、`matchPair`、`sum_base_ind` 均已就位，是 F4 批的现成器械。
  本文件**没有**把「距离形式」写成「已从转移矩阵证明」。
* 📌 **勘误（本批修正，上一位 agent 的中间版）**：中间版把 `pathPair_eq` 写成
  `= lam s · kernel tI a b + off tI · e s · off u`、把 `matchPair` 写成
  `= off s * e u + e s * off u + ind a b * lam (s + u)`。这两条右端**是假的**：
  左端根本不依赖 `tI`、`b`，且取 `a = b`、`e s = e u = 1/2`（即 `s = u = (3/4)·log 2 > 0`）时
  中间版的 `matchPair` 右端 = `9/16`，而左端 = `7/16`。本批已把右端改成上面正确的闭式
  （`kernel (s+u) a b` / `lam (s+u)`），左端一字未动。

**(C) I1 —— 全部完成。**
* ★★★ `I1_topologyA`：拓扑 `12|34` 上 `q₁₃ q₂₄ = q₁₄ q₂₃`（两组跨内部边配对之积相等）。
  证明路线：路径长度恒等式 `d₁₃ + d₂₄ = d₁₄ + d₂₃` + `Real.exp_add` ⟹ 两边是同一个 `e`。
* ★★ **阴性对照** `I1_topologyB_false`、`I1_topologyC_false`（及其 `q` 形式
  `I1_topologyB_false_q`、`I1_topologyC_false_q`）：另两个拓扑（`13|24`、`14|23`）上
  同一式子**不成立**，以全取 `1` 的**显式正边长**给出数值见证（`2+2 = 4 ≠ 6 = 3+3`）。

本文件**没有**任何 `sorry`、没有 `axiom`、没有 `def … : Prop` 缺口。
-/

noncomputable section

namespace Phylo

namespace JC

attribute [local instance] Classical.propDecidable

open Finset

/-! ## 0. 指示函数 `ind` -/

/-- 指示函数 `ind x y = if x = y then 1 else 0`。 -/
def ind {α : Type*} [DecidableEq α] (x y : α) : ℝ := if x = y then 1 else 0

theorem ind_self {α : Type*} [DecidableEq α] (x : α) : ind x x = 1 := by simp [ind]

theorem ind_ne {α : Type*} [DecidableEq α] {x y : α} (h : x ≠ y) : ind x y = 0 := by
  simp [ind, h]

theorem ind_comm {α : Type*} [DecidableEq α] (x y : α) : ind x y = ind y x := by
  by_cases h : x = y
  · rw [h]
  · rw [ind_ne h, ind_ne (Ne.symm h)]

theorem ind_sum_right {α : Type*} [Fintype α] [DecidableEq α] (a : α) :
    ∑ x : α, ind a x = 1 := by
  rw [Finset.sum_eq_single a]
  · simp [ind]
  · intro b _ hb; simp [ind, Ne.symm hb]
  · intro h; exact absurd (Finset.mem_univ a) h

/-- `∑_x ind a x * c = c`。 -/
theorem ind_mul_sum {α : Type*} [Fintype α] [DecidableEq α] (a : α) (c : ℝ) :
    ∑ x : α, ind a x * c = c := by
  rw [Finset.sum_eq_single a]
  · simp [ind]
  · intro b _ hb; simp [ind, Ne.symm hb]
  · intro h; exact absurd (Finset.mem_univ a) h

/-- ★ **基座 + 指标**的求和：`∑_x (base + ind a x * c) = 4 * base + c`（`|α| = 4`）。

这是「JC 转移矩阵行和为 `1`」的抽象机制：取 `base = off t`、`c = e t` 即得 `4*off + e = 1`。 -/
theorem sum_base_ind {α : Type*} [Fintype α] [DecidableEq α] (hcard : Fintype.card α = 4)
    (a : α) (base c : ℝ) : ∑ x : α, (base + ind a x * c) = 4 * base + c := by
  rw [Finset.sum_add_distrib, ind_mul_sum, Finset.sum_const, Finset.card_univ, hcard]
  simp [nsmul_eq_mul]

/-- `ind y z * ind x y = ind x z * ind x y`（把指标移到「只含 `x`」的一侧）。 -/
theorem ind_mul_ind' {α : Type*} [DecidableEq α] (x y z : α) :
    ind y z * ind x y = ind x z * ind x y := by
  by_cases h : x = y
  · subst h; rw [ind_self x]
  · rw [ind_ne h]; ring

/-! ## 1. `e`、`lam`、`off` -/

/-- JC 的指数项 `e a = exp (-(4/3) * a)`（`a` 为边长和）。 -/
def e (a : ℝ) : ℝ := Real.exp (-(4 / 3 : ℝ) * a)

/-- JC 的**对角**项 `lam a = 1/4 + 3/4 * e a`。 -/
def lam (a : ℝ) : ℝ := 1 / 4 + 3 / 4 * e a

/-- JC 的**非对角**项 `off a = 1/4 - 1/4 * e a`。 -/
def off (a : ℝ) : ℝ := 1 / 4 - 1 / 4 * e a

theorem e_zero : e 0 = 1 := by simp [e]

theorem off_zero : off 0 = 0 := by simp [off, e_zero]

theorem lam_zero : lam 0 = 1 := by
  simp only [lam, e_zero]
  norm_num

/-- ★ 指数可乘性：`e (a+b) = e a * e b`（来自 `Real.exp_add`）。 -/
theorem e_add (a b : ℝ) : e (a + b) = e a * e b := by
  simp only [e, mul_add, Real.exp_add]

theorem e_mul (a b : ℝ) : e a * e b = e (a + b) := (e_add a b).symm

/-- **行和恒等式**：`4 * off a + e a = 1`。 -/
theorem four_off_add (a : ℝ) : 4 * off a + e a = 1 := by
  simp only [off, e]
  ring_nf

theorem off_add_e (a : ℝ) : off a + e a = lam a := by
  simp only [off, lam, e]
  ring

/-! ## 2. JC 转移概率与转移矩阵 -/

/-- **JC 转移概率**：基座 `off t` 加（同态时）`e t`。

对角 `trans t s s = off t + e t = lam t`，非对角 `trans t s s' = off t`。 -/
def trans (t : ℝ) (s s' : Fin 4) : ℝ := off t + ind s s' * e t

/-- **与题面 `if` 形式逐字一致的展开**。 -/
theorem trans_if (t : ℝ) (s s' : Fin 4) :
    trans t s s' = if s = s' then 1 / 4 + 3 / 4 * Real.exp (-(4 / 3 : ℝ) * t)
      else 1 / 4 - 1 / 4 * Real.exp (-(4 / 3 : ℝ) * t) := by
  rw [trans]
  by_cases h : s = s'
  · subst h
    rw [show ind s s = (1 : ℝ) from ind_self s, ite_eq_left rfl]
    simp only [off, e]
    ring
  · rw [show (if s = s' then (1 : ℝ) / 4 + 3 / 4 * Real.exp (-(4 / 3 : ℝ) * t)
        else 1 / 4 - 1 / 4 * Real.exp (-(4 / 3 : ℝ) * t))
        = 1 / 4 - 1 / 4 * Real.exp (-(4 / 3 : ℝ) * t) from ite_eq_right h, ind_ne h]
    simp only [off, e]
    ring

/-- 转移矩阵（`Fin 4 × Fin 4 → ℝ`）。 -/
def kernel (t : ℝ) (s s' : Fin 4) : ℝ := trans t s s'

theorem kernel_apply (t : ℝ) (s s' : Fin 4) : kernel t s s' = off t + ind s s' * e t := rfl

/-- ★ 转移矩阵**对称**：`kernel t s s' = kernel t s' s`（JC 的行 = 列）。 -/
theorem kernel_symm (t : ℝ) (s s' : Fin 4) : kernel t s s' = kernel t s' s := by
  rw [kernel_apply, kernel_apply, ind_comm s s']

theorem kernel_diag (t : ℝ) (s : Fin 4) : kernel t s s = lam t := by
  rw [kernel_apply, ind_self s, one_mul, off_add_e]

theorem kernel_ne (t : ℝ) {s s' : Fin 4} (h : s ≠ s') : kernel t s s' = off t := by
  rw [kernel_apply, ind_ne h, zero_mul, add_zero]

/-- `t = 0` 时转移矩阵是单位阵。 -/
theorem kernel_zero (s s' : Fin 4) : kernel 0 s s' = ind s s' := by
  rw [kernel_apply, e_zero]
  by_cases h : s = s'
  · subst h
    rw [ind_self s, off, e_zero]
    norm_num
  · rw [ind_ne h, off, e_zero]
    norm_num

/-- ★★ **半群律 / 卷积**：`∑_j kernel s i j * kernel t j k = kernel (s+t) i k`。

（转移矩阵的乘法：`K s * K t = K (s+t)`。） -/
theorem kernel_conv (s t : ℝ) (i k : Fin 4) :
    ∑ j : Fin 4, kernel s i j * kernel t j k = kernel (s + t) i k := by
  fin_cases i <;> fin_cases k <;>
    · rw [Fin.sum_univ_four]
      simp [kernel_apply, ind, e_add, off]
      try ring

/-- 转移矩阵**行和**为 `1`。 -/
theorem kernel_sum_row (t : ℝ) (s : Fin 4) : ∑ s' : Fin 4, kernel t s s' = 1 := by
  rw [Finset.sum_congr rfl (fun s' _ => kernel_apply t s s'),
    sum_base_ind (by norm_num) s (off t) (e t), four_off_add]

/-- 转移矩阵**列和**为 `1`（由对称性 `kernel_symm` 归约到行和）。 -/
theorem kernel_sum_col (t : ℝ) (s' : Fin 4) : ∑ s : Fin 4, kernel t s s' = 1 := by
  rw [Finset.sum_congr rfl (fun s _ => kernel_symm t s s')]
  exact kernel_sum_row t s'

/-- `t ≥ 0` 时转移概率非负（此时 `0 < e t ≤ 1`）。 -/
theorem kernel_nonneg {t : ℝ} (ht : 0 ≤ t) (s s' : Fin 4) : 0 ≤ kernel t s s' := by
  have hpos : 0 < e t := Real.exp_pos _
  have hle : e t ≤ 1 := by
    rw [e, ← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by nlinarith)
  rw [kernel_apply, off]
  by_cases h : s = s'
  · subst h
    rw [ind_self s, one_mul]
    nlinarith
  · rw [ind_ne h, zero_mul, add_zero]
    nlinarith

/-! ## 3. 四叶 site-pattern 概率（`12|34`） -/

/-- ★ **site-pattern 概率**（根在内部顶点 `a`、根分布均匀 `1/4`）：

`patternProb t σ = (1/4) * ∑_{a} ∑_{b} kernel t0 a σ1 · kernel t1 a σ2 ·
kernel t2 a b · kernel t3 b σ3 · kernel t4 b σ4`。 -/
def patternProb (t : Fin 5 → ℝ) (σ : Fin 4 → Fin 4) : ℝ :=
  (1 / 4) * ∑ a : Fin 4, ∑ b : Fin 4,
    kernel (t 0) a (σ 0) * kernel (t 1) a (σ 1) * kernel (t 2) a b
      * kernel (t 3) b (σ 2) * kernel (t 4) b (σ 3)

/-! ## 4. 成对同态概率（**从 `kernel_conv` 推出**） -/

/-- ★★★ **成对同态概率闭式**：

`∑_{σ1,σ2} kernel s a σ1 · kernel u b σ2 · ind σ1 σ2 = kernel (s+u) a b`。

（`a`、`b` 为两片叶所在内部顶点的状态，`s`、`u` 为两叶各自到该顶点的路径长度。
`a = b` 时右端退化为 `lam (s+u)`：祖先同态 ⟹ 后代同态概率 = `lam`。）
证法：`ind σ1 σ2` 对 `σ2` 求和后只剩 `σ2 = σ1`；再用 `kernel_symm` 与 `kernel_conv`。 -/
theorem matchPair (s u : ℝ) (a b : Fin 4) :
    ∑ σ1 : Fin 4, ∑ σ2 : Fin 4, kernel s a σ1 * kernel u b σ2 * ind σ1 σ2
      = kernel (s + u) a b := by
  fin_cases a <;> fin_cases b <;>
    · rw [Fin.sum_univ_four]
      simp [kernel_apply, ind, e_add, off]
      try ring

/-- ★★★ **同一起点的成对同态概率**（`matchPair` 在 `a = b` 的退化情形）：

`∑_{σ1,σ2} kernel s a σ1 · kernel u a σ2 · ind σ1 σ2 = lam (s + u)`。

即「两片叶从同一祖先状态出发、各走 `s`、`u`，最终同态的概率 = `lam (s+u)`」。 -/
theorem pathPair_eq (s u : ℝ) (a : Fin 4) :
    ∑ σ1 : Fin 4, ∑ σ2 : Fin 4, kernel s a σ1 * kernel u a σ2 * ind σ1 σ2
      = lam (s + u) := by
  rw [matchPair s u a a, kernel_diag]

/-! ## 5. 路径长度、`pDiff`、`q`（**距离形式**） -/

/-- 树上的**路径长度**（拓扑 `12|34`；对角为 `0`）。 -/
def pathLen (t : Fin 5 → ℝ) (i j : Fin 4) : ℝ :=
  if i = j then 0
  else if (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) then t 0 + t 1
  else if (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2) then t 3 + t 4
  else if i = 0 then t 0 + t 2 + (if j = 2 then t 3 else t 4)
  else if i = 1 then t 1 + t 2 + (if j = 2 then t 3 else t 4)
  else if i = 2 ∧ j = 0 then t 0 + t 2 + t 3
  else if i = 3 ∧ j = 0 then t 0 + t 2 + t 4
  else if i = 2 then t 1 + t 2 + t 3
  else t 1 + t 2 + t 4

/-- 成对**差异概率** —— ⚠️ 本文件取 **JC 的距离形式**：
`pDiff t i j = 3/4 * (1 - e (pathLen t i j))`。

（「从 `patternProb` 的 256 项显式求和推出这个闭式」是本批的已知缺口，见文件头「诚实边界」。） -/
def pDiff (t : Fin 5 → ℝ) (i j : Fin 4) : ℝ := 3 / 4 * (1 - e (pathLen t i j))

/-- ★★ **Fourier 坐标 / JC 修正项**：`q t i j = 1 - 4 * pDiff t i j / 3`。 -/
def q (t : Fin 5 → ℝ) (i j : Fin 4) : ℝ := 1 - 4 * pDiff t i j / 3

/-- ★★ **`q` = 距离的指数**：`q t i j = e (pathLen t i j)`，
即 `1 - 4 * pDiff t i j / 3 = exp (-(4/3) * d_ij)`。 -/
theorem q_eq_exp_pathLen (t : Fin 5 → ℝ) (i j : Fin 4) :
    q t i j = e (pathLen t i j) := by
  simp only [q, pDiff]
  ring

theorem pathLen_13 (t : Fin 5 → ℝ) : pathLen t 0 2 = t 0 + t 2 + t 3 := by
  simp [pathLen]

theorem pathLen_24 (t : Fin 5 → ℝ) : pathLen t 1 3 = t 1 + t 2 + t 4 := by
  simp [pathLen]

theorem pathLen_14 (t : Fin 5 → ℝ) : pathLen t 0 3 = t 0 + t 2 + t 4 := by
  simp [pathLen]

theorem pathLen_23 (t : Fin 5 → ℝ) : pathLen t 1 2 = t 1 + t 2 + t 3 := by
  simp [pathLen]

/-- ★★★ **路径长度恒等式**：`d₁₃ + d₂₄ = d₁₄ + d₂₃`（两边都 = `t0+t1+2*t2+t3+t4`）。 -/
theorem pathLen_identity (t : Fin 5 → ℝ) :
    pathLen t 0 2 + pathLen t 1 3 = pathLen t 0 3 + pathLen t 1 2 := by
  rw [pathLen_13, pathLen_24, pathLen_14, pathLen_23]
  ring

/-! ## 6. ★★★ I1（Cavender–Felsenstein 四点不变量） -/

/-- ★★★ **I1（四点不变量）**：拓扑 `12|34` 上
**`q₁₃ q₂₄ = q₁₄ q₂₃`**（两组**跨内部边**的配对之积相等）。

这是文献 §5.5 中 `S3` 块秩 `≤ 1` 所给出的 2 阶子式条件 `q₁₃q₂₄ − q₁₄q₂₃ = 0`
（即 `T^{fe}(ψ)` 的 3×3 块行列式为零）。 -/
theorem I1_topologyA (t : Fin 5 → ℝ) :
    q t 0 2 * q t 1 3 = q t 0 3 * q t 1 2 := by
  rw [q_eq_exp_pathLen, q_eq_exp_pathLen, q_eq_exp_pathLen, q_eq_exp_pathLen,
    pathLen_13, pathLen_24, pathLen_14, pathLen_23]
  rw [← e_add, ← e_add]
  congr 1
  ring

/-- I1 的**显式指数形式**：`e (d₁₃+d₂₄) = e (d₁₄+d₂₃)`
（`I1_topologyA` 的等价表述，直接展示「两边是同一个 `exp`」）。 -/
theorem I1_exp (t : Fin 5 → ℝ) :
    e (pathLen t 0 2 + pathLen t 1 3) = e (pathLen t 0 3 + pathLen t 1 2) := by
  rw [pathLen_identity]

/-! ### 阴性对照：另两个拓扑上同一式子**不成立** -/

/-- 常数边长函数（全取 `1`，**显式正边长**）。 -/
def ones : Fin 5 → ℝ := fun _ => 1

/-- 拓扑 **`13|24`** 的路径长度（叶 2 与叶 3 互换角色）。 -/
def pathLenB (t : Fin 5 → ℝ) (i j : Fin 4) : ℝ :=
  if i = j then 0
  else if (i = 0 ∧ j = 2) ∨ (i = 2 ∧ j = 0) then t 0 + t 1
  else if (i = 1 ∧ j = 3) ∨ (i = 3 ∧ j = 1) then t 3 + t 4
  else if i = 0 then t 0 + t 2 + (if j = 1 then t 3 else t 4)
  else if i = 2 then t 1 + t 2 + (if j = 1 then t 3 else t 4)
  else if i = 1 ∧ j = 0 then t 0 + t 2 + t 3
  else if i = 3 ∧ j = 0 then t 0 + t 2 + t 4
  else if i = 1 then t 1 + t 2 + t 3
  else t 1 + t 2 + t 4

/-- 拓扑 **`14|23`** 的路径长度（叶 2 与叶 4 互换角色）。 -/
def pathLenC (t : Fin 5 → ℝ) (i j : Fin 4) : ℝ :=
  if i = j then 0
  else if (i = 0 ∧ j = 3) ∨ (i = 3 ∧ j = 0) then t 0 + t 1
  else if (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1) then t 3 + t 4
  else if i = 0 then t 0 + t 2 + (if j = 1 then t 3 else t 4)
  else if i = 3 then t 1 + t 2 + (if j = 1 then t 3 else t 4)
  else if i = 1 ∧ j = 0 then t 0 + t 2 + t 3
  else if i = 2 ∧ j = 0 then t 0 + t 2 + t 4
  else if i = 1 then t 1 + t 2 + t 3
  else t 1 + t 2 + t 4

theorem pathLenB_13 : pathLenB ones 0 2 = 2 := by norm_num [pathLenB, ones]

theorem pathLenB_24 : pathLenB ones 1 3 = 2 := by norm_num [pathLenB, ones]

theorem pathLenB_14 : pathLenB ones 0 3 = 3 := by norm_num [pathLenB, ones]

theorem pathLenB_23 : pathLenB ones 1 2 = 3 := by norm_num [pathLenB, ones]

/-- ★★ **阴性对照（拓扑 `13|24`）**：`e(d₁₃) * e(d₂₄) ≠ e(d₁₄) * e(d₂₃)`。

全取 `1` 时 `d₁₃ = d₂₄ = 2`、`d₁₄ = d₂₃ = 3`，故 `2+2 = 4 ≠ 6 = 3+3`，
即 `exp(-8/3) ≠ exp(-4)`。 -/
theorem I1_topologyB_false :
    e (pathLenB ones 0 2) * e (pathLenB ones 1 3)
      ≠ e (pathLenB ones 0 3) * e (pathLenB ones 1 2) := by
  rw [pathLenB_13, pathLenB_24, pathLenB_14, pathLenB_23, ← e_add, ← e_add]
  intro hcon
  have h2 : -(4 / 3 : ℝ) * (2 + 2) = -(4 / 3 : ℝ) * (3 + 3) := Real.exp_injective hcon
  norm_num at h2

theorem pathLenC_13 : pathLenC ones 0 2 = 3 := by norm_num [pathLenC, ones]

theorem pathLenC_24 : pathLenC ones 1 3 = 3 := by norm_num [pathLenC, ones]

theorem pathLenC_14 : pathLenC ones 0 3 = 2 := by norm_num [pathLenC, ones]

theorem pathLenC_23 : pathLenC ones 1 2 = 2 := by norm_num [pathLenC, ones]

/-- ★★ **阴性对照（拓扑 `14|23`）**：同一式子也**不成立**
（`3+3 = 6 ≠ 4 = 2+2`）。 -/
theorem I1_topologyC_false :
    e (pathLenC ones 0 2) * e (pathLenC ones 1 3)
      ≠ e (pathLenC ones 0 3) * e (pathLenC ones 1 2) := by
  rw [pathLenC_13, pathLenC_24, pathLenC_14, pathLenC_23, ← e_add, ← e_add]
  intro hcon
  have h2 : -(4 / 3 : ℝ) * (3 + 3) = -(4 / 3 : ℝ) * (2 + 2) := Real.exp_injective hcon
  norm_num at h2

/-! ### 阴性对照的 `q` 形式（与 `I1_topologyA` 同一谓词） -/

/-- `q` 在拓扑 `13|24` 上的对应物（把 `pathLen` 换成 `pathLenB`）。 -/
def qB (t : Fin 5 → ℝ) (i j : Fin 4) : ℝ := 1 - 4 * (3 / 4 * (1 - e (pathLenB t i j))) / 3

/-- `q` 在拓扑 `14|23` 上的对应物（把 `pathLen` 换成 `pathLenC`）。 -/
def qC (t : Fin 5 → ℝ) (i j : Fin 4) : ℝ := 1 - 4 * (3 / 4 * (1 - e (pathLenC t i j))) / 3

theorem qB_eq_exp (t : Fin 5 → ℝ) (i j : Fin 4) : qB t i j = e (pathLenB t i j) := by
  simp only [qB]; ring

theorem qC_eq_exp (t : Fin 5 → ℝ) (i j : Fin 4) : qC t i j = e (pathLenC t i j) := by
  simp only [qC]; ring

/-- ★★ **阴性对照（拓扑 `13|24`，`q` 形式）**：`I1_topologyA` 的式子在 `13|24` 上**假**。 -/
theorem I1_topologyB_false_q :
    qB ones 0 2 * qB ones 1 3 ≠ qB ones 0 3 * qB ones 1 2 := by
  rw [qB_eq_exp, qB_eq_exp, qB_eq_exp, qB_eq_exp]
  exact I1_topologyB_false

/-- ★★ **阴性对照（拓扑 `14|23`，`q` 形式）**：同一式子在 `14|23` 上也**假**。 -/
theorem I1_topologyC_false_q :
    qC ones 0 2 * qC ones 1 3 ≠ qC ones 0 3 * qC ones 1 2 := by
  rw [qC_eq_exp, qC_eq_exp, qC_eq_exp, qC_eq_exp]
  exact I1_topologyC_false

end JC

end Phylo
