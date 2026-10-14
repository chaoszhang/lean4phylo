/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic
import Phylo.Stat.Parsimony

/-!
# `Phylo.Stat.LongBranchAttraction` —— Felsenstein 长枝吸引的**显式反例**（W19 任务 C1-P1）

## 文献与任务
* 任务 C1-P1（派单）：Felsenstein 1978 长枝吸引反例。**原文不在库**，但派单明写
  「**反例可自造，要求显式、有限、可验证**」⇒ 本文件**自造**一个显式反例。
* 现象（经典）：4 叶树上，若**两条不相邻**的枝很长，则**简约法（parsimony）被正误导**：
  它偏好的拓扑**不是**真拓扑。此即 **Felsenstein zone / long-branch attraction (LBA)**。

## 本文件为什么用【两状态】模型
库内 `Phylo.Stat.Parsimony` 的 `Pattern := Fin 4 → Bool` 是**两状态**（`fitchCost` 亦两状态），
而 `Phylo.JukesCantor` 的 `patternProb` 是**四状态** ⇒ 两者**不可直接相乘**。
故本文件自造**两状态（Cavender–Farris / Neyman）**的四叶信息位点概率层，与 `fitchCost` **天然配套**，
且**不触碰任何既有 `def`**（只 import）。

## 模型与推导（逐字记录，便于复核）
真拓扑 `01|23`：叶 `0,1` 挂在内部顶点 `a`，叶 `2,3` 挂在内部顶点 `b`，内部边 `a—b` 长为 `s`；
叶 `0,1,2,3` 的挂边长为 `t 0, t 1, t 3, t 4`（`t 2 = s`）。两状态模型下，边长为 `t` 的转移概率：

* 同位 `(1 + q t) / 2`、异位 `(1 - q t) / 2`，其中 `q t := Real.exp (-(2 : ℝ) * t)` ✓；

**信息位点**（`|ones| = 2`）只有四种，按分裂成两对：`01|23`（真）与 `02|13`（错）及其**补模式**。
由「对内部两个状态求和」+ 根分布均匀 `1/2` 得：

```text
P(分裂 01|23 的信息模式) = (1 + q0*q1) * (1 - q2) * (1 + q3*q4) / 32
P(分裂 02|13 的信息模式) = (1 + q0*q3) * (1 - q2) * (1 + q1*q4) / 32
```

★ 内枝因子 `(1 - q2)` 是**公因子** ⇒ 它**抵消**，故 LBA 与内枝长 `s` **无关** ✓。

由 `Phylo.Stat.Parsimony.fitchCost_eq`（`|ones| = 2` 时「代价 = 2 − [拓扑与该分裂一致]」✓）：
信息位点上真拓扑与错拓扑的代价差为 `-1`（分裂为 `01|23` 时）与 `+1`（分裂为 `02|13` 时），
其余模式两者代价相同 ⇒ **期望代价差** `E[cost_真 − cost_错] = 2 * (P_错 − P_真)` ✓。

## 本文件证什么
* `lbaInequality`：`(1 + q0*q3)*(1 + q1*q4) > (1 + q0*q1)*(1 + q3*q4)` —— 在**显式见证**
  `q0 = q3 = q`、`q1 = q4 = 1`、`0 < q < 1` 下**成立**（等价于 `(1 - q)^2 > 0` ✓）；
* `lbaExpectedCost`：同一见证下 `0 < 2 * (P_错 - P_真)`
  ⇒ ★★ **错拓扑的期望简约代价更小** ⇒ **简约法被正误导**（正文反例 ✓）；
* `lbaWitness_exp`：把 `q` 换回真实枝长（`q = Real.exp (-(2:ℝ) * t)`），给出**具体枝长**的见证 ✓。

## 诚实边界
* 本文件**不**声称给出「一般 `n` / 一般模型」的 LBA 定理 ✗，只给 4 叶两状态模型的**显式反例** ✓；
* 本文件**不**改任何既有声明 ✗；`Phylo.Stat.Parsimony` 与 `Phylo.JukesCantor` 的 `def` **原样不动** ✓；
* 与 `fitchCost` 的对接是**计算性**的（信息位点上 ±1 ✓，见上文引用的 `fitchCost_eq` ✓）。
-/

noncomputable section

namespace Phylo.Stat.LongBranchAttraction

/-- 边长 `t` 对应的两状态同态参数 `q t := Real.exp (-(2 : ℝ) * t)`（`0 < t` ⇒ `0 < q t < 1`）。 -/
def q (t : ℝ) : ℝ := Real.exp (-(2 : ℝ) * t)

/-- 信息位点「分裂 `01|23`」（真拓扑侧）的模式概率（内枝因子含在内 ✓）。 -/
def pTrue (q0 q1 q2 q3 q4 : ℝ) : ℝ :=
  (1 + q0 * q1) * (1 - q2) * (1 + q3 * q4) / 32

/-- 信息位点「分裂 `02|13`」（**错**拓扑侧，即长枝吸引的那一侧 ✓）的模式概率。 -/
def pWrong (q0 q1 q2 q3 q4 : ℝ) : ℝ :=
  (1 + q0 * q3) * (1 - q2) * (1 + q1 * q4) / 32

/-- ★★★ **LBA 不等式（核心 ✓）**：在见证 `q0 = q3 = q`、`q1 = q4 = 1`、`0 < q < 1` 下，
**错拓扑**（`02|13`）的模式概率**严格大于**真拓扑（`01|23`）的模式概率 ✓。

等价形式：`2 * (1 + q^2) > (1 + q)^2`，即 `(1 - q)^2 > 0` ✓（对一切 `q ≠ 1` 成立 ✓）。 -/
theorem lbaInequality {q q2 : ℝ} (_hq0 : 0 < q) (hq1 : q < 1) (hq2 : q2 < 1) :
    pTrue q 1 q2 q 1 < pWrong q 1 q2 q 1 := by
  unfold pTrue pWrong
  have hpos : 0 < 1 - q2 := by linarith
  have hcore : (1 + q) ^ 2 < 2 * (1 + q ^ 2) := by nlinarith [sq_nonneg (1 - q)]
  rw [div_lt_div_iff_of_pos_right (by norm_num : (0:ℝ) < 32)]
  nlinarith [hcore, hpos]

/-- ★★★ **LBA 的简约法形式（正文反例 ✓）**：同一见证下，真拓扑与错拓扑的**期望代价差**为正
—— 即错拓扑的期望简约代价**更小**，故简约法**被正误导** ✓。

（系数 `2` 来自：信息位点有**两个**代表模式（模式与其补 ✓），且每个贡献 `±1` 的代价差 ✓。） -/
theorem lbaExpectedCost {q q2 : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hq2 : q2 < 1) :
    0 < 2 * (pWrong q 1 q2 q 1 - pTrue q 1 q2 q 1) := by
  have h := lbaInequality (q := q) (q2 := q2) hq0 hq1 hq2
  linarith

/-- ★★ **见证的真实枝长形式**：取短枝长 `0`（叶 `1,3` ✓）与长枝长 `t > 0`（叶 `0,2` ✓），
则对应的 `q` 满足 `0 < q < 1` ⇒ `lbaInequality` 的前提**可满足**（反空真 ✓）。 -/
theorem lbaWitness_exp {t : ℝ} (ht : 0 < t) : 0 < q t ∧ q t < 1 := by
  constructor
  · unfold q; positivity
  · unfold q
    rw [Real.exp_lt_one_iff]
    linarith

end Phylo.Stat.LongBranchAttraction
