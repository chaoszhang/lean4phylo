/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.Stat.CASTERtL1
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# `Phylo.Stat.CASTERExpect` —— CASTER 期望层的**符号**（W44 · L2）

文献：`references/CASTER_NJ_2026-11-04.md` §3（假设 A1、定理 3、推论 2）。
派单口径：`W44_TO_DSH_prompt.txt` §4.3。

## 本文件只做 §4.3 允许的那一层

文档 A3 的**单一指数形式**
`E[t(ab|cd)|𝒢] = α·e^{−βΣℓ}·(1−e^{−γI})·ε` 是**近似**（文档 §3.3 自己标注「主导项可解析验证，
单一指数形式是近似」）。**本文件一个字都不用它的指数部分。**

文档 §3.4 的证明其实只用两件事：

1. **A1 的两个闭式**：`p_ab = 1 − (2/3)e^{−T}`、`p_ac = p_ad = (1/3)e^{−T}`；
2. **幅度与基因树无关且为正**（`φ = α W_aW_bW_cW_d f(I) > 0`）——这是文档 §3.4 自己
   用的口径（「`αW⁴f(I)>0`，故 `E[t]` 的符号即 `ε` 的符号」）。

于是

```text
E[ε] = p_ab·(+1) + (p_ac + p_ad)·(−1/2) = 1 − e^{−T}      (T > 0 时 > 0)
```

## 交付

| # | 定理 | 内容 |
|---|---|---|
| L2.0 | `pab` / `pac` | A1 的两个闭式（**定义**，不是公理、也不是定理） |
| L2.1 | `prob_sum` | `p_ab + p_ac + p_ad = 1` |
| L2.2 | `expEps_eq` | `E[ε] = 1 − e^{−T}` |
| L2.3 | `expEps_pos` | `T > 0 ⇒ E[ε] > 0` |
| L2.4 | `expected_true_pos` | `0 < φ·E[ε]`（真拓扑的期望 > 0） |
| L2.5 | `expected_false_neg` | `φ·E[ε]·(−½) < 0`（两个错拓扑的期望 < 0，文档定理 3） |
| L2.6 | `expected_false_eq` | 后两者**恰为**前者的 `−½`（文档推论 2，与 `T`、`f`、`W` 均无关） |
| L2.7 | `pab_gt_third` / `pac_lt_third` | `p_ab > 1/3 > p_ac`（文档 §3.4 的 `p_ab > 1/3` 备注） |

## 诚实边界

* `p_ab`、`p_ac` 是 **A1 的闭式**，本文件把它们落成 `def`（**不**从溯祖过程推出，
  也**不**当作公理）——这正是派单 §4.3 推荐的处置。
* `φ` **与基因树无关**是本文件的显式字段（`MSC4Expect.hφ` 只给正性）。真实的
  `α e^{−βΣℓ}(1−e^{−γI})` 随基因树变化；文档 §3.4 隐含地把它当常数，**本文件照它的口径
  写明这一点**，不假装证出了更强的结论。
* 「`E[ε]` 的两项概率加权」是**定义性的**（ε 只取 `+1`/`−1/2`，由 A3 的 ε 定义直接读出），
  不含任何未证命题。
-/

noncomputable section

namespace Phylo.Stat.CASTERExpect

open Real

/-! ## 1. A1 的两个闭式（定义） -/

/-- **A1 的真拓扑概率** `p_ab = 1 − (2/3)e^{−T}`（`T` = 内部枝长，coalescent units）。 -/
noncomputable def pab (T : ℝ) : ℝ := 1 - (2 / 3) * Real.exp (-T)

/-- **A1 的错拓扑概率** `p_ac = p_ad = (1/3)e^{−T}`（两张错拓扑等概率，由 `c ↔ d` 对称）。 -/
noncomputable def pac (T : ℝ) : ℝ := (1 / 3) * Real.exp (-T)

/-- **`E[ε]`**：`ε = +1` 的概率是 `p_ab`，`ε = −1/2` 的概率是 `p_ac + p_ad`。 -/
noncomputable def expEps (T : ℝ) : ℝ := pab T * 1 + (pac T + pac T) * (-(1 / 2))

/-! ## 2. 概率与期望的算术 -/

/-- ★ **L2.1**：三条基因树拓扑的概率之和为 `1`。 -/
theorem prob_sum (T : ℝ) : pab T + pac T + pac T = 1 := by
  unfold pab pac
  ring

/-- ★★ **L2.2（文档 §3.4 的算式）**：`E[ε] = 1 − e^{−T}`。 -/
theorem expEps_eq (T : ℝ) : expEps T = 1 - Real.exp (-T) := by
  unfold expEps pab pac
  ring

/-- ★★ **L2.3**：`T > 0 ⇒ E[ε] > 0`。 -/
theorem expEps_pos {T : ℝ} (hT : 0 < T) : 0 < expEps T := by
  rw [expEps_eq]
  have h1 : Real.exp (-T) < 1 := by
    rw [Real.exp_lt_one_iff]; linarith
  linarith

/-- `p_ac > 0`（任意 `T`）。 -/
theorem pac_pos (T : ℝ) : 0 < pac T := by
  unfold pac
  have h := Real.exp_pos (-T)
  linarith

/-- ★ **L2.7a**：`T > 0 ⇒ p_ab > 1/3`（文档 §3.4 的备注）。 -/
theorem pab_gt_third {T : ℝ} (hT : 0 < T) : 1 / 3 < pab T := by
  unfold pab
  have h1 : Real.exp (-T) < 1 := by
    rw [Real.exp_lt_one_iff]; linarith
  linarith

/-- ★ **L2.7b**：`T > 0 ⇒ p_ac < 1/3`。 -/
theorem pac_lt_third {T : ℝ} (hT : 0 < T) : pac T < 1 / 3 := by
  unfold pac
  have h1 : Real.exp (-T) < 1 := by
    rw [Real.exp_lt_one_iff]; linarith
  linarith

/-! ## 3. 显式假设包（A1 + 幅度正性）与定理 3 -/

/-- **四物种 MSC 期望层假设包**（A1 ＋「幅度为正且与基因树无关」，文档 §3.4 的口径）。

字段全部**显式**：`T`（内部枝长）· `hT` · `φ`（幅度 `αW_aW_bW_cW_d f(I)`）· `hφ`。
`p_ab`/`p_ac` 不进结构 —— 它们是 `pab`/`pac` 两个 `def`，由 `A1` 决定。 -/
structure MSC4Expect where
  /-- 内部枝长（coalescent units） -/
  T : ℝ
  /-- 内部枝长为正 -/
  hT : 0 < T
  /-- 幅度 `α·W_aW_bW_cW_d·f(I)`（文档 §3.4 把它当与基因树无关的正常数） -/
  φ : ℝ
  /-- 幅度为正 -/
  hφ : 0 < φ

namespace MSC4Expect

variable (M : MSC4Expect)

/-- ★★★ **L2.4（文档定理 3，真拓扑）**：`E[t(ab|cd)] = φ·E[ε] > 0`。 -/
theorem expected_true_pos : 0 < M.φ * expEps M.T :=
  mul_pos M.hφ (expEps_pos M.hT)

/-- ★★★ **L2.5（文档定理 3，两个错拓扑）**：`E[t(ac|bd)] = E[t(ad|bc)] = φ·E[ε]·(−½) < 0`。 -/
theorem expected_false_neg : M.φ * expEps M.T * (-(1 / 2)) < 0 := by
  have h := expected_true_pos M
  nlinarith

/-- ★★ **L2.6（文档推论 2）**：错拓扑的期望**恰为**真拓扑期望的 `−½`，与 `T`、`f`、`W` 无关。 -/
theorem expected_false_eq : M.φ * expEps M.T * (-(1 / 2)) = -(1 / 2) * (M.φ * expEps M.T) := by
  ring

/-- ★★ **L2.5′（文档推论 2 的抽象形式）**：若 `E[w(ab|cd)] = A`、`E[w(ac|bd)] = E[w(ad|bc)] = B`，
则 `E[t(ab|cd)] = A − B`、`E[t(ac|bd)] = −½(A − B)`。 -/
theorem neg_half_exact (A B : ℝ) :
    B - (1 / 2) * (A + B) = -(1 / 2) * (A - B) := by
  ring

/-- 真拓扑与错拓扑的期望**同号相反**（推论 2 的直接推论）。 -/
theorem signs_opposite : M.φ * expEps M.T * (-(1 / 2)) < 0 ∧ 0 < M.φ * expEps M.T :=
  ⟨expected_false_neg M, expected_true_pos M⟩

end MSC4Expect

end Phylo.Stat.CASTERExpect
