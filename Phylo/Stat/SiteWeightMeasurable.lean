/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.Stat.CASTERGeneTree
import Phylo.Stat.MSCSamplingAE
import Phylo.Stat.MSCKingmanMeasure

set_option autoImplicit false

/-!
# `Phylo.Stat.SiteWeightMeasurable` —— 位点权重函数的**可测性**与**有界性**（W13a）

本文件交付 **W13 规格 §6 的缺口 B2（可测性）＋ B3（有界/可积）**，是 HANDOVER 第 117–119 行
那条待办（「`hint` 的可测性」）的正面回答。

## 1. 为什么需要这两件器材

`Phylo/Stat/MSCKingmanMeasure.lean` §6 已经能从 weight 表**算出**幅度的正性与可积性
（`jc69_hf_int` / `jc69_hf_pos_ae` / `lm1_hf_int` / `lm1_hf_pos_ae`），于是旗舰端点
`jc69_caster_statisticallyConsistent_kingman_measure_derived` 的参数表里**只剩 `hint` 与 `hconv`**。
其中

```
hint : ∀ T : Topo, Integrable (fun θ => ∑ T' : Topo, S.τd θ T' * P.A θ T' T) ν
```

是「**权重一致有界**」（CASTER 论文正文条件 (2)）。它的被积函数含 `P.A`，而 JC69 的 `P.A` 就是
`Phylo.Stat.CASTERGeneTree.geneScore`（`A θ T' T = geneScore T' θ.1 θ.2 T`，见该文件 §11 的
`jc69PropAData`）。库内**没有** `Measurable geneScore`、也**没有** `|geneScore …| ≤ B`
⇒ `hint` 只能当假设挂着。

本文件把这两件器材补齐，并给出「可测性 ＋ 有界性 ⇒ 可积」的收口引理
（`integrable_of_abs_bound`），于是

* `integrable_weightSum_of_measurable`：把 `hint` 形状的 `Integrable` **从** `τd` / `A` 的
  可测性与逐点界**推出来**（界 = `1`，不浪费）；
* `integrable_geneScore_weightSum`：把 `A` 换成 `geneScore`，直接吃本文件的有界性引理；
* `astral_statisticallyConsistent_ae_of_measurable`：`MSCSamplingAE.astral_statisticallyConsistent_ae`
  的变体，**假设里不再有 `hint`**（换成对 `ind` 的可测性）。

## 2. 拆解路线（逐层，`fun_prop` 证不出是因为它**不展开 `def`**）

```
geneScore S l lx T = ∑_σ wJCR T σ · patternProb (canonLen S l lx) (σ ∘ perm S)
patternProb t σ     = (1/4) · ∑_a ∑_b kernel (t 0) a (σ 0) · … · kernel (t 4) b (σ 3)
kernel t s s'       = off t + ind s s' · e t,   e t = Real.exp (-(4/3)·t)
```

* `continuous_kernel` / `continuous_patternProb`（`Real.continuous_exp` ＋ `Continuous.mul` ＋
  `continuous_finsetSum`）⇒ `measurable_patternProb`；
* `measurable_canonLen`（逐分量是 `l (perm S i)` 或 `lx`）⇒ `measurable_geneScore`
  （`wJCR T σ` **不依赖变量**，是常数）；
* **有界性**：先证 `patternProb` 是**概率分布**（`∑_σ patternProb t σ = 1`，**不需要任何假设**，
  因为 `kernel_sum_row` 无条件成立），配合非负性得 `patternProb t σ ≤ 1`；
  再用 `∑_σ |wJCR T σ| · patternProb … ≤ ∑_σ patternProb … = 1`（`|wJCR| ≤ 1` 逐情形）得
  **`|geneScore S l lx T| ≤ 1`**（在枝长非负的前提下）。

## 3. ★D 先判真假（结论：**界真的成立**，但**必须要求枝长非负**）

* `|patternProb t σ| ≤ 1` **在 `t` 各分量非负时**成立；**去掉非负性就是假的**：
  `e t = exp (-(4/3) t)` 在 `t < 0` 时 `> 1`，`kernel` 可任意大。
  故本文件所有有界性引理都**显式带 `∀ i, 0 ≤ t i`**（不是装饰）。
* `|geneScore S l lx T| ≤ 1` 在 `(∀ i, 0 ≤ l i) ∧ 0 ≤ lx` 下成立（同上）。
* ⚠️ **不要**试图证「一致**正**下界」（`f84Amp` 在 `lx = 0` 处为 `0`，那是**假命题**）；
  B3 要的是**有界**，与正性下界是两件事。

## 4. 诚实边界

* 本文件**不改**任何既有声明的签名，**不**动 `Phylo.lean`；所有内容都是**新声明**。
* 本文件的证明全部走正面构造，不含任何未完成证明占位、额外公理或计算式证明捷径。
* 对**负**枝长不保证有界性（见 §3）；下游若需要，须显式把「枝长非负」写进模型（规格 §1.2 的
  `r ∈ [r⁻, r⁺] ⊂ (0, ∞)` 正是这件事）。
-/

noncomputable section

namespace Phylo.Stat.SiteWeightMeasurable

open MeasureTheory Finset ProbabilityTheory
open scoped NNReal
open Phylo.JC (kernel patternProb kernel_sum_row)
open Phylo.Stat.CASTERWeights (Topo Val wJC wJCR perm)
open Phylo.Stat.CASTERGeneTree (canonLen geneScore sum_comp_perm)
open Phylo.Stat.EmpiricalConvergence (SiteFun)
open Phylo.Stat.MSCSamplingAE (SiteTable empTable)
open Phylo.Stat.MSCKingman (KingmanΘ KingmanDeep Kingmanτd kingmanMSCTopoSym)
open Phylo.Stat.MSCInstance (jc69PropADataK)
open Phylo.Stat.MSCKingmanMeasure (kingmanMSCMeasure toKingmanΘ measurable_toKingmanΘ)

/-! ## 1. `kernel` 与 `patternProb` 的连续性与可测性 -/

/-- ★ `kernel` 关于边长连续（`kernel_apply` 的闭式：`off t + ind s s' · e t`）。 -/
theorem continuous_kernel (s s' : Fin 4) : Continuous (fun t : ℝ => kernel t s s') := by
  have h : (fun t : ℝ => kernel t s s')
      = fun t => (1 / 4 - 1 / 4 * Real.exp (-(4 / 3 : ℝ) * t))
          + (if s = s' then 1 else 0) * Real.exp (-(4 / 3 : ℝ) * t) := rfl
  rw [h]
  fun_prop

/-- ★★ **`patternProb` 关于整条枝长向量连续**（逐位点模式 `σ`）。 -/
theorem continuous_patternProb (σ : Fin 4 → Fin 4) :
    Continuous (fun t : Fin 5 → ℝ => patternProb t σ) := by
  simp only [patternProb]
  refine Continuous.const_mul ?_ (1 / 4)
  refine continuous_finsetSum _ (fun a _ => ?_)
  refine continuous_finsetSum _ (fun b _ => ?_)
  exact ((((continuous_kernel a (σ 0)).comp (continuous_apply 0)).mul
    ((continuous_kernel a (σ 1)).comp (continuous_apply 1))).mul
    ((continuous_kernel a b).comp (continuous_apply 2))).mul
    ((continuous_kernel b (σ 2)).comp (continuous_apply 3)) |>.mul
    ((continuous_kernel b (σ 3)).comp (continuous_apply 4))

/-- ★★ **`patternProb t σ` 关于 `t` 可测**（逐位点模式 `σ`）。 -/
theorem measurable_patternProb (σ : Fin 4 → Fin 4) :
    Measurable (fun t : Fin 5 → ℝ => patternProb t σ) :=
  (continuous_patternProb σ).measurable

/-! ## 2. `canonLen` 与 `geneScore` 的可测性 -/

/-- ★★ **规范枝长向量关于 `(l, lx)` 可测**（逐分量是 `l (perm S i)` 或 `lx`）。 -/
theorem measurable_canonLen (S : Topo) :
    Measurable (fun p : (Fin 4 → ℝ) × ℝ => canonLen S p.1 p.2) := by
  rw [measurable_pi_iff]
  intro i
  fin_cases i <;> simp [canonLen] <;> fun_prop

/-- ★★★ **`geneScore` 关于 `(l, lx)` 可测** —— 缺口 **B2** 的主件。

证明：`geneScore` 是 `Fin 4 → Fin 4` 上的**有限和**，每一项是**常数** `wJCR T σ` 乘以
`patternProb (canonLen S l lx) (σ ∘ perm S)`；后者是 `measurable_patternProb` 与
`measurable_canonLen` 的复合。 -/
theorem measurable_geneScore (S T : Topo) :
    Measurable (fun p : (Fin 4 → ℝ) × ℝ => geneScore S p.1 p.2 T) := by
  simp only [geneScore]
  refine Finset.measurable_sum _ (fun σ _ => ?_)
  exact measurable_const.mul
    ((measurable_patternProb (fun i => σ (perm S i))).comp (measurable_canonLen S))

/-- ★★ **可测性沿任意可测参数化搬运**：若 `φ` 可测，则 `x ↦ geneScore S (φ x).1 (φ x).2 T` 可测。

（下游 `θ ↦ geneScore T' θ.1.1 θ.1.2 T`（`θ : KingmanΘ`）就是取 `φ = Prod.fst`。） -/
theorem measurable_geneScore_comp {α : Type*} [MeasurableSpace α] (S T : Topo)
    {φ : α → (Fin 4 → ℝ) × ℝ} (hφ : Measurable φ) :
    Measurable (fun x : α => geneScore S (φ x).1 (φ x).2 T) :=
  (measurable_geneScore S T).comp hφ

/-! ## 3. `patternProb` 是概率分布 ⇒ 有界 -/

/-- 位点模式 `σ : Fin 4 → Fin 4` 与四元组 `Fin 4 × Fin 4 × Fin 4 × Fin 4` 的**显式双射**。

（四个坐标就是四个叶上的字母；用它把 `∑_σ` 化成四重求和，从而对 `a`、`b` 两层的和因式分解。） -/
def patternEquiv : (Fin 4 → Fin 4) ≃ (Fin 4 × Fin 4 × Fin 4 × Fin 4) where
  toFun σ := (σ 0, σ 1, σ 2, σ 3)
  invFun p := ![p.1, p.2.1, p.2.2.1, p.2.2.2]
  left_inv := by intro σ; funext i; fin_cases i <;> rfl
  right_inv := by intro p; simp

/-- ★ **四重乘积和的因式分解**：`∑_{x0..x3} f0 x0 · f1 x1 · c · f2 x2 · f3 x3
= (∑ f0)(∑ f1)·c·(∑ f2)(∑ f3)`。 -/
theorem sum_four_mul (f0 f1 f2 f3 : Fin 4 → ℝ) (c : ℝ) :
    (∑ x0 : Fin 4, ∑ x1 : Fin 4, ∑ x2 : Fin 4, ∑ x3 : Fin 4,
        f0 x0 * f1 x1 * c * f2 x2 * f3 x3)
      = (∑ x0, f0 x0) * (∑ x1, f1 x1) * c * (∑ x2, f2 x2) * (∑ x3, f3 x3) := by
  have hrev : (∑ x0 : Fin 4, ∑ x1 : Fin 4, ∑ x2 : Fin 4, ∑ x3 : Fin 4,
        f0 x0 * f1 x1 * c * f2 x2 * f3 x3)
      = (∑ x3, f3 x3) * (∑ x2, f2 x2) * c * (∑ x1, f1 x1) * (∑ x0, f0 x0) := by
    simp only [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun x0 _ => ?_)
    refine Finset.sum_congr rfl (fun x1 _ => ?_)
    refine Finset.sum_congr rfl (fun x2 _ => ?_)
    refine Finset.sum_congr rfl (fun x3 _ => ?_)
    ring
  rw [hrev]
  ring

/-- ★★ **固定 `a`、`b` 时位点模式的和**：`∑_σ ∏ kernel(·) = kernel (t 2) a b`。

（四个叶位置各自独立，四个行和都为 `1`（`kernel_sum_row`），只剩内部边那一项。） -/
theorem sum_pattern_by_ab (t : Fin 5 → ℝ) (a b : Fin 4) :
    (∑ σ : Fin 4 → Fin 4, kernel (t 0) a (σ 0) * kernel (t 1) a (σ 1)
        * kernel (t 2) a b * kernel (t 3) b (σ 2) * kernel (t 4) b (σ 3))
      = kernel (t 2) a b := by
  have hsum := Fintype.sum_equiv patternEquiv
    (fun σ : Fin 4 → Fin 4 => kernel (t 0) a (σ 0) * kernel (t 1) a (σ 1)
        * kernel (t 2) a b * kernel (t 3) b (σ 2) * kernel (t 4) b (σ 3))
    (fun p : Fin 4 × Fin 4 × Fin 4 × Fin 4 =>
        kernel (t 0) a p.1 * kernel (t 1) a p.2.1 * kernel (t 2) a b
          * kernel (t 3) b p.2.2.1 * kernel (t 4) b p.2.2.2)
    (fun _ => rfl)
  rw [hsum]
  simp only [Fintype.sum_prod_type]
  rw [sum_four_mul (fun x => kernel (t 0) a x) (fun x => kernel (t 1) a x)
    (fun x => kernel (t 3) b x) (fun x => kernel (t 4) b x) (kernel (t 2) a b),
    kernel_sum_row, kernel_sum_row, kernel_sum_row, kernel_sum_row]
  ring

/-- 三层求和换序：`∑_σ ∑_a ∑_b = ∑_a ∑_b ∑_σ`。 -/
theorem sum_comm_pattern_ab (F : (Fin 4 → Fin 4) → Fin 4 → Fin 4 → ℝ) :
    (∑ σ : Fin 4 → Fin 4, ∑ a : Fin 4, ∑ b : Fin 4, F σ a b)
      = ∑ a : Fin 4, ∑ b : Fin 4, ∑ σ : Fin 4 → Fin 4, F σ a b := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.sum_comm]

/-- ★★★ **`patternProb` 是一条概率分布**：`∑_σ patternProb t σ = 1`。

**不需要任何假设** —— `kernel_sum_row`（行和 = `1`）对**任意** `t` 都成立。
这是 §4「有界性」的枢纽：有了它，`geneScore` 的界就是 `∑_σ |wJCR| · p_σ ≤ ∑_σ p_σ = 1`。 -/
theorem sum_patternProb (t : Fin 5 → ℝ) :
    ∑ σ : Fin 4 → Fin 4, patternProb t σ = 1 := by
  calc ∑ σ : Fin 4 → Fin 4, patternProb t σ
      = (1 / 4) * ∑ σ : Fin 4 → Fin 4, ∑ a : Fin 4, ∑ b : Fin 4,
          kernel (t 0) a (σ 0) * kernel (t 1) a (σ 1) * kernel (t 2) a b
            * kernel (t 3) b (σ 2) * kernel (t 4) b (σ 3) :=
        (Finset.mul_sum Finset.univ (fun σ : Fin 4 → Fin 4 => ∑ a : Fin 4, ∑ b : Fin 4,
          kernel (t 0) a (σ 0) * kernel (t 1) a (σ 1) * kernel (t 2) a b
            * kernel (t 3) b (σ 2) * kernel (t 4) b (σ 3)) (1 / 4)).symm
    _ = (1 / 4) * ∑ a : Fin 4, ∑ b : Fin 4, ∑ σ : Fin 4 → Fin 4,
          kernel (t 0) a (σ 0) * kernel (t 1) a (σ 1) * kernel (t 2) a b
            * kernel (t 3) b (σ 2) * kernel (t 4) b (σ 3) := by
        rw [sum_comm_pattern_ab]
    _ = (1 / 4) * ∑ a : Fin 4, ∑ b : Fin 4, kernel (t 2) a b := by
        rw [show (∑ a : Fin 4, ∑ b : Fin 4, ∑ σ : Fin 4 → Fin 4,
              kernel (t 0) a (σ 0) * kernel (t 1) a (σ 1) * kernel (t 2) a b
                * kernel (t 3) b (σ 2) * kernel (t 4) b (σ 3))
            = ∑ a : Fin 4, ∑ b : Fin 4, kernel (t 2) a b from
          Finset.sum_congr rfl (fun a _ =>
            Finset.sum_congr rfl (fun b _ => sum_pattern_by_ab t a b))]
    _ = 1 := by
        have h2 : (∑ a : Fin 4, ∑ b : Fin 4, kernel (t 2) a b) = 4 := by
          rw [show (∑ a : Fin 4, ∑ b : Fin 4, kernel (t 2) a b)
              = ∑ _a : Fin 4, (1 : ℝ) from
            Finset.sum_congr rfl (fun a _ => kernel_sum_row (t 2) a)]
          simp
        rw [h2]
        norm_num

/-- ★★ `patternProb` 非负（**需枝长非负**；见文件头 §3 的 ★D 说明）。 -/
theorem patternProb_nonneg (t : Fin 5 → ℝ) (ht : ∀ i, 0 ≤ t i) (σ : Fin 4 → Fin 4) :
    0 ≤ patternProb t σ := by
  simp only [patternProb]
  refine mul_nonneg (by norm_num) ?_
  refine Finset.sum_nonneg (fun a _ => Finset.sum_nonneg (fun b _ => ?_))
  exact mul_nonneg (mul_nonneg (mul_nonneg
    (mul_nonneg (Phylo.JC.kernel_nonneg (ht 0) a (σ 0))
      (Phylo.JC.kernel_nonneg (ht 1) a (σ 1)))
    (Phylo.JC.kernel_nonneg (ht 2) a b))
    (Phylo.JC.kernel_nonneg (ht 3) b (σ 2)))
    (Phylo.JC.kernel_nonneg (ht 4) b (σ 3))

/-- ★★ `patternProb` 是概率 ⇒ 单点不超过 `1`。 -/
theorem patternProb_le_one (t : Fin 5 → ℝ) (ht : ∀ i, 0 ≤ t i) (σ : Fin 4 → Fin 4) :
    patternProb t σ ≤ 1 := by
  have hle := Finset.single_le_sum
    (s := (Finset.univ : Finset (Fin 4 → Fin 4)))
    (f := fun σ' : Fin 4 → Fin 4 => patternProb t σ')
    (fun σ' _ => patternProb_nonneg t ht σ') (Finset.mem_univ σ)
  rwa [sum_patternProb t] at hle

/-- ★★ **B3（`patternProb` 版）**：`|patternProb t σ| ≤ 1`（枝长非负）。 -/
theorem abs_patternProb_le_one (t : Fin 5 → ℝ) (ht : ∀ i, 0 ≤ t i) (σ : Fin 4 → Fin 4) :
    |patternProb t σ| ≤ 1 := by
  rw [abs_of_nonneg (patternProb_nonneg t ht σ)]
  exact patternProb_le_one t ht σ

/-! ## 4. `wJCR` 与 `geneScore` 的有界性 -/

/-- ★★ JC69 逐模式权重**绝对值 ≤ 1**（`+1` / `-1/2` / `0` 三种取值，逐情形）。 -/
theorem abs_wJCR_le_one (T : Topo) (σ : Fin 4 → Fin 4) : |wJCR T σ| ≤ 1 := by
  cases hv : wJC T σ
  · rw [wJCR, hv, Val.toReal_pos]; norm_num
  · rw [wJCR, hv, Val.toReal_negHalf]; norm_num
  · rw [wJCR, hv, Val.toReal_zero]; norm_num

/-- ★★★ **B3（主件）：位点权重函数一致有界** —— `|geneScore S l lx T| ≤ 1`。

**界是显式的 `B = 1`**，比「`∑_σ |wJCR| · (1/4) = 9`」这类粗糙估计好一个数量级：
用的是 `∑_σ patternProb = 1`（本文件 `sum_patternProb`）而不是逐项 `≤ 1/4`。

前提 `∀ i, 0 ≤ l i`、`0 ≤ lx` 是**必需的**（负枝长时 `patternProb` 无界，见文件头 §3）。 -/
theorem abs_geneScore_le_one (S T : Topo) (l : Fin 4 → ℝ) (lx : ℝ)
    (hl : ∀ i, 0 ≤ l i) (hlx : 0 ≤ lx) :
    |geneScore S l lx T| ≤ 1 := by
  have hcanon : ∀ i : Fin 5, 0 ≤ canonLen S l lx i := by
    intro i
    fin_cases i
    · simpa [canonLen] using hl (perm S 0)
    · simpa [canonLen] using hl (perm S 1)
    · simpa [canonLen] using hlx
    · simpa [canonLen] using hl (perm S 2)
    · simpa [canonLen] using hl (perm S 3)
  have hnn : ∀ σ : Fin 4 → Fin 4,
      0 ≤ patternProb (canonLen S l lx) (fun i => σ (perm S i)) :=
    fun σ => patternProb_nonneg _ hcanon _
  calc |geneScore S l lx T|
      = |∑ σ : Fin 4 → Fin 4, wJCR T σ
            * patternProb (canonLen S l lx) (fun i => σ (perm S i))| := by
        simp only [geneScore]
    _ ≤ ∑ σ : Fin 4 → Fin 4, |wJCR T σ
            * patternProb (canonLen S l lx) (fun i => σ (perm S i))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ σ : Fin 4 → Fin 4, |wJCR T σ|
            * patternProb (canonLen S l lx) (fun i => σ (perm S i)) := by
        refine Finset.sum_congr rfl (fun σ _ => ?_)
        rw [abs_mul, abs_of_nonneg (hnn σ)]
    _ ≤ ∑ σ : Fin 4 → Fin 4, 1
            * patternProb (canonLen S l lx) (fun i => σ (perm S i)) := by
        refine Finset.sum_le_sum (fun σ _ => ?_)
        exact mul_le_mul_of_nonneg_right (abs_wJCR_le_one T σ) (hnn σ)
    _ = 1 := by
        have hre : (∑ σ : Fin 4 → Fin 4,
              patternProb (canonLen S l lx) (fun i => σ (perm S i)))
            = ∑ σ : Fin 4 → Fin 4, patternProb (canonLen S l lx) σ :=
          sum_comp_perm (perm S) _
        rw [show (∑ σ : Fin 4 → Fin 4, 1
              * patternProb (canonLen S l lx) (fun i => σ (perm S i)))
            = ∑ σ : Fin 4 → Fin 4,
                patternProb (canonLen S l lx) (fun i => σ (perm S i)) from
          Finset.sum_congr rfl (fun σ _ => one_mul _), hre]
        exact sum_patternProb (canonLen S l lx)

/-! ## 5. ★ B2 ＋ B3 的打包（含反空洞见证） -/

/-- ★★ **「位点权重可测且有界」的打包**（缺口 B2 ＋ B3 的接口形式）。

这是**新增的 `structure … : Prop`**；反空洞见证见 `isMeasurableBoundedWeight_one`
（显式实例，不是空真）。 -/
structure IsMeasurableBoundedWeight (S : Topo) (T : Topo) (B : ℝ) : Prop where
  /-- 可测性（缺口 B2）。 -/
  measurable : Measurable (fun p : (Fin 4 → ℝ) × ℝ => geneScore S p.1 p.2 T)
  /-- 一致有界性（缺口 B3）。 -/
  bound : ∀ (l : Fin 4 → ℝ) (lx : ℝ), (∀ i, 0 ≤ l i) → 0 ≤ lx →
    |geneScore S l lx T| ≤ B

/-- ★★ **反空洞见证**：`B = 1` 的显式实例（每个 `S`、`T` 都被 inhabit）。

⚠️ 这条**不是**空真的：`bound` 字段是关于**所有**非负枝长的全称断言，由
`abs_geneScore_le_one` 逐点给出。 -/
theorem isMeasurableBoundedWeight_one (S T : Topo) : IsMeasurableBoundedWeight S T 1 where
  measurable := measurable_geneScore S T
  bound := fun l lx hl hlx => abs_geneScore_le_one S T l lx hl hlx

/-! ## 6. 可测 ＋ 有界 ⇒ 可积（概率测度） -/

/-- ★★★ **收口引理**：**概率（有限）测度**上，`a.e.` 有界的 `a.e.` 强可测函数可积。

`Integrable.of_bound` 要求 `‖f x‖ ≤ C`；这里换成更好用的 `|f x| ≤ C`（`ℝ` 上二者同值）。 -/
theorem integrable_of_abs_bound {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] {f : α → ℝ} (hf : AEStronglyMeasurable f μ) {C : ℝ}
    (hC : ∀ᵐ x ∂μ, |f x| ≤ C) : Integrable f μ := by
  refine Integrable.of_bound hf C ?_
  filter_upwards [hC] with x hx
  rwa [Real.norm_eq_abs]

/-! ## 7. `MSCSamplingAE` 的 `hint`：从 `SiteTable` ＋ 可测性**推出** -/

/-- ★★ `SiteTable`（非负 ＋ 和为 `1`）⇒ 单个指示值落在 `[0, 1]`。 -/
theorem siteTable_ind_le_one {X : Type*} [Fintype X] [DecidableEq X] {Ω₀ : Type*}
    [MeasurableSpace Ω₀] {ind : SiteFun X Ω₀} (h : SiteTable ind) (x : Ω₀)
    (S : Finset X) (hS : S.card = 4) (q : Split ↥S) :
    |ind x S hS q| ≤ 1 := by
  have hle : ind x S hS q ≤ 1 := by
    have hsingle := Finset.single_le_sum
      (s := (Finset.univ : Finset (Split ↥S)))
      (f := fun q' : Split ↥S => ind x S hS q')
      (fun q' _ => h.nonneg x S hS q') (Finset.mem_univ q)
    rwa [h.sum_one x S hS] at hsingle
  rw [abs_of_nonneg (h.nonneg x S hS q)]
  exact hle

/-- ★★★ **`hint` 的 `SiteFun` 版被消解**：`SiteTable` ＋ `ind` 的**可测性** ＋ 概率测度
⇒ 既有 `hint` 形状 `Integrable (fun ω : ℕ → Ω₀ => ind (ω 0) S hS q) μ` **不再是假设**。 -/
theorem integrable_siteFun_of_siteTable {X : Type*} [Fintype X] [DecidableEq X]
    {Ω₀ : Type*} [MeasurableSpace Ω₀] (ind : SiteFun X Ω₀) (h : SiteTable ind)
    (hmeas : ∀ (S : Finset X) (hS : S.card = 4) (q : Split ↥S),
      Measurable (fun x : Ω₀ => ind x S hS q))
    (μ : Measure (ℕ → Ω₀)) [IsProbabilityMeasure μ]
    (S : Finset X) (hS : S.card = 4) (q : Split ↥S) :
    Integrable (fun ω : ℕ → Ω₀ => ind (ω 0) S hS q) μ := by
  refine integrable_of_abs_bound ?_ (C := 1) ?_
  · exact ((hmeas S hS q).comp (measurable_pi_apply 0)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun ω => siteTable_ind_le_one h (ω 0) S hS q

universe u v

/-- ★★★ **`astral_statisticallyConsistent_ae` 的「无 `hint`」变体**：

与 `Phylo.Stat.MSCSamplingAE.astral_statisticallyConsistent_ae` 结论**逐字相同**，
参数表里**删掉了 `hint`**，换成对 `ind` 的**可测性**假设
（由 `integrable_siteFun_of_siteTable` 把它按需重建）。

⚠️ `hindep` / `hident` / `hmean` **仍是假设** —— 它们是「位点 iid 且分布 = MSC 理论分布」，
属规格 §6 的缺口 B1（真测度层），**不在 W13a（B2＋B3）的范围**。 -/
theorem astral_statisticallyConsistent_ae_of_measurable {X : Type u} [Fintype X] [DecidableEq X]
    {Ω₀ : Type*} [MeasurableSpace Ω₀] (ind : SiteFun X Ω₀) (h : SiteTable ind)
    (hmeas : ∀ (S : Finset X) (hS : S.card = 4) (q : Split ↥S),
      Measurable (fun x : Ω₀ => ind x S hS q))
    (m : MSCFreq.{u, v} X) (μ : Measure (ℕ → Ω₀)) [IsProbabilityMeasure μ]
    (hindep : ∀ (S : Finset X) (hS : S.card = 4) (q : Split ↥S),
      iIndepFun (fun i (ω : ℕ → Ω₀) => ind (ω i) S hS q) μ)
    (hident : ∀ (S : Finset X) (hS : S.card = 4) (q : Split ↥S), ∀ i,
      IdentDistrib (fun ω : ℕ → Ω₀ => ind (ω i) S hS q)
        (fun ω : ℕ → Ω₀ => ind (ω 0) S hS q) μ μ)
    (hmean : ∀ (S : Finset X) (hS : S.card = 4) (q : Split ↥S),
      ∫ ω, ind (ω 0) S hS q ∂μ = m.freq.p S hS q)
    {E : QuartetFreq X → QuartetTree.{u, v} X} (hE : ∀ D, IsASTRAL D (E D))
    (hNE : ∃ q : QuartetChoice X, ¬ IsTrueChoice m q) :
    ∀ᵐ ω ∂μ, ∃ N : ℕ, ∀ n ≥ N, IsTrueChoice m (E (empTable ind h m n ω)).q :=
  MSCSamplingAE.astral_statisticallyConsistent_ae ind h m μ
    (fun S hS q => integrable_siteFun_of_siteTable ind h hmeas μ S hS q)
    hindep hident hmean hE hNE

/-! ## 8. CASTER 侧 `hint`（`∑ T' τd · A` 形状）：从可测性与界推出 -/

/-- ★★★ **`hint` 的 CASTER 版被消解**：若

* `τ : α → Topo → ℝ` 逐拓扑可测，且 `a.e.` 非负、`∑_T' τ x T' = 1`（如 `MSCTopoSym.τd`）；
* `A : α → Topo → ℝ` 逐拓扑可测，且 `a.e.` `|A x T'| ≤ 1`（如 `geneScore`，用 `abs_geneScore_le_one`）；
* `μ` 是概率测度，

则既有 `hint` 形状 `Integrable (fun x => ∑ T', τ x T' * A x T') μ` **不再是假设**。

**界取 `C = 1`**（不是 `3B`）：因为 `∑_T' τ x T' = 1`，`|∑ τ A| ≤ ∑ τ |A| ≤ ∑ τ · 1 = 1`。 -/
theorem integrable_weightSum_of_measurable {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] (τ : α → Topo → ℝ) (A : α → Topo → ℝ)
    (hτm : ∀ T' : Topo, Measurable (fun x => τ x T'))
    (hAm : ∀ T' : Topo, Measurable (fun x => A x T'))
    (hτ0 : ∀ᵐ x ∂μ, ∀ T' : Topo, 0 ≤ τ x T')
    (hτ1 : ∀ᵐ x ∂μ, ∑ T' : Topo, τ x T' = 1)
    (hA : ∀ᵐ x ∂μ, ∀ T' : Topo, |A x T'| ≤ 1) :
    Integrable (fun x => ∑ T' : Topo, τ x T' * A x T') μ := by
  refine integrable_of_abs_bound ?_ (C := 1) ?_
  · refine Measurable.aestronglyMeasurable ?_
    exact Finset.measurable_sum _ (fun T' _ => (hτm T').mul (hAm T'))
  · filter_upwards [hτ0, hτ1, hA] with x h0 h1 hb
    calc |∑ T' : Topo, τ x T' * A x T'|
        ≤ ∑ T' : Topo, |τ x T' * A x T'| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ T' : Topo, τ x T' * |A x T'| := by
          refine Finset.sum_congr rfl (fun T' _ => ?_)
          rw [abs_mul, abs_of_nonneg (h0 T')]
      _ ≤ ∑ T' : Topo, τ x T' * 1 := by
          exact Finset.sum_le_sum fun T' _ => mul_le_mul_of_nonneg_left (hb T') (h0 T')
      _ = 1 := by
          rw [show (∑ T' : Topo, τ x T' * 1) = ∑ T' : Topo, τ x T' from
            Finset.sum_congr rfl (fun T' _ => mul_one _)]
          exact h1

/-- ★★★ **CASTER 侧 `hint` 的 `geneScore` 实例**：把上一条的 `A` 取成
`fun x T' => geneScore T' (φ x).1 (φ x).2 T`（即 JC69 的 `P.A`），
可测性用 `measurable_geneScore`、界用 `abs_geneScore_le_one`。

（`φ` 是「枝长随参数变化」的可测读取，例如 `KingmanΘ` 上 `φ θ = (θ.1.1, θ.1.2)`
—— 物种树侧的四条叶长与内部枝长。`hlen` 就是「枝长非负」，是 B3 的**必需**前提，见文件头 §3。） -/
theorem integrable_geneScore_weightSum {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] (τ : α → Topo → ℝ) (φ : α → (Fin 4 → ℝ) × ℝ) (T : Topo)
    (hτm : ∀ T' : Topo, Measurable (fun x => τ x T'))
    (hφ : Measurable φ)
    (hτ0 : ∀ᵐ x ∂μ, ∀ T' : Topo, 0 ≤ τ x T')
    (hτ1 : ∀ᵐ x ∂μ, ∑ T' : Topo, τ x T' = 1)
    (hlen : ∀ᵐ x ∂μ, (∀ i, 0 ≤ (φ x).1 i) ∧ 0 ≤ (φ x).2) :
    Integrable (fun x => ∑ T' : Topo, τ x T' * geneScore T' (φ x).1 (φ x).2 T) μ := by
  have hm : ∀ T' : Topo, Measurable (fun x => geneScore T' (φ x).1 (φ x).2 T) :=
    fun T' => (measurable_geneScore T' T).comp hφ
  have hb : ∀ᵐ x ∂μ, ∀ T' : Topo, |geneScore T' (φ x).1 (φ x).2 T| ≤ 1 := by
    filter_upwards [hlen] with x hx
    exact fun T' => abs_geneScore_le_one T' T (φ x).1 (φ x).2 hx.1 hx.2
  exact integrable_weightSum_of_measurable τ (fun x T' => geneScore T' (φ x).1 (φ x).2 T)
    hτm hm hτ0 hτ1 hb

/-! ## 9. 落到既有端到端形状：Kingman 测度上的 `hint` 被推出

`Phylo/Stat/MSCKingmanMeasure.lean` §6 的旗舰端点
`jc69_caster_statisticallyConsistent_kingman_measure_derived` 的假设表里**只剩 `hint` 与 `hconv`**。
本节把其中的 **`hint` 也推掉**（`hconv` 是大数定律，不属本子批 B2／B3）：

| 用到的事实 | 本文件中的出处 |
|---|---|
| `jc69PropADataK.A θ T' T = geneScore T' (θ.1).1 (θ.1).2 T`（**定义相等**） | `jc69PropADataK_A_eq` |
| `θ ↦ kingmanMSCTopoSym.τd θ T` 可测 | `measurable_kingmanτd` |
| `τd` 非负、`∑_T' τd θ T' = 1`（逐点） | 既有 `MSCTopoSym.τd_nonneg` / `τd_sum` |
| `ν`-`a.e.` 枝长非负 | `ae_len_nonneg_kingman_dirac`（`kingmanMSCMeasure_dirac_eq_map` ＋ `ae_map_iff`） |
| `\|geneScore\| ≤ 1` | §4 `abs_geneScore_le_one` |

⇒ `kingman_jc69_hint`：**既有 `hint` 形状**的 `Integrable` 陈述，
新增假设只有「物种树叶长非负」`hleaf`（内部枝长 `a + b ≥ 0` 由 `ℝ≥0` 自动）。 -/

/-- ★★ JC69 的 `P.A` 与 `geneScore` **定义相等**（`jc69PropAData` 的 `A` 就是 `geneScore`，
`jc69PropADataK` 只是沿 `Prod.fst` 前推）。这条把本文件的有界性/可测性
**逐字**接到 `MSCInstance.jc69PropADataK` 上。 -/
theorem jc69PropADataK_A_eq (θ : KingmanΘ) (T' T : Topo) :
    jc69PropADataK.A θ T' T = geneScore T' (θ.1).1 (θ.1).2 T := rfl

/-- ★★ **`Kingmanτd` 逐拓扑可测**（它是两个 `Bool` 分量上的条件分支）。 -/
theorem measurable_kingmanτd (T : Topo) :
    Measurable (fun θ : KingmanΘ => kingmanMSCTopoSym.τd θ T) := by
  have hd : MeasurableSet {θ : KingmanΘ | KingmanDeep θ} := by
    show MeasurableSet ({θ : KingmanΘ | θ.2.1 = true} ∩ {θ : KingmanΘ | θ.2.2 = true})
    exact MeasurableSet.inter
      ((measurable_fst.comp measurable_snd) (measurableSet_singleton true))
      ((measurable_snd.comp measurable_snd) (measurableSet_singleton true))
  have h : (fun θ : KingmanΘ => kingmanMSCTopoSym.τd θ T)
      = fun θ => if KingmanDeep θ then 1 / 3 else (if T = Topo.ab_cd then 1 else 0) := rfl
  rw [h]
  exact Measurable.ite hd measurable_const measurable_const

/-- ★★ **`kingmanMSCMeasure (Measure.dirac (leaf, a, b))` 上枝长 `a.e.` 非负**：
像点的叶长恒为 `leaf`、内部枝长恒为 `a + b`。 -/
theorem ae_len_nonneg_kingman_dirac (leaf : Fin 4 → ℝ) (hleaf : ∀ i, 0 ≤ leaf i)
    (a b : ℝ≥0) :
    ∀ᵐ θ ∂(kingmanMSCMeasure (Measure.dirac (leaf, a, b))),
      (∀ i, 0 ≤ (θ.1).1 i) ∧ 0 ≤ (θ.1).2 := by
  have hg : Measurable (fun v : ℝ × ℝ => toKingmanΘ ((leaf, a, b), v)) :=
    measurable_toKingmanΘ.comp (measurable_const.prodMk measurable_id)
  have h11 : Measurable (fun θ : KingmanΘ => (θ.1).1) := measurable_fst.fst
  have hset : MeasurableSet {θ : KingmanΘ | (∀ i, 0 ≤ (θ.1).1 i) ∧ 0 ≤ (θ.1).2} := by
    have h1 : MeasurableSet (⋂ i, {θ : KingmanΘ | (0 : ℝ) ≤ (θ.1).1 i}) :=
      MeasurableSet.iInter fun i =>
        measurableSet_le (f := fun _ : KingmanΘ => (0 : ℝ))
          (g := fun θ : KingmanΘ => (θ.1).1 i) measurable_const ((measurable_pi_apply i).comp h11)
    have h2 : MeasurableSet {θ : KingmanΘ | (0 : ℝ) ≤ (θ.1).2} :=
      measurableSet_le (f := fun _ : KingmanΘ => (0 : ℝ))
        (g := fun θ : KingmanΘ => (θ.1).2) measurable_const measurable_fst.snd
    have hEq : (⋂ i, {θ : KingmanΘ | (0 : ℝ) ≤ (θ.1).1 i}) ∩ {θ : KingmanΘ | (0 : ℝ) ≤ (θ.1).2}
        = {θ : KingmanΘ | (∀ i, 0 ≤ (θ.1).1 i) ∧ 0 ≤ (θ.1).2} := by
      ext θ
      simp
    rw [← hEq]
    exact h1.inter h2
  rw [Phylo.Stat.MSCKingmanMeasure.kingmanMSCMeasure_dirac_eq_map (leaf, a, b),
    ae_map_iff hg.aemeasurable hset]
  refine Filter.Eventually.of_forall (fun v => ?_)
  have h1 : (toKingmanΘ ((leaf, a, b), v)).1.1 = leaf := rfl
  have h2 : (toKingmanΘ ((leaf, a, b), v)).1.2 = (a : ℝ) + (b : ℝ) := rfl
  simp only [h1, h2]
  exact ⟨hleaf, add_nonneg a.2 b.2⟩

/-- ★★★ **既有 `hint` 形状在 Kingman 测度上被推出**（HANDOVER 第 117–119 行那条待办的
**端到端形态**）：

```
hint : ∀ T : Topo, Integrable (fun θ => ∑ T' : Topo, S.τd θ T' * P.A θ T' T) ν
```

取 `S = kingmanMSCTopoSym`、`P = jc69PropADataK`、`ν = kingmanMSCMeasure (Measure.dirac (leaf, a, b))`
时，上式的 `Integrable` **不再是假设**：本定理只用 §1–§4 的可测性与有界性把它**推出来**。

**假设面只剩**：`hleaf : ∀ i, 0 ≤ leaf i`（物种树四条叶长非负 —— 规格 §1.2 的
`r ∈ [r⁻, r⁺] ⊂ (0, ∞)` 与 `L ∈ [1, C]` 正是这类正性/有界条件；
内部枝长 `a + b ≥ 0` 由 `ℝ≥0` 自动）。 -/
theorem kingman_jc69_hint (leaf : Fin 4 → ℝ) (hleaf : ∀ i, 0 ≤ leaf i) (a b : ℝ≥0)
    (T : Topo) :
    Integrable (fun θ : KingmanΘ =>
        ∑ T' : Topo, kingmanMSCTopoSym.τd θ T' * jc69PropADataK.A θ T' T)
      (kingmanMSCMeasure (Measure.dirac (leaf, a, b))) := by
  have hτ0 : ∀ᵐ θ ∂(kingmanMSCMeasure (Measure.dirac (leaf, a, b))),
      ∀ T' : Topo, 0 ≤ kingmanMSCTopoSym.τd θ T' :=
    Filter.Eventually.of_forall fun θ T' => kingmanMSCTopoSym.τd_nonneg θ T'
  have hτ1 : ∀ᵐ θ ∂(kingmanMSCMeasure (Measure.dirac (leaf, a, b))),
      ∑ T' : Topo, kingmanMSCTopoSym.τd θ T' = 1 :=
    Filter.Eventually.of_forall fun θ => kingmanMSCTopoSym.τd_sum θ
  have hmain := integrable_geneScore_weightSum
    (fun θ T' => kingmanMSCTopoSym.τd θ T') (fun θ : KingmanΘ => θ.1) T
    (fun T' => measurable_kingmanτd T') measurable_fst hτ0 hτ1
    (ae_len_nonneg_kingman_dirac leaf hleaf a b)
  simpa only [jc69PropADataK_A_eq] using hmain

end Phylo.Stat.SiteWeightMeasurable
