/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.Algorithm.RF
import Phylo.Quartet
import Mathlib.Tactic

/-!
# `Phylo.Stat.TreeMetricDistribution` —— W11h / X8 + Q2-①：树比较度量的精确分布

文献行号一律指 `references/md/…` 里 Markdown 文件的**行号**。

* **Steel & Penny 1993**，*Distributions of Tree Comparison Metrics—Some New Results*，
  *Syst. Biol.* 42(2):126–141（`SteelPenny1993_DistributionsTreeComparisonMetrics.md`）：

  | 行 | 内容 |
  |---|---|
  | 285–286 | `the partition metric and the quartet metric are examples of symmetric difference metrics` —— 两个度量**共用一个对称差骨架** |
  | 288–295 | Eq.(4)：`d_p(T₁,T₂) = i(T₁) + i(T₂) − 2 v_p(T₁,T₂)` |
  | 313–316 | `i = n − 3`（二元树）；partition metric 的**直径** `= 2n − 6` |
  | 325–331 | **对任意 label-invariant 分布 D**：`μ_D(d_p) = 2[μ_D(i) − μ_D(v_p)]` |
  | 77–81 | quartet metric 的归一化因子取**quartet 总数** `C(n,4)`；归一化取值 `< 1` |
  | 431–435 | Figure 5：`n = 4…10` 的 `min shared` 与 `max d_q`（`n = 4`：`0` 与 `1`） |
  | 456–458 | 两棵**不同** n 叶树的 `d_q` 最小值 `= n − 3` |
  | 486–490 | Eq.(11)：label-invariant binary 分布下 `μ_D(d_q)/C(n,4) = 2/3` |
  | 355–410 | Theorem 1 + Corollary：`v_p` **渐近 Poisson**（本文件落缺口） |

* **Alon, Naves & Sudakov 2016**，*On the maximum quartet distance between phylogenetic trees*：
  第 124–131 行 `qd = C(n,4) − #(两棵树都相容的 quartet)`；第 341–345 行 Prop 2.2
  （随机重标号下期望满足数 `= |Q|/3`）；第 347–353 行 Prop 2.3（`E[qd] = (2/3)·C(n,4)`）；
  第 137–141 行 Bandelt–Dress 上界 `(14/15)·C(n,4)`；第 199 行 Theorem 1.1（`0.69 + o(1)`）。
* **Estabrook, McMorris & Meacham 1985**（`EstabrookMcMorrisMeacham1985_QuartetMetricTrees.md`
  第 44–57 行 Abstract）：quartet 度量**定义来源**（4 元子集继承的子树）。

## 本文件内容

1. **§1** 两个度量的基数骨架：RF 版 / quartet 版的 Eq.(4)、`≤ |A| + |B|`、
   `|A| = |B| = m ⟹ d ≤ 2m`（取 `m = n − 3` 即第 316 行的直径 `2n − 6`），
   以及「两个度量在同一个叶集上**是同一个函数**」。
2. **§2** 「按**同一判据**筛出的子族」的距离不增（+ 反例：只靠「子集 ⟹ 不增」是**错的**）。
3. **§3** 有限树空间上的**精确**分布：有序对总和、均值（**第 325–331 行**，且对**任意**分布成立
   —— 比文献的 label-invariant 假设**更强**）、方差、完整分布表与其**质量守恒**。
4. **§4** 最小具体例子 **n = 4**（3 棵 binary 树）端到端算完：分布 `{0:3, 2:6}`、
   `μ(i) = 1`、`μ(v_p) = 1/3`、`μ(d_p) = 4/3 = 2(1 − 1/3)`、方差 `8/9`。
5. **§5** Q2-①：quartet 侧的基数上界与 `n = 4` 的最大 quartet 距离，以及三个
   `def … : Prop` **缺口**（Poisson 渐近、一般 `n` 的 `E[d_q] = (2/3)C(n,4)`、最大 quartet 距离）。

## 命名空间与 import（协调说明）

* 本文件所有**新**声明都放在**独立命名空间 `Phylo.MetricDist`** 里 —— 与
  `Phylo/TreeDistance.lean` 的 `Phylo.TreeDist` 同款做法：`Phylo/Distance.lean`、
  `Phylo/Algorithm/RF.lean` 由**其他 agent 并行**开发，独立命名空间使同名不可能撞车。
  收口时若要把它们并回 `Split` / 根命名空间，删掉本 namespace 即可。
* import 只有两个库内模块（两个度量的定义与已有度量性质）＋ `Mathlib.Tactic`：
  §3 的期望/方差是**有理数精确值**，需要 `norm_num` / `field_simp` / `ring`；
  由此顺带可用 `ℚ` 与 `∑` 记号。**没有**引入任何分析 / 测度 import。
-/

namespace Phylo

namespace MetricDist

open Finset

/-! ## §1 两个度量共用同一个对称差骨架 -/

/-- **RF 距离的 Eq.(4) 形式**：`d_p = |S| + |S'| − 2·|S ∩ S'|`。

文献：Steel & Penny 1993 **第 293 行** Eq.(4)（`d_p(T₁,T₂) = i(T₁) + i(T₂) − 2 v_p(T₁,T₂)`）：
`i(T) = S.card`（二元树 `i = n − 3`，第 152–160、313–316 行），
`v_p(T₁,T₂) = (S ∩ S').card`（共享 split 数，第 296–298 行）。

骨架恒等式是 `Phylo/Distance.lean` 的 `symmDiffCard_eq_card_add_sub_two_inter`。 -/
theorem rfDistance_eq_card_add_sub_two_inter {α : Type*} [Fintype α] [DecidableEq α]
    (S S' : Finset (Split α)) :
    Split.rfDistance S S' = S.card + S'.card - 2 * (S ∩ S').card :=
  symmDiffCard_eq_card_add_sub_two_inter S S'

/-- RF 距离不超过两个 split 系统的大小之和。 -/
theorem rfDistance_le_card_add {α : Type*} [Fintype α] [DecidableEq α]
    (S S' : Finset (Split α)) : Split.rfDistance S S' ≤ S.card + S'.card :=
  symmDiffCard_le_card_add S S'

/-- ★ **直径上界 `2n − 6`**：若两个 split 系统各有 `m` 个元素，则 `d_p ≤ 2m`；
取 `m = n − 3`（二元树的内部边数，第 313–316 行）得 **Steel & Penny 1993 第 316 行**的
「partition metric 直径 `= 2n − 6`」。 -/
theorem rfDistance_le_two_mul {α : Type*} [Fintype α] [DecidableEq α]
    {S S' : Finset (Split α)} {m : ℕ} (hS : S.card = m) (hS' : S'.card = m) :
    Split.rfDistance S S' ≤ 2 * m := by
  have h := rfDistance_le_card_add S S'
  omega

/-- **quartet 距离的 Eq.(4) 形式**（同一个基数恒等式，第 285–286 行
「both … are examples of symmetric difference metrics」）。 -/
theorem quartetDistance_eq_card_add_sub_two_inter {X : Type*} [Fintype X] [DecidableEq X]
    {S : Finset X} (Q Q' : Finset (Split ↥S)) :
    quartetDistance Q Q' = Q.card + Q'.card - 2 * (Q ∩ Q').card :=
  symmDiffCard_eq_card_add_sub_two_inter Q Q'

/-- quartet 距离不超过两个 quartet 系统的大小之和。 -/
theorem quartetDistance_le_card_add {X : Type*} [Fintype X] [DecidableEq X]
    {S : Finset X} (Q Q' : Finset (Split ↥S)) :
    quartetDistance Q Q' ≤ Q.card + Q'.card :=
  symmDiffCard_le_card_add Q Q'

/-- ★★ **Q2-① 的基数上界**：`|Q| = |Q'| = m ⟹ d_q ≤ 2m`。

取 `m = C(n,4)`（Steel & Penny 1993 **第 77–81 行**：quartet 度量的自然归一化因子是
**quartet 总数**，故归一化后取值总 `< 1`）即 「`d_q ≤ 2·C(n,4)`」。 -/
theorem quartetDistance_le_two_mul {X : Type*} [Fintype X] [DecidableEq X]
    {S : Finset X} {Q Q' : Finset (Split ↥S)} {m : ℕ} (hQ : Q.card = m) (hQ' : Q'.card = m) :
    quartetDistance Q Q' ≤ 2 * m := by
  have h := quartetDistance_le_card_add Q Q'
  omega

/-- ★★★ **Q2-①：两个度量在同一个叶集 `↥S` 上就是同一个函数**。

把支撑集 `↥S` 本身当成叶集，则 `Split.rfDistance`（基数版 RF）与 `quartetDistance`
都是 `symmDiffCard`，故**相等**（`rfl`）。文献依据是 Steel & Penny 1993 **第 285–286 行**：
partition metric 与 quartet metric **都是对称差度量**（RF 定义见第 288–289 行、
quartet 定义见第 441–448 行）。

⚠️ **诚实边界**：这条等式是**骨架层面**的，它**不**说明「真实树上 quartet 距离 ≤ RF 距离」——
后者是**假的**，见 §2 的反例与 `scripts/msc/tree_metric_distribution.py` 的穷举
（`n = 6`：两棵树的 `d_q = 14`，而 RF 直径只有 `2n − 6 = 6`）。 -/
theorem quartetDistance_eq_rfDistance {X : Type*} [Fintype X] [DecidableEq X]
    {S : Finset X} (Q Q' : Finset (Split ↥S)) :
    quartetDistance Q Q' = Split.rfDistance Q Q' := rfl

/-- ★ **`n = 4` 的最大 quartet 距离**（单 quartet 版）：两个**不同** resolution 的距离恰为 `2`
（未归一化），即 Steel & Penny 归一化后的 `d_q = 1` —— 这正是他们 Figure 5 表里
`n = 4` 一行的 `min shared = 0`、`max{d_q} = 1`（**第 431–435 行**）。 -/
theorem quartetDistance_singleton_of_ne {X : Type*} [Fintype X] [DecidableEq X]
    {S : Finset X} {q q' : Split ↥S} (h : q ≠ q') :
    quartetDistance ({q} : Finset (Split ↥S)) {q'} = 2 := by
  have hcard0 : (({q} : Finset (Split ↥S)) ∩ {q'}).card = 0 := by
    rw [Finset.card_eq_zero]
    ext x
    simp only [Finset.mem_inter, Finset.mem_singleton, Finset.notMem_empty, iff_false, not_and]
    exact fun h1 h2 => h (h1.symm.trans h2)
  rw [quartetDistance_eq_card_add_sub_two_inter, hcard0]
  simp

/-- ★ **`n = 4`：每个 quartet 系统的基数 `≤ 1`（每棵树只给一个 resolution）时 `d_q ≤ 2`。 -/
theorem quartetDistance_le_two_of_card_le_one {X : Type*} [Fintype X] [DecidableEq X]
    {S : Finset X} {Q Q' : Finset (Split ↥S)} (hQ : Q.card ≤ 1) (hQ' : Q'.card ≤ 1) :
    quartetDistance Q Q' ≤ 2 := by
  have h := quartetDistance_le_card_add Q Q'
  omega

/-! ## §2 按**同一判据**筛出的子族：距离不增（以及「只靠子集」为何是错的）

Q2-① 要的「quartet 距离与 RF 距离的不等式」在图书馆的骨架层面只能是**基数比较**：
两者都是 `symmDiffCard`，因此「把两个系统按**同一个判据** `p` 筛小」不会让距离变大。
⚠️ 反过来，「`Q ⊆ S`、`Q' ⊆ S'` ⟹ `d_q ≤ d_p`」是**错的** —— 见 `symmDiffCard_not_monotone`。 -/

/-- ★★★ **同一个判据下的子族距离不增**（Q2-① 的「只差基数比较」那一步）。

`(S.filter p) △ (S'.filter p) ⊆ S △ S'`，故两个度量的距离在所有「同一判据筛出的子族」上
都被**原系统的 RF 距离**控制。 -/
theorem symmDiffCard_filter_le {β : Type*} [DecidableEq β] (p : β → Prop) [DecidablePred p]
    (S S' : Finset β) :
    symmDiffCard (S.filter p) (S'.filter p) ≤ symmDiffCard S S' := by
  rw [symmDiffCard_def, symmDiffCard_def]
  refine Finset.card_le_card ?_
  intro x hx
  simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_filter] at hx ⊢
  tauto

/-- ★★ **Q2-① 的结构性不等式**：`S.filter p` 与 `S'.filter p` 的 quartet 距离
（在 `↥S` 这一叶集上是 `quartetDistance`，见 `quartetDistance_eq_rfDistance`）
不超过 `S`、`S'` 的 **RF 距离**。 -/
theorem quartetDistance_le_rfDistance_of_filter {α : Type*} [Fintype α] [DecidableEq α]
    (p : Split α → Prop) [DecidablePred p] (S S' : Finset (Split α)) :
    symmDiffCard (S.filter p) (S'.filter p) ≤ Split.rfDistance S S' :=
  symmDiffCard_filter_le p S S'

/-- ★B **反例检查（必读）**：`A ⊆ C`、`B ⊆ D` **推不出** `symmDiffCard A B ≤ symmDiffCard C D`。
取 `A = {0}`、`B = {1}`、`C = {0,1}`、`D = {1}`：`|A △ B| = 2 > 1 = |C △ D|`。

⇒ 所以 Q2-① 的「quartet 距离 ≤ RF 距离」**不能**用「quartet 集 ⊆ split 集」一句话带过；
真正可证的是**同一判据**版本（`symmDiffCard_filter_le`）。真实树上该不等式更是**假的**
（脚本穷举：`n = 6` 时 `max qd = 14 > max RF = 6`）。 -/
theorem symmDiffCard_not_monotone :
    ∃ A B C D : Finset (Fin 3),
      A ⊆ C ∧ B ⊆ D ∧ symmDiffCard C D < symmDiffCard A B :=
  ⟨{0}, {1}, {0, 1}, {1}, by decide, by decide, by decide⟩

/-! ## §3 有限树空间上的**精确**分布（X8）

「有限树空间」= 一族 split 系统 `𝒯 : Finset (Finset (Split α))`（每棵树 ↦ 它的非平凡 split 集）；
**均匀分布** = 每个成员等概率。下面所有量都是**精确**整数/有理数，无 Monte Carlo。 -/

/-- 有序对的 RF 距离**总和**（均匀分布下期望的分子）。 -/
def rfDistSum {α : Type*} [Fintype α] [DecidableEq α]
    (𝒯 : Finset (Finset (Split α))) : ℕ :=
  ∑ S ∈ 𝒯, ∑ S' ∈ 𝒯, Split.rfDistance S S'

/-- 每棵树内部边数的总和（`μ(i)` 的分子）。 -/
def rfSizeSum {α : Type*} [Fintype α] [DecidableEq α]
    (𝒯 : Finset (Finset (Split α))) : ℕ :=
  ∑ S ∈ 𝒯, S.card

/-- 有序对**共享 split 数**的总和（`μ(v_p)` 的分子）。 -/
def rfSharedSum {α : Type*} [Fintype α] [DecidableEq α]
    (𝒯 : Finset (Finset (Split α))) : ℕ :=
  ∑ S ∈ 𝒯, ∑ S' ∈ 𝒯, (S ∩ S').card

/-- ★ **RF 距离的**完整分布表**：距离恰为 `k` 的**有序对数**。 -/
def rfMultiplicity {α : Type*} [Fintype α] [DecidableEq α]
    (𝒯 : Finset (Finset (Split α))) (k : ℕ) : ℕ :=
  ((𝒯.product 𝒯).filter (fun p => Split.rfDistance p.1 p.2 = k)).card

/-- 有序对的 RF 距离**平方和**（方差的分子）。 -/
def rfDistSqSum {α : Type*} [Fintype α] [DecidableEq α]
    (𝒯 : Finset (Finset (Split α))) : ℕ :=
  ∑ S ∈ 𝒯, ∑ S' ∈ 𝒯, (Split.rfDistance S S') ^ 2

/-- **每对的 Eq.(4)**：无减法形式 `d_p + 2|S ∩ S'| = |S| + |S'|`。 -/
theorem rfDistance_add_inter_card {α : Type*} [Fintype α] [DecidableEq α]
    (S S' : Finset (Split α)) :
    Split.rfDistance S S' + 2 * (S ∩ S').card = S.card + S'.card := by
  have h := rfDistance_eq_card_add_sub_two_inter S S'
  have h1 : (S ∩ S').card ≤ S.card := Finset.card_le_card Finset.inter_subset_left
  have h2 : (S ∩ S').card ≤ S'.card := Finset.card_le_card Finset.inter_subset_right
  omega

/-- ★★★ **X8 主定理：均值公式**（Steel & Penny 1993 **第 325–331 行**）
`μ_D(d_p) = 2[μ_D(i) − μ_D(v_p)]` 的**有限精确形式**：

`|𝒯|² · μ(d_p) = 2·|𝒯|·Σ_S |S| − 2·Σ_{S,S'} |S ∩ S'|`。

文献把这条归给「任意 **label-invariant** 分布 D」；这里**不需要任何分布假设**
（Eq.(4) 是逐对恒等式 + 求和的线性性），即本定理**比文献的陈述更强**：
**RF 距离的均值与底层树分布无关**。

（用 `ℤ` 写以免 `ℕ` 截断：两边都是精确整数。） -/
theorem rfMean_eq_int {α : Type*} [Fintype α] [DecidableEq α]
    (𝒯 : Finset (Finset (Split α))) :
    (rfDistSum 𝒯 : ℤ) = 2 * (𝒯.card : ℤ) * (rfSizeSum 𝒯 : ℤ) - 2 * (rfSharedSum 𝒯 : ℤ) := by
  have hterm : ∀ S ∈ 𝒯, ∀ S' ∈ 𝒯,
      ((Split.rfDistance S S' : ℤ)) = (S.card : ℤ) + (S'.card : ℤ) - 2 * ((S ∩ S').card : ℤ) := by
    intro S _ S' _
    have h := rfDistance_add_inter_card S S'
    have h' : ((Split.rfDistance S S' : ℤ)) + 2 * ((S ∩ S').card : ℤ)
        = (S.card : ℤ) + (S'.card : ℤ) := by
      exact_mod_cast h
    linarith
  have hinner : ∀ S ∈ 𝒯,
      (∑ S' ∈ 𝒯, ((S.card : ℤ) + (S'.card : ℤ) - 2 * ((S ∩ S').card : ℤ)))
        = (𝒯.card : ℤ) * (S.card : ℤ) + (∑ S' ∈ 𝒯, (S'.card : ℤ))
          - 2 * (∑ S' ∈ 𝒯, ((S ∩ S').card : ℤ)) := by
    intro S _
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const, ← Finset.mul_sum]
    simp only [nsmul_eq_mul]
  have houter :
      (∑ S ∈ 𝒯, ((𝒯.card : ℤ) * (S.card : ℤ) + (∑ S' ∈ 𝒯, (S'.card : ℤ))
          - 2 * (∑ S' ∈ 𝒯, ((S ∩ S').card : ℤ))))
        = 2 * (𝒯.card : ℤ) * (∑ S ∈ 𝒯, (S.card : ℤ))
          - 2 * (∑ S ∈ 𝒯, ∑ S' ∈ 𝒯, ((S ∩ S').card : ℤ)) := by
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
      ← Finset.mul_sum]
    simp only [nsmul_eq_mul]
    ring
  unfold rfDistSum rfSizeSum rfSharedSum
  push_cast
  calc (∑ S ∈ 𝒯, ∑ S' ∈ 𝒯, ((Split.rfDistance S S' : ℤ)))
      = ∑ S ∈ 𝒯, ∑ S' ∈ 𝒯, ((S.card : ℤ) + (S'.card : ℤ) - 2 * ((S ∩ S').card : ℤ)) :=
        Finset.sum_congr rfl fun S hS => Finset.sum_congr rfl fun S' hS' => hterm S hS S' hS'
    _ = ∑ S ∈ 𝒯, ((𝒯.card : ℤ) * (S.card : ℤ) + (∑ S' ∈ 𝒯, (S'.card : ℤ))
          - 2 * (∑ S' ∈ 𝒯, ((S ∩ S').card : ℤ))) :=
        Finset.sum_congr rfl fun S hS => hinner S hS
    _ = 2 * (𝒯.card : ℤ) * (∑ S ∈ 𝒯, (S.card : ℤ))
          - 2 * (∑ S ∈ 𝒯, ∑ S' ∈ 𝒯, ((S ∩ S').card : ℤ)) := houter

/-- 均匀分布下 RF 距离的**期望**（精确有理数）。
`𝒯.card = 0` 时按 Lean 的 `0 / 0 = 0` 约定为 `0`（所有用到它的定理都带 `𝒯.card ≠ 0`）。 -/
noncomputable def rfMean {α : Type*} [Fintype α] [DecidableEq α]
    (𝒯 : Finset (Finset (Split α))) : ℚ :=
  (rfDistSum 𝒯 : ℚ) / (𝒯.card : ℚ) ^ 2

/-- `μ(i)`：每棵树内部边数（split 数）的期望。 -/
noncomputable def rfSizeMean {α : Type*} [Fintype α] [DecidableEq α]
    (𝒯 : Finset (Finset (Split α))) : ℚ :=
  (rfSizeSum 𝒯 : ℚ) / (𝒯.card : ℚ)

/-- `μ(v_p)`：一对树共享 split 数的期望。 -/
noncomputable def rfSharedMean {α : Type*} [Fintype α] [DecidableEq α]
    (𝒯 : Finset (Finset (Split α))) : ℚ :=
  (rfSharedSum 𝒯 : ℚ) / (𝒯.card : ℚ) ^ 2

/-- 均匀分布下 RF 距离的**方差**（精确有理数，教科书式 `E[d²] − (E d)²`）。 -/
noncomputable def rfVar {α : Type*} [Fintype α] [DecidableEq α]
    (𝒯 : Finset (Finset (Split α))) : ℚ :=
  (rfDistSqSum 𝒯 : ℚ) / (𝒯.card : ℚ) ^ 2 - rfMean 𝒯 ^ 2

/-- 方差的**整数分子**：`Var = rfVarNum / |𝒯|⁴`（见 `rfVar_eq`）。 -/
def rfVarNum {α : Type*} [Fintype α] [DecidableEq α]
    (𝒯 : Finset (Finset (Split α))) : ℤ :=
  (𝒯.card : ℤ) ^ 2 * (rfDistSqSum 𝒯 : ℤ) - (rfDistSum 𝒯 : ℤ) ^ 2

/-- ★★ **`rfMean_eq_int` 的有理数形式**：`μ(d_p) = 2[μ(i) − μ(v_p)]`
（Steel & Penny 1993 第 325–331 行）。 -/
theorem rfMean_eq {α : Type*} [Fintype α] [DecidableEq α]
    (𝒯 : Finset (Finset (Split α))) (h : 𝒯.card ≠ 0) :
    rfMean 𝒯 = 2 * (rfSizeMean 𝒯 - rfSharedMean 𝒯) := by
  have hcard : (𝒯.card : ℚ) ≠ 0 := by exact_mod_cast h
  have hint := rfMean_eq_int 𝒯
  have hq : (rfDistSum 𝒯 : ℚ)
      = 2 * (𝒯.card : ℚ) * (rfSizeSum 𝒯 : ℚ) - 2 * (rfSharedSum 𝒯 : ℚ) := by
    have h' : ((rfDistSum 𝒯 : ℤ) : ℚ)
        = ((2 * (𝒯.card : ℤ) * (rfSizeSum 𝒯 : ℤ) - 2 * (rfSharedSum 𝒯 : ℤ) : ℤ) : ℚ) := by
      rw [hint]
    push_cast at h'
    exact h'
  rw [rfMean, rfSizeMean, rfSharedMean, hq]
  field_simp

/-- ★★ **方差的精确表达**：`Var = rfVarNum / |𝒯|⁴`（整数分子 / `|𝒯|⁴`）。 -/
theorem rfVar_eq {α : Type*} [Fintype α] [DecidableEq α]
    (𝒯 : Finset (Finset (Split α))) (h : 𝒯.card ≠ 0) :
    rfVar 𝒯 = (rfVarNum 𝒯 : ℚ) / (𝒯.card : ℚ) ^ 4 := by
  have hcard : (𝒯.card : ℚ) ≠ 0 := by exact_mod_cast h
  rw [rfVar, rfMean, rfVarNum]
  push_cast
  field_simp

/-- ★ **分布表的**质量守恒**：若所有距离 `≤ K`，则各重数之和 `= |𝒯|²`
（`k` 从 `0` 到 `K` 的**完整**分布表）。 -/
theorem rfMultiplicity_sum {α : Type*} [Fintype α] [DecidableEq α]
    (𝒯 : Finset (Finset (Split α))) {K : ℕ}
    (h : ∀ S ∈ 𝒯, ∀ S' ∈ 𝒯, Split.rfDistance S S' ≤ K) :
    ∑ k ∈ Finset.range (K + 1), rfMultiplicity 𝒯 k = 𝒯.card * 𝒯.card := by
  have hmaps : Set.MapsTo (fun p : Finset (Split α) × Finset (Split α) =>
      Split.rfDistance p.1 p.2) (↑(𝒯.product 𝒯)) (↑(Finset.range (K + 1))) := by
    intro p hp
    have hp' : p ∈ 𝒯.product 𝒯 := hp
    have hp'' := Finset.mem_product.mp hp'
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (h p.1 hp''.1 p.2 hp''.2))
  have hcard := Finset.card_eq_sum_card_fiberwise (s := 𝒯.product 𝒯)
    (f := fun p : Finset (Split α) × Finset (Split α) => Split.rfDistance p.1 p.2)
    (t := Finset.range (K + 1)) hmaps
  have hprod : (𝒯.product 𝒯).card = 𝒯.card * 𝒯.card := Finset.card_product 𝒯 𝒯
  rw [hprod] at hcard
  simpa only [rfMultiplicity] using hcard.symm

/-! ## §4 最小具体例子：`n = 4`（3 棵 binary 树）★C

`Fin 4` 上的三条 2|2 split —— 即 4 叶二元树的 3 个可能的内部边。
规范化：`sideA` 取**含最小叶 `0`** 的那一侧（与 `scripts/msc/tree_metric_distribution.py` 一致）。
每棵 4 叶二元树恰有 1 条内部边，故它的 split 系统是单元素集，`trees4` 就是**全体 3 棵树**。 -/

/-- `{0,1} | {2,3}`。 -/
def q01 : Split (Fin 4) where
  parts := fun i => if i = 0 then ({0, 1} : Finset (Fin 4)) else {2, 3}
  pairwise_disjoint := by decide
  union_eq_univ := by decide
  nonempty := by decide

/-- `{0,2} | {1,3}`。 -/
def q02 : Split (Fin 4) where
  parts := fun i => if i = 0 then ({0, 2} : Finset (Fin 4)) else {1, 3}
  pairwise_disjoint := by decide
  union_eq_univ := by decide
  nonempty := by decide

/-- `{0,3} | {1,2}`。 -/
def q03 : Split (Fin 4) where
  parts := fun i => if i = 0 then ({0, 3} : Finset (Fin 4)) else {1, 2}
  pairwise_disjoint := by decide
  union_eq_univ := by decide
  nonempty := by decide

/-- 第 1 棵树的 split 系统（单元素）。 -/
def t01 : Finset (Split (Fin 4)) := {q01}

/-- 第 2 棵树的 split 系统（单元素）。 -/
def t02 : Finset (Split (Fin 4)) := {q02}

/-- 第 3 棵树的 split 系统（单元素）。 -/
def t03 : Finset (Split (Fin 4)) := {q03}

/-- ★ **`n = 4` 的树空间**：3 棵 binary 树（均匀分布）。 -/
def trees4 : Finset (Finset (Split (Fin 4))) := {t01, t02, t03}

/-- `n = 4` 树空间有 3 个成员（`(2·4 − 5)!! = 3`）。 -/
theorem trees4_card : trees4.card = 3 := by decide

/-- 三条 split 两两不同（`3` 条 2|2 split 恰是 4 叶二元树的 3 个内部边）。 -/
theorem trees4_pairs_distinct : q01 ≠ q02 ∧ q01 ≠ q03 ∧ q02 ≠ q03 := by decide

/-- ★★★ **RF 距离的精确分布表（n = 4）**：`k ≤ 2` 时重数为 `{0 ↦ 3, 2 ↦ 6}`，其余为 `0`。 -/
theorem trees4_rf_profile (k : ℕ) (hk : k ≤ 2) :
    rfMultiplicity trees4 k = if k = 0 then 3 else if k = 2 then 6 else 0 := by
  interval_cases k <;> decide

/-- 分布表逐点值：`d_p = 0` 有 3 个有序对（对角线）。 -/
theorem trees4_rf_profile_zero : rfMultiplicity trees4 0 = 3 := by decide

/-- 分布表逐点值：`d_p = 1` 不可能（对称差基数是偶数）。 -/
theorem trees4_rf_profile_one : rfMultiplicity trees4 1 = 0 := by decide

/-- 分布表逐点值：`d_p = 2` 有 6 个有序对（非对角线）。 -/
theorem trees4_rf_profile_two : rfMultiplicity trees4 2 = 6 := by decide

/-- 有序对距离总和 `= 0·3 + 2·6 = 12`。 -/
theorem trees4_distSum : rfDistSum trees4 = 12 := by decide

/-- 有序对距离平方和 `= 0·3 + 4·6 = 24`。 -/
theorem trees4_distSqSum : rfDistSqSum trees4 = 24 := by decide

/-- 内部边数总和 `= 1 + 1 + 1 = 3`。 -/
theorem trees4_sizeSum : rfSizeSum trees4 = 3 := by decide

/-- 共享 split 数总和 `= 1 + 1 + 1 = 3`（对角线上每对共享自己的那条 split）。 -/
theorem trees4_sharedSum : rfSharedSum trees4 = 3 := by decide

/-- ★★★ **`n = 4` 的均值**：`μ(d_p) = 12/9 = 4/3`。 -/
theorem trees4_mean : rfMean trees4 = 4 / 3 := by
  rw [rfMean, trees4_distSum, trees4_card]
  norm_num

/-- ★★★ **`n = 4` 的方差**：`Var = 24/9 − (4/3)² = 8/9`。 -/
theorem trees4_var : rfVar trees4 = 8 / 9 := by
  rw [rfVar, rfMean, trees4_distSqSum, trees4_distSum, trees4_card]
  norm_num

/-- 方差的整数分子：`9·24 − 12² = 72 = 8/9 · 81`（`rfVar_eq` 的实例）。 -/
theorem trees4_varNum : rfVarNum trees4 = 72 := by
  rw [rfVarNum, trees4_distSqSum, trees4_distSum, trees4_card]
  norm_num

/-- `trees4` 的每个成员都是单元素 split 系统（供 `rfMultiplicity_sum` 的假设用）。 -/
theorem trees4_mem_card (S : Finset (Split (Fin 4))) (hS : S ∈ trees4) : S.card = 1 := by
  simp only [trees4, Finset.mem_insert, Finset.mem_singleton] at hS
  rcases hS with rfl | rfl | rfl <;> decide

/-- `trees4` 上任意一对的距离 `≤ 2`（直径）。 -/
theorem trees4_dist_le_two (S : Finset (Split (Fin 4))) (hS : S ∈ trees4)
    (S' : Finset (Split (Fin 4))) (hS' : S' ∈ trees4) :
    Split.rfDistance S S' ≤ 2 := by
  have h1 := trees4_mem_card S hS
  have h2 := trees4_mem_card S' hS'
  have h3 := rfDistance_le_card_add S S'
  omega

/-- ★★★ **分布表质量守恒（一般定理的 `n = 4` 实例）**：`3 + 0 + 6 = 9 = 3²`。 -/
theorem trees4_profile_sum :
    ∑ k ∈ Finset.range 3, rfMultiplicity trees4 k = 9 := by
  have h := rfMultiplicity_sum trees4 (K := 2)
    (fun S hS S' hS' => trees4_dist_le_two S hS S' hS')
  rw [trees4_card] at h
  exact h

/-- ★C **反空真 + 交叉检查 1**：具体穷举（`decide`）与一般质量守恒定理给出同一个 `9`。 -/
example : ∑ k ∈ Finset.range 3, rfMultiplicity trees4 k = 9 := by decide

/-- ★C **反空真 + 交叉检查 2**：一般均值公式 `rfMean_eq_int` 在 `n = 4` 上给出
`2·3·3 − 2·3 = 12`，与穷举总和 `trees4_distSum = 12` 一致。 -/
example : 2 * (trees4.card : ℤ) * (rfSizeSum trees4 : ℤ) - 2 * (rfSharedSum trees4 : ℤ)
    = (rfDistSum trees4 : ℤ) := (rfMean_eq_int trees4).symm

/-- ★C **交叉检查 3**：`μ(d_p) = 2[μ(i) − μ(v_p)]` 的 `n = 4` 实例
`2(1 − 1/3) = 4/3` —— 即 Steel & Penny 1993 第 325–331 行的公式在具体树集上复现。 -/
theorem trees4_mean_formula :
    rfMean trees4 = 2 * (rfSizeMean trees4 - rfSharedMean trees4) :=
  rfMean_eq trees4 (by rw [trees4_card]; norm_num)

/-- ★C **反空真**：`μ(i) = 1`（每棵 4 叶二元树恰有 1 条内部边）。 -/
theorem trees4_sizeMean : rfSizeMean trees4 = 1 := by
  rw [rfSizeMean, trees4_sizeSum, trees4_card]
  norm_num

/-- ★C **反空真**：`μ(v_p) = 1/3`（随机两棵树共享内部边的概率 `= 1/3`）。 -/
theorem trees4_sharedMean : rfSharedMean trees4 = 1 / 3 := by
  rw [rfSharedMean, trees4_sharedSum, trees4_card]
  norm_num

/-- ★C **交叉检查 4**：`4/3 = 2(1 − 1/3)`，逐项对账第 325–331 行的公式。 -/
theorem trees4_mean_by_components :
    rfMean trees4 = 2 * (rfSizeMean trees4 - rfSharedMean trees4)
      ∧ rfSizeMean trees4 = 1 ∧ rfSharedMean trees4 = 1 / 3
      ∧ rfMean trees4 = 4 / 3 ∧ rfVar trees4 = 8 / 9 :=
  ⟨trees4_mean_formula, trees4_sizeMean, trees4_sharedMean, trees4_mean, trees4_var⟩

/-! ## §4b Q2-① 的字面实例：`n = 4` 的 **quartet** 距离分布

§4 的 `trees4` 用的是 `Split (Fin 4)`（4 条叶的全集作为叶集）。
quartet 距离的 API（`quartetDistance`）要求**固定支撑集** `↥S`，故这里再给一份
**字面**的 `S := Finset.univ : Finset (Fin 4)` 版本：三个 resolution `r01`/`r02`/`r03`
（小侧分别 `{0,1}`、`{0,2}`、`{0,3}`，即三条 2|2 split）。

**`n = 4` 时两个度量数值完全相同**：每棵 4 叶二元树只有 1 条内部边，
它的 split 系统与它的 quartet 系统是同一个单元素集
（`quartetDistance_eq_rfDistance` 就是这条的骨架版）。 -/

/-- `↥univ` 上小侧为 `{0,1}` 的 resolution（即 `01|23`）。 -/
def r01 : Split ↥(Finset.univ : Finset (Fin 4)) where
  parts := fun i => if i = 0
    then Finset.univ.filter fun a : ↥(Finset.univ : Finset (Fin 4)) =>
      (a : Fin 4) ∈ ({0, 1} : Finset (Fin 4))
    else Finset.univ.filter fun a : ↥(Finset.univ : Finset (Fin 4)) =>
      (a : Fin 4) ∈ ({2, 3} : Finset (Fin 4))
  pairwise_disjoint := by decide
  union_eq_univ := by decide
  nonempty := by decide

/-- `↥univ` 上小侧为 `{0,2}` 的 resolution（即 `02|13`）。 -/
def r02 : Split ↥(Finset.univ : Finset (Fin 4)) where
  parts := fun i => if i = 0
    then Finset.univ.filter fun a : ↥(Finset.univ : Finset (Fin 4)) =>
      (a : Fin 4) ∈ ({0, 2} : Finset (Fin 4))
    else Finset.univ.filter fun a : ↥(Finset.univ : Finset (Fin 4)) =>
      (a : Fin 4) ∈ ({1, 3} : Finset (Fin 4))
  pairwise_disjoint := by decide
  union_eq_univ := by decide
  nonempty := by decide

/-- `↥univ` 上小侧为 `{0,3}` 的 resolution（即 `03|12`）。 -/
def r03 : Split ↥(Finset.univ : Finset (Fin 4)) where
  parts := fun i => if i = 0
    then Finset.univ.filter fun a : ↥(Finset.univ : Finset (Fin 4)) =>
      (a : Fin 4) ∈ ({0, 3} : Finset (Fin 4))
    else Finset.univ.filter fun a : ↥(Finset.univ : Finset (Fin 4)) =>
      (a : Fin 4) ∈ ({1, 2} : Finset (Fin 4))
  pairwise_disjoint := by decide
  union_eq_univ := by decide
  nonempty := by decide

/-- 三个 resolution 两两不同（4 叶二元树恰有 3 个拓扑）。 -/
theorem r01_ne_r02 : r01 ≠ r02 := by decide

/-- 第 1 个 quartet 系统（单元素）。 -/
def qt01 : Finset (Split ↥(Finset.univ : Finset (Fin 4))) := {r01}

/-- 第 2 个 quartet 系统（单元素）。 -/
def qt02 : Finset (Split ↥(Finset.univ : Finset (Fin 4))) := {r02}

/-- 第 3 个 quartet 系统（单元素）。 -/
def qt03 : Finset (Split ↥(Finset.univ : Finset (Fin 4))) := {r03}

/-- ★ **`n = 4` 的 quartet 空间**：3 个 resolution（均匀分布）。 -/
def qt4 : Finset (Finset (Split ↥(Finset.univ : Finset (Fin 4)))) := {qt01, qt02, qt03}

/-- `n = 4` 的 quartet 空间有 3 个成员。 -/
theorem qt4_card : qt4.card = 3 := by decide

/-- ★★★ **Q2-①：`n = 4` 时 quartet 距离的分布表与 RF 的完全一致**
（`rfMultiplicity` 内部用 `Split.rfDistance`，而它与 `quartetDistance` 是同一个函数）。 -/
theorem qt4_mult_eq_quartetMult (k : ℕ) :
    rfMultiplicity qt4 k
      = ((qt4.product qt4).filter fun p => quartetDistance p.1 p.2 = k).card := rfl

/-- ★★★ **Q2-①：`n = 4` 的 quartet 距离精确分布表**：`{0 ↦ 3, 2 ↦ 6}`。 -/
theorem qt4_profile (k : ℕ) (hk : k ≤ 2) :
    rfMultiplicity qt4 k = if k = 0 then 3 else if k = 2 then 6 else 0 := by
  interval_cases k <;> decide

/-- ★★ **`n = 4` 的最大 quartet 距离 `= 2`**（归一化后 `1`），
与 Steel & Penny 1993 第 431–435 行 Figure 5 的 `n = 4` 行一致。 -/
theorem qt4_max_distance : quartetDistance qt01 qt02 = 2 :=
  quartetDistance_singleton_of_ne r01_ne_r02

/-- `n = 4` 的 quartet 距离总和 `= 12`（`2 × 6`）。 -/
theorem qt4_distSum : rfDistSum qt4 = 12 := by decide

/-- ★★★ **Q2-①：`n = 4` 的归一化 quartet 均值 `= 2/3 = (2/3)·C(4,4)`** ——
Steel & Penny 1993 第 486–490 行 Eq.(11) 与 Alon–Naves–Sudakov 2016
第 347–353 行 Prop 2.3 在最小情形上的字面复现（`12/9 = 4/3`，除以 `2` 即 `2/3`）。 -/
theorem qt4_normalizedMean : rfMean qt4 / 2 = 2 / 3 := by
  rw [rfMean, qt4_distSum, qt4_card]
  norm_num

/-! ## §5 Q2-①：quartet 侧的分布对象与**缺口**

`QuartetRes X` 是「一棵树的 quartet 数据」的**有限模型**：给每个 4-子集指定一个**配对**。
用「小侧」（2 元子集）而不是 `Split` 表示配对，是为了**天然商掉 `Split.swap`**
（本库的 `Split` 是**有向**的：`A|B` 与 `B|A` 是不同的 `Split` 值，见 `Split.swap`）。

`quartetDistFull r r'` 是**未归一化**的 quartet 距离（Alon 等 2016 第 124–131 行的 `qd`）：
在每个 4-子集上「配对不同」就计 `2` —— 因此 `quartetDistFull / 2` 就是
Steel & Penny 第 441–448 行归一化后的 `d_q`。 -/

/-- 「resolution 表」：给**每个** 4-子集 `A` 指定一个小侧 `B`（`B.card = 2`，配对 = `{B, A∖B}`）。 -/
abbrev QuartetRes (X : Type*) [Fintype X] [DecidableEq X] :=
  (A : {A : Finset X // A.card = 4}) → {B : Finset ↥A.1 // B.card = 2}

/-- **未归一化 quartet 距离**：逐 4-子集比较配对（相同或互补算一致），不同则计 `2`。 -/
def quartetDistFull {X : Type*} [Fintype X] [DecidableEq X]
    (r r' : QuartetRes X) : ℕ :=
  ∑ _A : {A : Finset X // A.card = 4},
    if (r _A).1 = (r' _A).1 ∨ (r _A).1 = (r' _A).1ᶜ then 0 else 2

/-- ★ **反空真**：叶集不足 4 个时**没有** 4-子集，故 `C(n,4)` 的载体是空的
（下面缺口的结论在退化情形 `n ≤ 3` 上两边都是 `0`，不是「空真型的假命题」）。 -/
theorem card_fourSubsets_fin3 : (Fintype.card {A : Finset (Fin 3) // A.card = 4}) = 0 := by
  rw [Fintype.card_eq_zero_iff]
  exact ⟨fun A => by
    have h : A.1.card ≤ 3 := by
      simpa using Finset.card_le_univ A.1
    omega⟩

/-- **缺口 1**（Steel & Penny 1993 **第 355–410 行** Theorem 1 与第 393–404 行 Corollary）：
partition metric 的共享 split 数 `v_p` **渐近 Poisson**。

本库**没有**测度层、没有 iid 空间 / `Measure.infinitePi`，也没有把「`n` 叶树空间上的
均匀分布」抬成 `Measure`，故只把命题登记成 `Prop`：`P n k` 是「两棵 `n` 叶 binary 树
共享 `k` 个 split」的概率，若 `v_p` 的均值有极限 `lam`，则概率比收敛到 Poisson 比
`lam^k / k!`（用比值写以**避开** `exp`，从而不引入任何分析 import）。

⚠️ **诚实边界**：文献 Theorem 1(c) 还要求一个关于**近邻对数**标准差的技术条件
（第 336–352 行）；本库没有「近邻对数」这一层，该条件在此**写不出来**。
所以本 `Prop` 是**缺口的形状**（待补：`n` 叶树的 label-invariant 分布层 + 近邻对数统计量），
**不是**已验证的定理陈述。 -/
def rfPoissonAsymptotic_gap : Prop :=
  ∀ (P : ℕ → ℕ → ℚ) (lam : ℚ), 0 ≤ lam →
    (∀ n, (∑ k ∈ Finset.range (n + 1), P n k) = 1) →
    (∀ n k, 0 ≤ P n k) →
    (∀ eps : ℚ, 0 < eps → ∃ N : ℕ, ∀ n ≥ N,
      |(∑ k ∈ Finset.range (n + 1), (k : ℚ) * P n k) - lam| < eps) →
    ∀ eps : ℚ, 0 < eps → ∃ N : ℕ, ∀ n ≥ N, ∀ k ≤ n,
      |P n k / P n 0 - lam ^ k / (k.factorial : ℚ)| < eps

/-- **缺口 2**（Steel & Penny 1993 **第 486–490 行** Eq.(11)；Alon–Naves–Sudakov 2016
**第 341–353 行** Prop 2.2 + Prop 2.3）：
**label-invariant 分布下 quartet 距离的均值是分布无关的**，等于 `(2/3)·C(n,4)`。

这里是它的**有限精确形式**（不需要测度层）：若每个 4-子集的**每个**小侧 `B`
都在树族 `𝒯` 里出现**恰好 `k`** 次（这正是「随机重标号 ⇒ 每个 4-子集上的配对小侧
等可能」的组合内容，Alon 等第 341–345 行），则

`Σ_{r,r' ∈ 𝒯} quartetDistFull r r' = 48·k²·C(n,4)`，

等价地**归一化**均值 `= (2/3)·C(n,4)`（因为 `|𝒯| = 6k`，故
`48k²C(n,4) / (2·36k²) = (2/3)C(n,4)`）。

**未证**：需要一个「每个 4-子集恰有 6 个小侧、3 个互补类」的计数引理 + 交换求和。

**已由脚本穷举核对**（`scripts/msc/tree_metric_distribution.py` §★D，
**文献的原 setting**：固定一棵树 `T`，两棵树都取 `T` 的均匀随机重标号 `σ ∈ Sₙ`，
`𝒯 = {σ·T}`，`|𝒯| = n!`）：

| n | `n!` | `k = n!/6` | `Σ qdFull`（实测） | `48·k²·C(n,4)` |
|---|---|---|---|---|
| 4 | 24 | 4 | **768** | 768 |
| 5 | 120 | 20 | **96000** | 96000 |
| 6 | 720 | 120 | **10368000** | 10368000 |

且每个 4-子集的 6 个小侧在 `𝒯` 里**出现次数完全相同**（`= k`）—— 这正是
Alon 等第 341–345 行 Prop 2.2 的引擎（随机重标号下每个 4-子集的配对小侧等可能）。
`n = 4` 的**去重**版本（`𝒯` = 全部 6 张表、`k = 1`）给出 `48·1²·1 = 48`：
6 张表两两比较，一致 12 对、不同 24 对，`2·24 = 48`；
归一化后 `48/(2·36) = 2/3 = (2/3)·C(4,4)` ✓，与 `trees4`/`qt4` 的读法一致。 -/
def quartetMeanEquidistributed_gap : Prop :=
  ∀ (X : Type) [Fintype X] [DecidableEq X] (k : ℕ) (𝒯 : Finset (QuartetRes X)),
    (∀ (A : {A : Finset X // A.card = 4}) (B : {B : Finset ↥A.1 // B.card = 2}),
      (𝒯.filter fun r => (r A).1 = B.1).card = k) →
    (∑ r ∈ 𝒯, ∑ r' ∈ 𝒯, quartetDistFull r r')
      = 48 * k ^ 2 * Fintype.card {A : Finset X // A.card = 4}

/-- **缺口 3**（Bandelt & Dress 1986，如 Alon–Naves–Sudakov 2016 **第 137–141 行**所述；
改进见第 199 行 Theorem 1.1 `(0.69 + o(1))·C(n,4)`）：
**最大** quartet 距离 `≤ (14/15)·C(n,4)`。

一般 `n` 的**精确**最大值**至今未知**（第 252 行），本库也没有 `n` 叶树的枚举层；
这里按**有限精确形式**登记（两边乘 `15` 以免除法）：对任意两张 resolution 表 `r`、`r'`，

`15 · quartetDistFull r r' ≤ 28 · C(n,4)`

（系数 `28 = 2·14`：Alon 等的 `qd` 是「**不同** quartet 的个数」，
而 `quartetDistFull` 每个不同 quartet 计 `2`，故 `qd = quartetDistFull / 2`）。

⚠️ 文献原文写「**严格**小于 `(14/15)C(n,4)`」（第 137–141 行），但
`scripts/msc/tree_metric_distribution.py` 对 `n = 6` 的**完全穷举**（105 棵 binary 树）
给出 `max qd = 14 = (14/15)·C(6,4)` —— **取等**。故本 `Prop` 按 `≤` 登记
（与 Steel & Penny 第 431–435 行 Figure 5 的 `n = 6: min shared = 1` 一致）。 -/
def maxQuartetDistance_gap : Prop :=
  ∀ (X : Type) [Fintype X] [DecidableEq X] (r r' : QuartetRes X),
    15 * quartetDistFull r r' ≤ 28 * Fintype.card {A : Finset X // A.card = 4}

/-- **缺口 4**（Steel & Penny 1993 **第 456–458 行**）：两棵**不同** n 叶树的 `d_q` 最小值 `= n − 3`
（脚本对 `n = 4…7` 穷举核对通过；本库没有 `Cladogram` 的「n 叶 + binary」计数层，
故只登记为 `Prop`：对任意两张**不同**的表，`quartetDistFull ≥ 2(n − 3)`，
即归一化后 `≥ n − 3`）。 -/
def quartetMinDistance_gap : Prop :=
  ∀ (X : Type) [Fintype X] [DecidableEq X] (r r' : QuartetRes X), r ≠ r' →
    2 * (Fintype.card X - 3) ≤ quartetDistFull r r'

end MetricDist

end Phylo
