/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.Stat.MultiLocusASTRAL
import Phylo.Stat.MSCSamplingAE
import Phylo.Stat.QuartetDecides
import Phylo.Stat.Stability

/-!
# `Phylo.Stat.MultiLocusLaw` —— 「多标记平均 ⟹ 真频率」（缺口 **G1**）

## 1. 这条缺口是什么

`Phylo/Stat/MultiLocusASTRAL.lean:145` 的 ★★★ `multiLocus_maximizer_agrees`（与它下游
`Phylo/Stat/QuartetDecides.lean:357` 的 ★★★ `multiLocus_iso`）以

    (hM : M.avg = m.freq)

为**裸假设**：即「多标记平均频率**恰好**等于 MSC 理论频率」。这条等式**不可能**对随机数据
一般成立（有限平均不是极限），所以它此前只能当假设收下。**本文件把这条假设删掉**。

## 2. 本文件的路线（三步，每步都是定理）

1. **代数层（无概率）**：`MultiMarkerFreq.avg` 的定义本来就是「`L` 个基因座频率表的**有限平均**」
   （`MultiLocusASTRAL.lean:78`）。本文件把它与渐近层的「经验频率」显式对齐
   （`multiLocusData_avg_eq_empFreq`），并证明**平均的代数性质**：
   * `avg_p_sub_le` —— 平均与参考表的偏差**不超过**各基因座偏差的平均（三角不等式）；
   * `avg_FreqClose` —— **每个**基因座 `ε`-接近 ⇒ **平均**也 `ε`-接近；
   * `avg_p_eq_of_forall_eq` / `avg_eq_of_forall_eq` —— 所有基因座同表 ⇒ 平均表**就是**该表。
2. **稳定性层（无概率）**：★★★ `multiLocus_maximizer_agrees_close` —— 把 `M.avg = m.freq`
   **换成** `FreqClose M.avg m.freq (δ/(2N+1))`，结论**不变**。
   ⇒ 这是 `multiLocus_maximizer_agrees` 的**严格加强**（假设更弱：等式 ⇒ 任意 `ε`-接近），
   而旧定理成了它的**推论**（`multiLocus_maximizer_agrees_of_eq`）。
3. **概率层（SLLN，**几乎必然**）**：把每个基因座的表当作 iid 随机变量（`locus : Ω₀ → QuartetFreq X`），
   则 `L` 个基因座的平均表 **a.e.** 收敛到 `m.freq`
   （★★★ `multiLocus_avg_tendsto_ae_all` / `multiLocus_avg_eventually_close_ae`），
   于是多标记估计量 **a.e. 最终**逐 quartet 恢复真树
   （★★★ `multiLocus_statisticallyConsistent_ae` / `multiLocus_iso_ae`）。

   ⚠️ 「`L` 个基因座的平均」与「`n` 个位点的经验频率」是**同一个** `(·)⁻¹ * ∑ (·)`
   （`empFreq`，`Phylo/Stat/EmpiricalConvergence.lean:118`），故本层的 SLLN **不是新的**
   —— 它**完全复用** `Phylo.Stat.MSCSamplingAE`（W10e）的 `empFreq_tendsto_ae_all`
   与 `empFreq_eventually_close_ae_all`（后者本身就来自 `ProbabilityTheory.strong_law_ae`，
   Etemadi 版）。**本文件没有新增任何概率论器材。**

## 3. 交付（全部零 `sorry` / 零 `axiom` / 零 `native_decide`）

| 条目 | 状态 |
|---|---|
| `M.avg` 是 `L` 个基因座表的有限平均 | ✅ 既有定义（`MultiLocusASTRAL.lean:78`）＋ `multiLocusData_avg_eq_empFreq` |
| 平均的代数性质（三角不等式 / `ε`-接近 / 同表） | ✅ 本文件 |
| **裸假设 `M.avg = m.freq` 被删掉**（换成 `ε`-接近） | ✅ `multiLocus_maximizer_agrees_close` |
| 旧定理作为特例 | ✅ `multiLocus_maximizer_agrees_of_eq` |
| 平均表 a.e. 收敛到 `m.freq` | ✅ `multiLocus_avg_tendsto_ae_all` |
| 多标记估计量 a.e. 统计一致性（quartet 层 / 树层） | ✅ `multiLocus_statisticallyConsistent_ae` / `multiLocus_iso_ae` |
| `M.avg = m.freq` **作为定理**（理想样本） | ✅ `const_avg`（所有基因座同表 = `m.freq`）⇒ 假设**非空真** |
| iid **概率空间**的构造（Kolmogorov 扩张） | ❌ **仍未构造**（`EmpiricalConvergence.kolmogorov_extension_gap`）；与 W10d/W10e 一样把 iid 作为假设 |

## 4. 反例检查（★B）：「有限平均的 a.e. 极限一定是真频率吗？」

**不是。** 反例（本文件 `empFreq_const_locus`，脚本 `scripts/msc/w11f_g1_check.py` 精确复刻）：
取 `locus ≡ D`（**所有**基因座都给出同一张表 `D`），则平均表**恒等于** `D`，其 a.e. 极限是 `D`
—— 当 `D ≠ m.freq` 时**不是**真频率。故 SLLN 结论里的
`hmean : ∫ (locus (ω 0)).p S hS q = m.freq.p S hS q`（「基因座边缘分布 = MSC 理论频率」）
**不可省**：它是「真频率」这三个字的唯一来源。本文件把它写成**显式假设**（与 W10d/W10e 口径一致），
**没有**把它藏起来。

⚠️ 第二处检查（★B）：`hmean` 逐 `(S, hS, q)` 只约束**边缘期望**；而「每个基因座的表本身是一张频率表」
（非负 / 和为 1 / `swap` 不变）是 `QuartetFreq` 的**字段**，故**自动**成立 —— 这一点与 W10d 的
`SiteTable`（那里是**假设**）不同，是本层更干净的地方。
-/

universe u v

noncomputable section

open Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal

namespace Phylo.Stat.MultiLocusLaw

open Phylo.Stat.EmpiricalConvergence (empFreq)
open Phylo.Stat.MSCSamplingAE (empFreq_tendsto_ae_all empFreq_eventually_close_ae_all QuartetIndex)

variable {X : Type u} [Fintype X] [DecidableEq X]
variable {Ω₀ : Type*} [MeasurableSpace Ω₀]

/-! ## 1. 基因座层的随机模型与「平均表 = 有限平均」的对齐 -/

/-- **基因座表值随机变量**：`locus x` 是「随机结果 `x` 下该基因座给出的 quartet 频率表」。 -/
abbrev LocusTable (X : Type u) [Fintype X] [DecidableEq X] (Ω₀ : Type*) [MeasurableSpace Ω₀] :
    Type _ :=
  Ω₀ → QuartetFreq X

/-- 把「基因座表值随机变量」读成位点观测函数 `SiteFun`：
`ind x S hS q := (locus x).p S hS q`。（**定义**，不是假设。） -/
def locusSiteFun (locus : Ω₀ → QuartetFreq X) :
    Ω₀ → (S : Finset X) → (S.card = 4) → Split ↥S → ℝ :=
  fun x S hS q => (locus x).p S hS q

/-- ★ **多标记数据**（`L` 个基因座，第 `ℓ` 个贡献它自己的表 `locus (ω ℓ)`）。

于是 `(multiLocusData locus L hL ω).avg` **就是** `L` 个基因座频率表的**有限平均**
（`MultiMarkerFreq.avg` 的定义，`MultiLocusASTRAL.lean:78`）。 -/
def multiLocusData (locus : Ω₀ → QuartetFreq X) (L : ℕ) (hL : 0 < L) (ω : ℕ → Ω₀) :
    MultiMarkerFreq X where
  L := L
  Lpos := hL
  freq := fun ℓ => locus (ω ℓ)

omit [MeasurableSpace Ω₀] in
/-- **平均表的第 `(S,q)` 分量 = `L` 个基因座该分量的算术平均**（把 `Fin L` 求和换成 `range L`）。 -/
theorem multiLocusData_avg_p (locus : Ω₀ → QuartetFreq X) (L : ℕ) (hL : 0 < L)
    (ω : ℕ → Ω₀) (S : Finset X) (hS : S.card = 4) (q : Split ↥S) :
    (multiLocusData locus L hL ω).avg.p S hS q
      = (∑ ℓ ∈ Finset.range L, (locus (ω ℓ)).p S hS q) / L := by
  show (∑ m : Fin L, (locus (ω ↑m)).p S hS q) / (L : ℝ)
      = (∑ ℓ ∈ Finset.range L, (locus (ω ℓ)).p S hS q) / L
  rw [Fin.sum_univ_eq_sum_range (fun ℓ => (locus (ω ℓ)).p S hS q) L]

/-- ★★★ **对齐**：多标记**平均表**在 `(S,q)` 上的分量**就是** `L` 个基因座的经验频率
（`empFreq`，`Phylo/Stat/EmpiricalConvergence.lean:118`）。

⇒ 「跨基因座平均」与「跨位点经验频率」是**同一个**数学对象，故 G1 的 SLLN 只需复用 W10d/W10e。 -/
theorem multiLocusData_avg_eq_empFreq (locus : Ω₀ → QuartetFreq X) (L : ℕ) (hL : 0 < L)
    (ω : ℕ → Ω₀) (S : Finset X) (hS : S.card = 4) (q : Split ↥S) :
    (multiLocusData locus L hL ω).avg.p S hS q = empFreq (locusSiteFun locus) L ω S hS q := by
  rw [multiLocusData_avg_p, empFreq]
  simp only [locusSiteFun, div_eq_inv_mul]

/-! ## 2. 代数层：平均的三角不等式与「同表 ⇒ 平均表」 -/

/-- ★ **平均的三角不等式**：平均表与参考表 `D₀` 的偏差不超过各基因座偏差的**平均**。 -/
theorem avg_p_sub_le (M : MultiMarkerFreq X) (D₀ : QuartetFreq X)
    (S : Finset X) (hS : S.card = 4) (q : Split ↥S) :
    |M.avg.p S hS q - D₀.p S hS q|
      ≤ (∑ ℓ : Fin M.L, |(M.freq ℓ).p S hS q - D₀.p S hS q|) / M.L := by
  have hL : (0 : ℝ) < (M.L : ℝ) := Nat.cast_pos.mpr M.Lpos
  have h1 : M.avg.p S hS q - D₀.p S hS q
      = (∑ ℓ : Fin M.L, ((M.freq ℓ).p S hS q - D₀.p S hS q)) / M.L := by
    rw [MultiMarkerFreq.avg, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, sub_div, mul_div_cancel_left₀ _ (ne_of_gt hL)]
  rw [h1, abs_div, abs_of_pos hL]
  refine div_le_div_of_nonneg_right ?_ hL.le
  exact Finset.abs_sum_le_sum_abs _ _

/-- ★★ **平均 `ε`-接近**：若**每个**基因座都 `ε`-接近 `D₀`，则**平均表**也 `ε`-接近 `D₀`
（`L ≥ 1`）。

⇒ 这就是「多标记平均 ⟹ 真频率」在**有限样本**里的**确定性**一半：把逐基因座的收敛逐点平均，
**不需要**任何额外的概率论。 -/
theorem avg_FreqClose (M : MultiMarkerFreq X) {D₀ : QuartetFreq X} {ε : ℝ}
    (h : ∀ ℓ : Fin M.L, ∀ (S : Finset X) (hS : S.card = 4) (q : Split ↥S),
      |(M.freq ℓ).p S hS q - D₀.p S hS q| < ε) :
    FreqClose M.avg D₀ ε := by
  intro S hS q
  refine lt_of_le_of_lt (avg_p_sub_le M D₀ S hS q) ?_
  have hL : (0 : ℝ) < (M.L : ℝ) := Nat.cast_pos.mpr M.Lpos
  have hsum : (∑ ℓ : Fin M.L, |(M.freq ℓ).p S hS q - D₀.p S hS q|)
      < ∑ _ℓ : Fin M.L, ε :=
    Finset.sum_lt_sum (fun ℓ _ => (h ℓ S hS q).le)
      ⟨⟨0, M.Lpos⟩, Finset.mem_univ _, h _ S hS q⟩
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  rw [div_lt_iff₀ hL]
  linarith

/-- ★★ **所有基因座同表 ⇒ 平均表就是该表**（对 `p` 分量陈述）。 -/
theorem avg_p_eq_of_forall_eq (M : MultiMarkerFreq X) (D : QuartetFreq X)
    (h : ∀ ℓ : Fin M.L, M.freq ℓ = D)
    (S : Finset X) (hS : S.card = 4) (q : Split ↥S) :
    M.avg.p S hS q = D.p S hS q := by
  have hL : (M.L : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp M.Lpos)
  have h1 : M.avg.p S hS q = (∑ ℓ : Fin M.L, (M.freq ℓ).p S hS q) / M.L := rfl
  rw [h1, Finset.sum_congr rfl (fun ℓ _ => by rw [h ℓ]), Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_div_cancel_left₀ _ hL]

open Classical in
/-- ★★ **所有基因座同表 ⇒ 平均表 = 该表**（结构等式；三条 `Prop` 字段由证明无关性消去）。 -/
theorem avg_eq_of_forall_eq (M : MultiMarkerFreq X) (D : QuartetFreq X)
    (h : ∀ ℓ : Fin M.L, M.freq ℓ = D) : M.avg = D := by
  set A : QuartetFreq X := M.avg with hA
  have hpA : ∀ (S : Finset X) (hS : S.card = 4) (q : Split ↥S), A.p S hS q = D.p S hS q :=
    fun S hS q => by rw [hA]; exact avg_p_eq_of_forall_eq M D h S hS q
  obtain ⟨p₁, _n₁, _s₁, _w₁⟩ := A
  obtain ⟨p₂, _n₂, _s₂, _w₂⟩ := D
  have hp : p₁ = p₂ := funext fun S => funext fun hS => funext fun q => hpA S hS q
  subst hp
  rfl

/-- **理想（无限基因座）数据**：`L` 个基因座全部给出同一个表 `D`。 -/
def const (D : QuartetFreq X) (L : ℕ) (hL : 0 < L) : MultiMarkerFreq X where
  L := L
  Lpos := hL
  freq := fun _ => D

/-- ★★★ **`M.avg = m.freq` 是一条定理**（理想样本 `M = const m.freq L hL`）。

⇒ 这同时给出两件事：(i) 旧定理的裸假设 `M.avg = m.freq` **不是空真**（有居民）；
(ii) 在「基因座数无噪声」的理想情形下，那条假设**确实**成立。
真正的一般情形由 §4–§5 的 a.e. 版本覆盖。 -/
theorem const_avg (D : QuartetFreq X) (L : ℕ) (hL : 0 < L) : (const D L hL).avg = D :=
  avg_eq_of_forall_eq _ _ fun _ => rfl

omit [MeasurableSpace Ω₀] in
/-- ★★ **多标记数据的居民**（**反空真**）：只要有一条基因座随机变量，`MultiMarkerFreq` 就有居民。 -/
theorem multiLocusData_nonempty (locus : Ω₀ → QuartetFreq X) (L : ℕ) (hL : 0 < L)
    (ω : ℕ → Ω₀) : Nonempty (MultiMarkerFreq X) :=
  ⟨multiLocusData locus L hL ω⟩

/-! ## 3. ★★★ 删掉裸假设：`M.avg = m.freq` ⟶ `ε`-接近 -/

open Classical in
/-- ★★★ **（修正版）多标记得分最大化者逐 quartet 恢复真树** —— **不需要** `M.avg = m.freq`。

假设换成 `FreqClose M.avg m.freq (δ/(2N+1))`（`δ` 为 `exists_gap` 的 gap、`N = #(4-元集)`），
结论与 `MultiLocusASTRAL.multiLocus_maximizer_agrees` **逐字相同**。

**证明**：`multiLocus_isASTRAL`（多标记 argmax = 平均表上 ASTRAL 的 argmax）
＋ `Stability.stable_argmax`（扰动 `< δ/(2N+1)` 时 argmax 仍为真选择）。 -/
theorem multiLocus_maximizer_agrees_close (m : MSCFreq.{u, v} X) (M : MultiMarkerFreq X)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : ∀ q : QuartetChoice X, ¬ IsTrueChoice m q →
      astralScore m.freq q + δ ≤ astralScore m.freq m.q)
    {qt : QuartetTree.{u, v} X}
    (h : ∀ qt1 : QuartetTree.{u, v} X, multiLocusScore M qt1.q ≤ multiLocusScore M qt.q)
    (hclose : FreqClose M.avg m.freq
      (δ / (2 * (Fintype.card {S : Finset X // S.card = 4} : ℝ) + 1))) :
    IsTrueChoice m qt.q := by
  have h1 : IsASTRAL M.avg qt := (multiLocus_isASTRAL M).mp h
  exact stable_argmax m hδ hgap hclose (h1 m.toQuartetTree)

open Classical in
/-- ★★★ **旧定理是修正版的推论**：`M.avg = m.freq` ⟹ `ε`-接近（对任意 `ε > 0`）。

⇒ `MultiLocusASTRAL.multiLocus_maximizer_agrees` 的**裸假设被完全移除**：
它在修正版里只是一个**可选的**（且过强的）特例假设。 -/
theorem multiLocus_maximizer_agrees_of_eq (m : MSCFreq.{u, v} X) (M : MultiMarkerFreq X)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : ∀ q : QuartetChoice X, ¬ IsTrueChoice m q →
      astralScore m.freq q + δ ≤ astralScore m.freq m.q)
    (hM : M.avg = m.freq) {qt : QuartetTree.{u, v} X}
    (h : ∀ qt1 : QuartetTree.{u, v} X, multiLocusScore M qt1.q ≤ multiLocusScore M qt.q) :
    IsTrueChoice m qt.q := by
  have hfac : (0 : ℝ) < 2 * (Fintype.card {S : Finset X // S.card = 4} : ℝ) + 1 := by
    positivity
  refine multiLocus_maximizer_agrees_close m M hδ hgap h fun S hS q => ?_
  rw [hM, sub_self, abs_zero]
  exact div_pos hδ hfac

/-! ## 4. ★★★ 概率层：平均表 **几乎必然**收敛到 `m.freq`（SLLN）

模型（与 W10d/W10e **逐条同形**，只是把「一个位点」换成「一个基因座」）：

* `locus : Ω₀ → QuartetFreq X` —— 基因座的表值随机变量；
* `μ` —— 基因座序列 `ℕ → Ω₀` 上的概率测度；
* 四个假设 `hint` / `hindep` / `hident` / `hmean` —— iid 与「边缘分布 = MSC 理论频率」。

⚠️ **仍然是假设**（不是构造）：本版 Mathlib 无可数无限乘积测度
（`Phylo.Stat.EmpiricalConvergence.kolmogorov_extension_gap`）。 -/

/-- ★★★ **整张平均表的几乎必然收敛**：**同一个零测集之外**，对**所有** `(S, hS, q)`，
`L` 个基因座的平均频率收敛到 `m.freq.p S hS q`（**同一个 `ω`**）。

证明 = `Phylo.Stat.MSCSamplingAE.empFreq_tendsto_ae_all`（W10e，本身由 Etemadi 强大数定律
`ProbabilityTheory.strong_law_ae` 推出）作用在 `ind := locusSiteFun locus` 上。 -/
theorem multiLocus_avg_tendsto_ae_all (locus : Ω₀ → QuartetFreq X) (m : MSCFreq.{u, v} X)
    (μ : Measure (ℕ → Ω₀)) [IsProbabilityMeasure μ]
    (hint : ∀ (S : Finset X) (hS : S.card = 4) (q : Split ↥S),
      Integrable (fun ω : ℕ → Ω₀ => (locus (ω 0)).p S hS q) μ)
    (hindep : ∀ (S : Finset X) (hS : S.card = 4) (q : Split ↥S),
      iIndepFun (fun i (ω : ℕ → Ω₀) => (locus (ω i)).p S hS q) μ)
    (hident : ∀ (S : Finset X) (hS : S.card = 4) (q : Split ↥S), ∀ i,
      IdentDistrib (fun ω : ℕ → Ω₀ => (locus (ω i)).p S hS q)
        (fun ω : ℕ → Ω₀ => (locus (ω 0)).p S hS q) μ μ)
    (hmean : ∀ (S : Finset X) (hS : S.card = 4) (q : Split ↥S),
      ∫ ω, (locus (ω 0)).p S hS q ∂μ = m.freq.p S hS q) :
    ∀ᵐ ω ∂μ, ∀ (S : Finset X) (hS : S.card = 4) (q : Split ↥S),
      Tendsto (fun L : ℕ => (∑ ℓ ∈ Finset.range L, (locus (ω ℓ)).p S hS q) / L) atTop
        (𝓝 (m.freq.p S hS q)) := by
  have key := empFreq_tendsto_ae_all (locusSiteFun locus) m μ hint hindep hident hmean
  filter_upwards [key] with ω hω S hS q
  have hfun : (fun L : ℕ => (∑ ℓ ∈ Finset.range L, (locus (ω ℓ)).p S hS q) / L)
      = fun L : ℕ => empFreq (locusSiteFun locus) L ω S hS q := by
    funext L
    rw [empFreq]
    simp only [locusSiteFun, div_eq_inv_mul]
  rw [hfun]
  exact hω S hS q

open Classical in
/-- ★★★ **统一的 `L₀`**：几乎必然地，对一切 `ε > 0` 存在 `L₀`，使 `L ≥ L₀` 时
**整张**平均表与 `m.freq` `ε`-接近（`FreqClose`）。

证明 = `empFreq_eventually_close_ae_all`（逐指标各自的 `N`）＋ 有限指标集上的 `Finset.sup`
取**共同** `L₀`（`X` 有限 ⇒ 4-元集与 `split` 都有限）。 -/
theorem multiLocus_avg_eventually_close_ae (locus : Ω₀ → QuartetFreq X) (m : MSCFreq.{u, v} X)
    (μ : Measure (ℕ → Ω₀)) [IsProbabilityMeasure μ]
    (hint : ∀ (S : Finset X) (hS : S.card = 4) (q : Split ↥S),
      Integrable (fun ω : ℕ → Ω₀ => (locus (ω 0)).p S hS q) μ)
    (hindep : ∀ (S : Finset X) (hS : S.card = 4) (q : Split ↥S),
      iIndepFun (fun i (ω : ℕ → Ω₀) => (locus (ω i)).p S hS q) μ)
    (hident : ∀ (S : Finset X) (hS : S.card = 4) (q : Split ↥S), ∀ i,
      IdentDistrib (fun ω : ℕ → Ω₀ => (locus (ω i)).p S hS q)
        (fun ω : ℕ → Ω₀ => (locus (ω 0)).p S hS q) μ μ)
    (hmean : ∀ (S : Finset X) (hS : S.card = 4) (q : Split ↥S),
      ∫ ω, (locus (ω 0)).p S hS q ∂μ = m.freq.p S hS q) :
    ∀ᵐ ω ∂μ, ∀ ε : ℝ, 0 < ε → ∃ L₀ : ℕ, ∀ L ≥ L₀, ∀ hL : 0 < L,
      FreqClose (multiLocusData locus L hL ω).avg m.freq ε := by
  classical
  have key := empFreq_eventually_close_ae_all (locusSiteFun locus) m μ hint hindep hident hmean
  filter_upwards [key] with ω hω
  intro ε hε
  let N : QuartetIndex X → ℕ := fun i => Classical.choose (hω i.1.1 i.1.2 i.2 ε hε)
  refine ⟨max (Finset.univ.sup N) 1, fun L hL hLpos S hS q => ?_⟩
  have hN := Classical.choose_spec (hω S hS q ε hε)
  have hle : N ⟨⟨S, hS⟩, q⟩ ≤ max (Finset.univ.sup N) 1 :=
    le_trans (Finset.le_sup (Finset.mem_univ _)) (le_max_left _ 1)
  rw [multiLocusData_avg_eq_empFreq locus L hLpos ω S hS q]
  exact hN L (le_trans hle hL)

/-! ## 5. ★★★ 收口：多标记估计量的**几乎必然**统计一致性 -/

open Classical in
/-- ★★★ **多标记 ASTRAL 的几乎必然统计一致性（quartet 层）**：

在基因座 iid 模型下（§4 的四个假设），**几乎必然**地，多标记估计量 `E`
在**足够多基因座**后逐 quartet 恢复真树（模 `swap`）。

⚠️ 与 `MultiLocusASTRAL.multiLocus_maximizer_agrees` 的区别：那里 `L` **任意固定**、
假设 `M.avg = m.freq` 是**裸的**；这里 `L ≥ L₀`（`L₀` 存在）而假设全部是**概率层**的
（iid ＋ 正确边缘），由 SLLN 真正推出。**裸假设被删除。** -/
theorem multiLocus_statisticallyConsistent_ae (locus : Ω₀ → QuartetFreq X) (m : MSCFreq.{u, v} X)
    (μ : Measure (ℕ → Ω₀)) [IsProbabilityMeasure μ]
    (hint : ∀ (S : Finset X) (hS : S.card = 4) (q : Split ↥S),
      Integrable (fun ω : ℕ → Ω₀ => (locus (ω 0)).p S hS q) μ)
    (hindep : ∀ (S : Finset X) (hS : S.card = 4) (q : Split ↥S),
      iIndepFun (fun i (ω : ℕ → Ω₀) => (locus (ω i)).p S hS q) μ)
    (hident : ∀ (S : Finset X) (hS : S.card = 4) (q : Split ↥S), ∀ i,
      IdentDistrib (fun ω : ℕ → Ω₀ => (locus (ω i)).p S hS q)
        (fun ω : ℕ → Ω₀ => (locus (ω 0)).p S hS q) μ μ)
    (hmean : ∀ (S : Finset X) (hS : S.card = 4) (q : Split ↥S),
      ∫ ω, (locus (ω 0)).p S hS q ∂μ = m.freq.p S hS q)
    (hNE : ∃ q : QuartetChoice X, ¬ IsTrueChoice m q)
    {E : QuartetFreq X → QuartetTree.{u, v} X} (hE : ∀ D, IsASTRAL D (E D)) :
    ∀ᵐ ω ∂μ, ∃ L₀ : ℕ, ∀ L ≥ L₀, ∀ hL : 0 < L,
      IsTrueChoice m (E (multiLocusData locus L hL ω).avg).q := by
  classical
  obtain ⟨δ, hδ, hgap⟩ := exists_gap m hNE
  have hfac : (0 : ℝ) < 2 * (Fintype.card {S : Finset X // S.card = 4} : ℝ) + 1 := by
    positivity
  have hεpos : 0 < δ / (2 * (Fintype.card {S : Finset X // S.card = 4} : ℝ) + 1) :=
    div_pos hδ hfac
  filter_upwards [multiLocus_avg_eventually_close_ae locus m μ hint hindep hident hmean]
    with ω hω
  obtain ⟨L₀, hL₀⟩ := hω _ hεpos
  refine ⟨L₀, fun L hL hLpos => ?_⟩
  exact multiLocus_maximizer_agrees_close m _ hδ hgap
    ((multiLocus_isASTRAL _).mpr (hE _)) (hL₀ L hL hLpos)

open Classical in
/-- ★★★ **多标记 ASTRAL 的几乎必然**树层**统计一致性**：把 §5 的 quartet 层结论
经库内既有的 ★★★ `QuartetDecidesTree`（quartet 系统决定 binary 树）升到**树同构**。 -/
theorem multiLocus_iso_ae (locus : Ω₀ → QuartetFreq X) (m : MSCFreq.{u, v} X)
    (hT : m.tree.IsBinary) (μ : Measure (ℕ → Ω₀)) [IsProbabilityMeasure μ]
    (hint : ∀ (S : Finset X) (hS : S.card = 4) (q : Split ↥S),
      Integrable (fun ω : ℕ → Ω₀ => (locus (ω 0)).p S hS q) μ)
    (hindep : ∀ (S : Finset X) (hS : S.card = 4) (q : Split ↥S),
      iIndepFun (fun i (ω : ℕ → Ω₀) => (locus (ω i)).p S hS q) μ)
    (hident : ∀ (S : Finset X) (hS : S.card = 4) (q : Split ↥S), ∀ i,
      IdentDistrib (fun ω : ℕ → Ω₀ => (locus (ω i)).p S hS q)
        (fun ω : ℕ → Ω₀ => (locus (ω 0)).p S hS q) μ μ)
    (hmean : ∀ (S : Finset X) (hS : S.card = 4) (q : Split ↥S),
      ∫ ω, (locus (ω 0)).p S hS q ∂μ = m.freq.p S hS q)
    (hNE : ∃ q : QuartetChoice X, ¬ IsTrueChoice m q)
    {E : QuartetFreq X → QuartetTree.{u, v} X} (hE : ∀ D, IsASTRAL D (E D))
    (hEbin : ∀ D, (E D).tree.IsBinary) :
    ∀ᵐ ω ∂μ, ∃ L₀ : ℕ, ∀ L ≥ L₀, ∀ hL : 0 < L,
      Nonempty (Iso (E (multiLocusData locus L hL ω).avg).tree m.tree) := by
  filter_upwards [multiLocus_statisticallyConsistent_ae locus m μ hint hindep hident hmean
    hNE hE] with ω hω
  obtain ⟨L₀, hL₀⟩ := hω
  exact ⟨L₀, fun L hL hLpos =>
    QuartetDecidesTree X (E (multiLocusData locus L hLpos ω).avg) m.toQuartetTree
      (hEbin _) hT (hL₀ L hL hLpos)⟩

/-! ## 6. 反例检查（★B）：平均的 a.e. 极限**不一定**是真频率 -/

/-- ★★ **反例的代数核心**：若**所有**基因座都给出同一张表 `D`，则 `L` 个基因座的经验频率
（`L ≥ 1`）**恒等于** `D` 的分量 —— 与 `m.freq` 无关。

⇒ 于是 a.e. 极限是 `D.p S hS q`；当 `D ≠ m.freq` 时它**不是**真频率。
这证明 §4 的 `hmean`（「基因座边缘分布 = MSC 理论频率」）**不可省**：
它是结论里「真频率」三个字的**唯一**来源。（`Fin 4` 上取两个不同的内枝长即得具体反例，
见 `scripts/msc/w11f_g1_check.py`。） -/
theorem empFreq_const_locus (D : QuartetFreq X) (L : ℕ) (hL : 0 < L) (ω : ℕ → Ω₀)
    (S : Finset X) (hS : S.card = 4) (q : Split ↥S) :
    empFreq (locusSiteFun fun _ => (D : QuartetFreq X)) L ω S hS q = D.p S hS q := by
  have hL0 : (L : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hL)
  rw [empFreq]
  simp only [locusSiteFun, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀ hL0, one_mul]

/-! ## 7. 派生结构：把基因座 iid 模型打包（供下游直接引用） -/

/-- ★★★ **多标记律**（**派生结构**，库内惯例：**不改** `MultiMarkerFreq` 的任何字段）：
把「一个基因座表值随机变量 ＋ 基因座 iid 概率空间 ＋ 大数定律结论」打成一个包。

⚠️ 真实律 `m` 是**参数**而不是字段（避免不必要的宇宙级多态）；
`converges` 与本文件的 ★★★ `multiLocus_avg_eventually_close_ae` **同形** ——
本文件不把它当字段假设用，而是在 §4 里**证明**它。 -/
structure MultiMarkerFreqLaw {X : Type u} [Fintype X] [DecidableEq X]
    (m : MSCFreq.{u, v} X) (Ω₀ : Type*) [MeasurableSpace Ω₀] where
  /-- 基因座表值随机变量。 -/
  locus : Ω₀ → QuartetFreq X
  /-- 基因座序列的测度。 -/
  μ : Measure (ℕ → Ω₀)
  /-- 它是概率测度。 -/
  isProb : IsProbabilityMeasure μ
  /-- ★ **大数定律**（整张表、统一 `L₀`）。 -/
  converges : ∀ᵐ ω ∂μ, ∀ ε : ℝ, 0 < ε → ∃ L₀ : ℕ, ∀ L ≥ L₀, ∀ hL : 0 < L,
    FreqClose (multiLocusData locus L hL ω).avg m.freq ε

/-- ★★ **反空真**：对任意 MSC 律 `m`，`MultiMarkerFreqLaw` 有居民
（取 `μ = dirac`、`locus ≡ m.freq`：理想样本，此时平均表恒为 `m.freq`）。

⇒ 该派生结构**不是空类型**，§4 的 a.e. 结论才有内容。 -/
theorem multiMarkerFreqLaw_nonempty (m : MSCFreq.{u, v} X) :
    Nonempty (MultiMarkerFreqLaw m Unit) :=
  ⟨{ locus := fun _ => m.freq
     μ := Measure.dirac fun _ => ()
     isProb := inferInstance
     converges := by
       filter_upwards with ω ε hε
       refine ⟨1, fun L hL hLpos S hS q => ?_⟩
       rw [multiLocusData_avg_p]
       have hL0 : (L : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hLpos)
       simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
       rw [mul_div_cancel_left₀ _ hL0, sub_self, abs_zero]
       exact hε }⟩

end Phylo.Stat.MultiLocusLaw

end
