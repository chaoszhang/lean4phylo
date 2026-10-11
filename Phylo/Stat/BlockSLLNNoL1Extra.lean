/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.Stat.BlockSLLNNoL1

/-!
# `Phylo.Stat.BlockSLLNNoL1Extra` —— **`hL1` 判定的补件**（W13m）

本文件是 `Phylo/Stat/BlockSLLNNoL1.lean`（协调侧：`Phylo.Stat.BlockSLLN.BlockSLLN_no_L1`）
的**纯追加补件**：把新定理与既有主定理 `Phylo.Stat.BlockSLLN.BlockSLLN`（`Phylo/Stat/BlockSLLN.lean:142`）
接起来。**不改**那条新定理、**不改**任何已落盘文件（★C）✓。

## 1. `BlockSLLN_of_L1` —— 旧定理是新定理的**推论**（⇒「可去」有了机制性证据）

* 新定理的假设面：`hjoint / hident / hL0 (= ∫L₀ ≠ 0) / hintM / hintL`；
* 旧定理的假设面：`hjoint / hident / hL1 (= 1 ≤ L) / hintM / hintL`。

`hL1 ⇒ hL0` 的证明就是把旧文件 `BlockSLLN.lean:190–199` 的 `hL0pos` **逐字搬来**
（`IsProbabilityMeasure μ` ＋ `1 ≤ L 0` ⇒ `∫L₀ ≥ ∫1 = 1 > 0`）。
⇒ 旧定理的**每一条实例**都由新定理覆盖 ⇒ 新定理**严格强于**旧定理（「严格」= 假设面更弱，
且 `hL1` 不被新定理蕴含：取 `L ≡ -1` 则 `∫L₀ = -1 ≠ 0` 而 `¬ 1 ≤ L` ⇒ 见 §3.1）✓。

## 2. `BlockSLLNIdx_no_L1` —— 逐指标版（W13e 入口）同样去掉 `hL1`

## 3. ★D —— 本件对「`hL1` 是否必要」的完整判定

**结论：`hL1` 可去 ✓；但只能弱化到 `hL0 : ∫L₀ ≠ 0`，不能弱化到「无」。**

1. **`hL1` 可去**（与 `Phylo.Stat.BlockSLLN.BlockSLLN_no_L1` 一致，本文件独立复核过）：
   在 `BlockSLLN.lean` 里 `hL1` **只用两处** ——
   `:197`（`hL0pos`，造 `∫L₀ ≥ 1 > 0`）与 `:210`（给 `div_eq_div_blocks` 喂 `0 < L j ω`）；
   两处分别由**假设** `hL0` 与**零假设**恒等式 `div_eq_div_blocks_nohyp` 覆盖 ✓。
2. **`hL0` 是必需的**（`BlockSLLN_no_L1` 的假设面**不能再瘦**）：反例（**数学上成立、本文件未形式化**）
   取 `Ω = {−1,+1}^ℕ`、`μ` = 公平伯努利乘性测度、`M j ≡ 1`、`L j ω = ω j`（iid 均匀 `{±1}`）：
   * `iIndepFun` / `IdentDistrib` / `Integrable` 全满足，`∫M₀ = 1`、`∫L₀ = 0`；
   * `(Σ_(j<k) M_j)/(Σ_(j<k) L_j) = k / S_k(ω)`（`S` = 一维简单随机游走，`S_k = 0` 处取 `0`）；
   * 一维简单随机游走 **a.s. 无穷次回到 `0`**（常返性）且**每一步都非零** ⇒ 在每次回归后的下一时刻
     `|k/S_k| = k`，这些时刻无界 ⇒ 该序列 **a.s. 不收敛于 `𝔼M/𝔼L = 1/0 = 0`** ⇒ 结论**为假**。
   * **未形式化的原因（诚实交代）**：这一步需要「一维简单随机游走的常返性」（`S_k = 0` a.s. 无穷多次），
     Mathlib **没有**该定理（`grep` 未见可用常返性结果）⇒ 形式化它等于新开一个随机游走子项目。
     数值复现：`scripts/msc/W13m_no_L1_check.py` 的 `case_symmetric`（值 `k/S_k` 随 `k` 无界、且多次取 `0`）✓。
3. ★ **协调侧「`∫L₀ = 0` 时 `x/0 = 0` 使两边同为 `0` ⇒ 连 `hL0` 也可去」这一推论不成立**：
   `div_eq_div_blocks_nohyp` 的「两边同为 `0`」只对**逐点值**成立；
   而 `𝔼M/𝔼L = 𝔼M/0 = 0` 是 `Tendsto.div` **用不了**时的退化记号，**并不等于**实际序列的极限
   （第 2 条的反例里实际序列无界）✓。
4. ★ **协调侧「前缀全零概率几何可和 ⇒ Borel–Cantelli」路线正确但多余**：
   `div_eq_div_blocks_nohyp` 是**零假设**恒等式 ⇒ 它对**每一个** `k`（不只 a.e. 的有限例外）都成立，
   `x/0 = 0` 已经把退化点全兜住 ⇒ 不需要任何「有限多个 `k`」论证 ✓。
-/

set_option autoImplicit false
set_option linter.dupNamespace false

noncomputable section

open Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal

namespace Phylo.Stat.BlockSLLN

/-! ## 1. 旧主定理由新定理导出 -/

/-- ★★ **既有主定理 `BlockSLLN` 由 `BlockSLLN_no_L1` 导出**（⇒ 新定理**严格更强**）。

`hL1 ⇒ hL0` 的证明是 `BlockSLLN.lean:190–199` 的 `hL0pos` **逐字**搬来：
`IsProbabilityMeasure μ` ＋ `1 ≤ L 0` ⇒ `∫L₀ ≥ ∫1 = 1 > 0` ✓。 -/
theorem BlockSLLN_of_L1 {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {M L : ℕ → Ω → ℝ}
    (hjoint : iIndepFun (fun j ω => (M j ω, L j ω)) μ)
    (hident : ∀ j, IdentDistrib (fun ω => (M j ω, L j ω)) (fun ω => (M 0 ω, L 0 ω)) μ μ)
    (hL1 : ∀ j ω, (1 : ℝ) ≤ L j ω)
    (hintM : Integrable (fun ω => M 0 ω) μ)
    (hintL : Integrable (fun ω => L 0 ω) μ) :
    ∀ᵐ ω ∂μ, Tendsto
      (fun k : ℕ => (∑ j ∈ Finset.range k, M j ω) / (∑ j ∈ Finset.range k, L j ω))
      atTop (𝓝 ((∫ ω, M 0 ω ∂μ) / (∫ ω, L 0 ω ∂μ))) := by
  have hL0 : (∫ ω, L 0 ω ∂μ) ≠ 0 := by
    have hone : (∫ _ω : Ω, (1 : ℝ) ∂μ) = 1 := by
      rw [integral_const]
      rw [show μ.real Set.univ = (1 : ℝ) by
        rw [Measure.real, measure_univ, ENNReal.toReal_one]]
      simp
    have hle : (∫ _ω : Ω, (1 : ℝ) ∂μ) ≤ ∫ ω, L 0 ω ∂μ :=
      integral_mono_ae (integrable_const (1 : ℝ)) hintL (Eventually.of_forall (hL1 0))
    exact ne_of_gt (by linarith)
  exact BlockSLLN_no_L1 hjoint hident hL0 hintM hintL

/-! ## 2. 逐指标版（W13e 入口） -/

/-- ★★★ **逐指标块级 SLLN（去掉 `hL1`）**：与 `Phylo.Stat.BlockSLLN.BlockSLLNIdx` 同形，
唯一改动是把 `(hL1 : ∀ i j ω, 1 ≤ Lf i j ω)` 换成 `(hL0 : ∀ i, (∫ ω, Lf i 0 ω ∂μ) ≠ 0)` ✓。 -/
theorem BlockSLLNIdx_no_L1 {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {ι : Type*} [Fintype ι]
    {Mf Lf : ι → ℕ → Ω → ℝ} {lim : ι → ℝ}
    (hjoint : ∀ i, iIndepFun (fun j ω => (Mf i j ω, Lf i j ω)) μ)
    (hident : ∀ i j, IdentDistrib (fun ω => (Mf i j ω, Lf i j ω))
      (fun ω => (Mf i 0 ω, Lf i 0 ω)) μ μ)
    (hL0 : ∀ i, (∫ ω, Lf i 0 ω ∂μ) ≠ 0)
    (hintM : ∀ i, Integrable (fun ω => Mf i 0 ω) μ)
    (hintL : ∀ i, Integrable (fun ω => Lf i 0 ω) μ)
    (hlim : ∀ i, (∫ ω, Mf i 0 ω ∂μ) / (∫ ω, Lf i 0 ω ∂μ) = lim i) :
    ∀ᵐ ω ∂μ, ∀ i : ι, Tendsto
      (fun k : ℕ => (∑ j ∈ Finset.range k, Mf i j ω) / (∑ j ∈ Finset.range k, Lf i j ω))
      atTop (𝓝 (lim i)) := by
  classical
  have key : ∀ i : ι, ∀ᵐ ω ∂μ, Tendsto
      (fun k : ℕ => (∑ j ∈ Finset.range k, Mf i j ω) / (∑ j ∈ Finset.range k, Lf i j ω))
      atTop (𝓝 ((∫ ω, Mf i 0 ω ∂μ) / (∫ ω, Lf i 0 ω ∂μ))) :=
    fun i => BlockSLLN_no_L1 (hjoint i) (fun j => hident i j) (hL0 i) (hintM i) (hintL i)
  have hall : ∀ᵐ ω ∂μ, ∀ i : ι, Tendsto
      (fun k : ℕ => (∑ j ∈ Finset.range k, Mf i j ω) / (∑ j ∈ Finset.range k, Lf i j ω))
      atTop (𝓝 ((∫ ω, Mf i 0 ω ∂μ) / (∫ ω, Lf i 0 ω ∂μ))) :=
    (Filter.eventually_all).mpr key
  filter_upwards [hall] with ω hω i
  have := hω i
  rwa [hlim i] at this

end Phylo.Stat.BlockSLLN
