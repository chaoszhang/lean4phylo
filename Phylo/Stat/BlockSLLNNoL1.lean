/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.Stat.CASTERTopo
import Phylo.Stat.MSCSamplingAE

/-!
# `Phylo.Stat.BlockSLLN.BlockSLLN_no_L1` —— **块级 SLLN 去掉 `hL1` 的加强版**（W13 ＋ W13m 判定）

⚠️ **文件路径 ≠ 命名空间**：本文件（`Phylo/Stat/BlockSLLNNoL1.lean`）里的声明住在
**`namespace Phylo.Stat.BlockSLLN`** 里 ⇒ 全名是 `Phylo.Stat.BlockSLLN.BlockSLLN_no_L1`
（**不是** `Phylo.Stat.BlockSLLNNoL1.BlockSLLN_no_L1`）✓ —— 按模块名猜前缀会得到 `Unknown constant`。

## 1. 本文件是什么

`Phylo/Stat/BlockSLLN.lean:142` 的主定理 `BlockSLLN` 有一条假设
`hL1 : ∀ j ω, (1 : ℝ) ≤ L j ω`（每块位点数 ≥ 1）。本文件给出它的**加强版**：
把 `hL1` 换成**更弱**的 `hL0 : (∫ ω, L 0 ω ∂μ) ≠ 0` ✓ —— 即 **`hL1` 不是本质假设** ✓。

## 2. 交付（两条）

| 声明 | 内容 |
|---|---|
| ★★ `div_eq_div_blocks_nohyp` | **零假设**的取商恒等式：`((ΣM)/k)/((ΣL)/k) = (ΣM)/(ΣL)`（原版 `div_eq_div_blocks` 要求 `∀ j, 0 < L j ω`，本版**去掉**） |
| ★★★ `BlockSLLN_no_L1` | **主定理的加强版**：假设面 = `hjoint / hident / **hL0** / hintM / hintL`（`hL1` 已去除） |

## 3. 为什么 `hL1` 可去（逐处，实读 `BlockSLLN.lean` 全文）

`hL1` 在 `BlockSLLN` 的证明里**只有两处**用法：
1. `:190–198` 的 `hL0pos`：由 `1 ≤ L 0` 经 `integral_mono_ae` 造出 `∫L₀ ≥ 1 > 0`，**只为**供
   `:207` 的 `Filter.Tendsto.div`（它要求分母极限 ≠ 0）⇒ **换成假设** `hL0` ✓；
2. `:210`：`div_eq_div_blocks ω k (fun j => …)` 的参数 `∀ j, 0 < L j ω`，**只为**造 `ΣL ≠ 0` 以启动
   `field_simp` ⇒ **换成零假设的** `div_eq_div_blocks_nohyp` ✓（`ℝ` 的 `x / 0 = 0` 使 `ΣL = 0` 与 `k = 0` 时两边同为 `0`）。
其余全文（`hpairM`/`hpairL`/`hidentM`/`hidentL`/`strong_law_ae_real`）**不含** `hL1` ✓。
（独立复核：W13m 另写一版逐行比对，逻辑相同、同样编译通过 ✓。）

## 4. ★D 诚实边界（逐条，不藏）

| 条目 | 状态 |
|---|---|
| `hL1` **可去** | ✅ **已证**（本文件）✓ |
| `hL0` **能否再去掉** | ❌ **不能**（反例，**本文件未形式化**）：取 `M j ≡ 1`、`L j ω = ω j` i.i.d. 均匀 `{±1}`（故 `∫L₀ = 0`），其余假设全满足，则 `(ΣM)/(ΣL) = k / S_k`（`S` = 一维简单随机游走）**不收敛于** `𝔼M/𝔼L = 1/0 = 0` ✓。**未形式化的原因**：需「一维 SRW 常返性」（a.s. 无穷次回 0），Mathlib **无**该定理 ⇒ 形式化它等于新开随机游走子项目；数值证据见 `scripts/msc/W13m_no_L1_check.py` 的 `case_symmetric` ✓ |
| 「`x/0 = 0` ⇒ 两边同为 0 ⇒ 连 `hL0` 也可去」 | ❌ **不成立**：两边同为 `0` 只对**逐点值**成立；`𝔼M/0 = 0` 是 `Tendsto.div` **用不了**时的退化记号，**不等于**实际序列的极限（上述反例里实际序列无界）✓ |
| 「前缀全零概率几何可和 ＋ Borel–Cantelli」路线 | ⚠️ **正确但多余**：`div_eq_div_blocks_nohyp` 是**零假设**恒等式 ⇒ 对**每一个** `k`（不只 a.e. 有限例外）都成立，`x/0 = 0` 已把退化点全兜住 ✓ |
| 「新定理严格强于旧定理」 | ✅ **有机制性证据**：见补件 `Phylo/Stat/BlockSLLNNoL1Extra.lean` 的 `BlockSLLN_of_L1` —— 其签名与 `BlockSLLN` **逐字相同**，并由本文件的 `BlockSLLN_no_L1` **在 Lean 里导出** ✓ |
| 本文件**不含** `BlockSLLN` / `BlockSLLNIdx` / `BlockSLLNHyp` 等 | ✅ 它们都在 `Phylo/Stat/BlockSLLN.lean` ✓（本文件只含上表两条） |
| 反空洞 | ✅ 本文件**不新增** `structure` / `def : Prop`；`div_eq_div_blocks_nohyp` 与 `BlockSLLN_no_L1` 均有平凡实例可代入 ✓ |
-/

set_option autoImplicit false
set_option linter.dupNamespace false

noncomputable section

open Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal

namespace Phylo.Stat.BlockSLLN

/-- ★★ **`div_eq_div_blocks` 的 `hL : ∀ j, 0 < L j ω` 可去**（原版只用它启动 `field_simp`；
退化情形 `ΣL = 0` 时两边都塌成 `0`，由 Lean 的 `x / 0 = 0` 约定）。 -/
theorem div_eq_div_blocks_nohyp {Ω : Type*} {M L : ℕ → Ω → ℝ} (ω : Ω) (k : ℕ) :
    ((∑ i ∈ Finset.range k, M i ω) / (k : ℝ))
        / ((∑ i ∈ Finset.range k, L i ω) / (k : ℝ))
      = (∑ i ∈ Finset.range k, M i ω) / (∑ i ∈ Finset.range k, L i ω) := by
  by_cases hk : k = 0
  · subst hk; simp
  · by_cases hden : (∑ i ∈ Finset.range k, L i ω) = 0
    · simp [hden]
    · have hkR : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk
      field_simp

/-- ★★★ **块级强大数定律（不带 `hL1` 的加强版）**：把 `1 ≤ L j ω` 换成**更弱的**
`hL0 : ∫ ω, L 0 ω ∂μ ≠ 0`（`Filter.Tendsto.div` 只需要分母极限非零）。

★ 由来：在 `BlockSLLN` 的证明里 `hL1` 只用在两处 ——
① 推出 `∫L₀ ≥ 1 > 0`（`hL0pos`，本版**直接换成假设** `hL0`）；
② 供 `div_eq_div_blocks` 用（本版改用**不带假设的** `div_eq_div_blocks_nohyp`，其退化情形由 `x/0 = 0` 兜住）。
⇒ **`hL1` 不是本质的** ✓。 -/
theorem BlockSLLN_no_L1 {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {M L : ℕ → Ω → ℝ}
    (hjoint : iIndepFun (fun j ω => (M j ω, L j ω)) μ)
    (hident : ∀ j, IdentDistrib (fun ω => (M j ω, L j ω)) (fun ω => (M 0 ω, L 0 ω)) μ μ)
    (hL0 : (∫ ω, L 0 ω ∂μ) ≠ 0)
    (hintM : Integrable (fun ω => M 0 ω) μ)
    (hintL : Integrable (fun ω => L 0 ω) μ) :
    ∀ᵐ ω ∂μ, Tendsto
      (fun k : ℕ => (∑ j ∈ Finset.range k, M j ω) / (∑ j ∈ Finset.range k, L j ω))
      atTop (𝓝 ((∫ ω, M 0 ω ∂μ) / (∫ ω, L 0 ω ∂μ))) := by
  classical
  have hpairM : Pairwise (Function.onFun (fun x1 x2 : Ω → ℝ => x1 ⟂ᵢ[μ] x2)
      (fun j (ω : Ω) => M j ω)) := by
    intro i j hij
    have h1 : (fun ω => (M i ω, L i ω)) ⟂ᵢ[μ] (fun ω => (M j ω, L j ω)) :=
      hjoint.indepFun (β := fun _ => ℝ × ℝ) hij
    have h2 := h1.comp (φ := fun p : ℝ × ℝ => p.1) (ψ := fun p : ℝ × ℝ => p.1)
      measurable_fst measurable_fst
    have h3 : ((fun p : ℝ × ℝ => p.1) ∘ fun ω => (M i ω, L i ω)) = fun ω => M i ω := rfl
    have h4 : ((fun p : ℝ × ℝ => p.1) ∘ fun ω => (M j ω, L j ω)) = fun ω => M j ω := rfl
    rw [h3, h4] at h2
    exact h2
  have hpairL : Pairwise (Function.onFun (fun x1 x2 : Ω → ℝ => x1 ⟂ᵢ[μ] x2)
      (fun j (ω : Ω) => L j ω)) := by
    intro i j hij
    have h1 : (fun ω => (M i ω, L i ω)) ⟂ᵢ[μ] (fun ω => (M j ω, L j ω)) :=
      hjoint.indepFun (β := fun _ => ℝ × ℝ) hij
    have h2 := h1.comp (φ := fun p : ℝ × ℝ => p.2) (ψ := fun p : ℝ × ℝ => p.2)
      measurable_snd measurable_snd
    have h3 : ((fun p : ℝ × ℝ => p.2) ∘ fun ω => (M i ω, L i ω)) = fun ω => L i ω := rfl
    have h4 : ((fun p : ℝ × ℝ => p.2) ∘ fun ω => (M j ω, L j ω)) = fun ω => L j ω := rfl
    rw [h3, h4] at h2
    exact h2
  have hidentM : ∀ i, IdentDistrib (fun ω => M i ω) (fun ω => M 0 ω) μ μ := by
    intro i
    have h2 := (hident i).comp measurable_fst
    have h3 : (fun p : ℝ × ℝ => p.1) ∘ (fun ω => (M i ω, L i ω)) = fun ω => M i ω := rfl
    have h4 : (fun p : ℝ × ℝ => p.1) ∘ (fun ω => (M 0 ω, L 0 ω)) = fun ω => M 0 ω := rfl
    rw [h3, h4] at h2
    exact h2
  have hidentL : ∀ i, IdentDistrib (fun ω => L i ω) (fun ω => L 0 ω) μ μ := by
    intro i
    have h2 := (hident i).comp measurable_snd
    have h3 : (fun p : ℝ × ℝ => p.2) ∘ (fun ω => (M i ω, L i ω)) = fun ω => L i ω := rfl
    have h4 : (fun p : ℝ × ℝ => p.2) ∘ (fun ω => (M 0 ω, L 0 ω)) = fun ω => L 0 ω := rfl
    rw [h3, h4] at h2
    exact h2
  have hA := strong_law_ae_real (μ := μ) (fun j (ω : Ω) => M j ω) hintM hpairM hidentM
  have hB := strong_law_ae_real (μ := μ) (fun j (ω : Ω) => L j ω) hintL hpairL hidentL
  filter_upwards [hA, hB] with ω hωA hωB
  have hquot : Tendsto
      ((fun n : ℕ => (∑ i ∈ Finset.range n, M i ω) / (n : ℝ)) /
       fun n : ℕ => (∑ i ∈ Finset.range n, L i ω) / (n : ℝ)) atTop
      (𝓝 ((∫ ω, M 0 ω ∂μ) / (∫ ω, L 0 ω ∂μ))) :=
    hωA.div hωB hL0
  refine Filter.Tendsto.congr' (Eventually.of_forall fun k => ?_) hquot
  rw [Pi.div_apply]
  exact div_eq_div_blocks_nohyp ω k



end Phylo.Stat.BlockSLLN
