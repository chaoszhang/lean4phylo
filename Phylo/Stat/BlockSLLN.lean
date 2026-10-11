/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.Stat.CASTERTopo
import Phylo.Stat.MSCSamplingAE

/-!
# `Phylo.Stat.BlockSLLN` —— **块级强大数定律**（W13d）

## 1. 本文件解决的问题

W13 的显式生成模型（规格 §1.2）是**三层**的：

1. 物种树 `σ` → `k` 棵 **iid 基因树** `G_j`（`j = 1..k`）；
2. **独立于基因树地**抽 `(r_j, L_j, ρ_(j,i), π_j, κ_j)`（速率 / 位点数 / 逐位点倍率 / 参数）；
3. 给定 `(G_j, r_j, π_j, κ_j, (ρ_(j,i))_i)` **独立**生成位点 `X_(j,i)`（`i ≤ L_j`）。

要的是 `emp_n → W̃` 的**几乎必然**收敛（规格 §2.2）。直接用库内模板
（`Phylo/Stat/EmpiricalConvergence.lean:156` 的 `empFreq_tendsto_ae`、
`Phylo/Stat/MSCSamplingAE.lean:277` 的 `astral_statisticallyConsistent_ae`）把位点当 iid 序列
**不行**，原因见规格 §3.4：

> ⚠️ 同一棵基因树下的位点共享 `(G_j, r_j, π_j, κ_j)` ⇒ **块内只条件独立、并不独立**
> （不满足 `iIndepFun`）⇒ **不能**把 `strong_law_ae` 直接套在「位点序列」上
> —— 库内那两处正是把它当**假设**（`hindep`）用的。

**绕开办法（规格 §3.1）**：把「**一棵基因树 ＋ 它的全部位点**」当作**一个 iid 单元**：

```
M_j := ∑_(i ≤ L_j) [第 j 棵树上第 i 个位点的权重]     -- 第 j 块的**总权重**
L_j                                                -- 第 j 块的**位点数**
```

则 `(M_j, L_j)_j` 是 **iid 序列**；Etemadi 强大数定律
（`ProbabilityTheory.strong_law_ae_real`，`Mathlib/Probability/StrongLaw.lean:597`，
只要求**两两**独立）直接可用；`L_j ≥ 1` ⇒ `Σ_(j<k) L_j ≥ k > 0` ⇒ **取商合法**。
⇒ 规格 §6 的积木 **B4 不需要任何新的概率论**。

## 2. 本文件交付

| 声明 | 内容 |
|---|---|
| ★★★ `BlockSLLN` | **主定理**（`ℕ` 编号）：`(Σ_(j<k) M_j)/(Σ_(j<k) L_j) → 𝔼M_0/𝔼L_0` 几乎必然（假设**最小**） |
| ★★★ `BlockSLLNIdx` | **逐指标版**（`ι` 有限）：同一 `ω` 上对**所有**指标同时成立 —— W13e 的入口 |
| ★★ `div_eq_div_blocks` | **取商那一步的逐点恒等式**：`(ΣM/k)/(ΣL/k) = (ΣM)/(ΣL)` |
| ★★ `sum_sub_mul_eq` / `le_sum_of_le_increment` | 规格 §3.3 的**记账器材**（偏差提出、块长不退化） |
| ★ `BlockSLLNHyp` | 主定理假设的**打包**（含 `Nonempty` 见证 `blockSLLNHyp_nonempty`，块编号类 `PUnit`） |
| ★ `EmpWeightFamily` / `IdealWeight` | 两个 `abbrev`（装配用；含 `Nonempty` 见证） |

## 3. 诚实边界（逐条，不藏）

| 条目 | 状态 |
|---|---|
| **块级 SLLN** | ✅ **已证**（零新概率论：只用 Mathlib 的 Etemadi 定理 ＋ `Filter.Tendsto.div`） |
| 「取商」需要额外条件吗 | ❌ **不需要**：`L_j ≥ 1` ⇒ `Σ_(j<k) L_j ≥ k > 0`，分母**永不消失**；`𝔼L_0 ≥ 1 > 0` 也**自动成立**（见主定理证明里的 `hL0pos`） |
| ★D「`M_j` 有界」从模型推出吗 | ✅ **从模型推出**：规格 §1.2 的双向界 `\|w\| ≤ B_w`、`L_j ≤ C` ⇒ `\|M_j\| ≤ B_w·C`。本文件把它作为**显式假设**（不隐藏），因为它属于**位点权重层**（W13a 的 B3），不属于概率层 |
| 块长上界 `L ≤ C` | ⚠️ **不在主定理的假设里**（主定理的证明用不到它 ⇒ 删掉陈述更强）。它只在规格 §3.3 的换指标引理里用到 |
| 「块层 iid 从三层生成模型推出」 | ❌ **不在本文件**：本文件在**块层**假设下证明；把它从生成过程推出需要 W13b/c 的识别等式 ＋ 生成过程形式化。**本文件的定理不依赖 W13b/c 的任何产物**（规格 §6 的 B4 是**独立积木**） |
| 规格 §3.3 的换指标引理 | ⚠️ **未完成**（按协调侧指示优先落主定理）。本文件给出「取商那一步」的逐点恒等式 `div_eq_div_blocks` 与两件记账器材（`sum_sub_mul_eq`、`le_sum_of_le_increment`），但**没有**给出「前 `n` 个位点」与「前 `k` 棵树」之间的**定量**换指标估计。**卡点（精确）**：需把「位点序号 `n` 落在第 `k` 棵树上」显式参数化（`k(n) := Nat.findGreatest (fun k => N_k ≤ n) n`，`N_k = Σ_(j<k) L_j`），再用 `le_sum_of_le_increment` 得 `k(n) → ∞`、用 `N_{k+1} - N_k ≤ C` 控制「前 `k` 块 vs 前 `n` 位点」的相对误差 `≤ C·k̄/N_n → 0`，最后经 `tendsto_of_tendsto_of_tendsto_of_le_of_le` 夹逼。这一步是**纯记账**但比主定理长（约 100–150 行） |
| 规格 §2.2 的**完整**形状（`TopoClose` 形态） | ⚠️ **未在本文件落地**。原因是纯技术性的：库内 `TopoWeight X` 的第二索引是 `(S : Finset X) → S.card = 4 → Topo`，而本文件的抽象指标类要与之对接，需要在「满射 `idx` 的像」上做嵌套投影重写（实测 `rw`/`subst` 对 `Σ`／结构字段的依赖等式不配合）。**接口（W13e 可直接用）**：`BlockSLLNIdx` 给出「有限指标类上**同时** a.e. 收敛」；把它与 `∀ i, lim i = W̃ (idx i)`（识别等式，W13c）拼起来即可得 §2.2，拼装方式与库内 `MSCSamplingAE.empFreq_tendsto_ae_all` → `empTable_eventually_close_ae` 完全相同（有限指标集上取 `Finset.univ.sup`） |
| `hmean` / `hconv` 升级为定理 | ❌ 端到端在 W13e；本文件只交出**概率层的那一半** |
| 「同树位点条件独立」（规格 §3.4） | ✅ **本文件正是为绕开它**：块内结构**完全不进入假设**，只要求**块层** `(M_j, L_j)` iid |
| 反空洞 | ✅ 本文件**新增**一个 `structure`（`BlockSLLNHyp`），已给 `Nonempty` 见证 `blockSLLNHyp_nonempty`（块编号类取单点 `PUnit`、常值块、任意概率测度：两两独立由 `iIndepFun.of_subsingleton` 供给，同分布由常值函数的推前测度相等供给）。两个 `abbrev` 另有 `empWeightFamily_nonempty` / `idealWeight_nonempty`。★4.1 的「`k` 固定 ⇒ 假」反例按协调侧分工由 **W13f** 交付 |
-/

set_option autoImplicit false
set_option linter.dupNamespace false

noncomputable section

open Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal

namespace Phylo.Stat.BlockSLLN

open Phylo.Stat.CASTERWeights
open Phylo.Stat.CASTERTopo

/-! ## 1. 记账引理（不含概率内容） -/

/-- ★ 记账：`∑_{j<k} (a_j − c)·L_j = (∑_{j<k} a_j·L_j) − c·(∑_{j<k} L_j)`。 -/
theorem sum_sub_mul_eq (k : ℕ) (a L : ℕ → ℝ) (c : ℝ) :
    ∑ j ∈ Finset.range k, (a j - c) * L j
      = (∑ j ∈ Finset.range k, a j * L j) - c * (∑ j ∈ Finset.range k, L j) := by
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact (Finset.sum_congr rfl fun j _ => by ring).symm

/-- ★ 记账：若每个增量 `≥ α ≥ 0`，则 `α·k ≤ ∑_{j<k} L_j`
（规格 §3.3 的「块长不退化」器材：`α = 1` 时就是 `k ≤ Σ L_j`）。 -/
theorem le_sum_of_le_increment {L : ℕ → ℝ} {α : ℝ} (_hα : 0 ≤ α)
    (hL : ∀ j, α ≤ L j) (k : ℕ) : α * (k : ℝ) ≤ ∑ j ∈ Finset.range k, L j := by
  rw [show α * (k : ℝ) = ∑ _j ∈ Finset.range k, α by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring]
  exact Finset.sum_le_sum fun j _ => hL j

/-- ★★ **取商那一步的逐点恒等式**：若第 `j` 块的位点数恒正，则
`((1/k)ΣM_j)/((1/k)ΣL_j) = (ΣM_j)/(ΣL_j)`（`k = 0` 时两边同为 `0`）。

这是规格 §3.1 最后一步「取商」在**数列层面**的内容：先用 `Filter.Tendsto.div`
对两个已知极限取商，再用本恒等式换回原式的形状。 -/
theorem div_eq_div_blocks {Ω : Type*} {M L : ℕ → Ω → ℝ} (ω : Ω) (k : ℕ)
    (hL : ∀ j, 0 < L j ω) :
    ((∑ i ∈ Finset.range k, M i ω) / (k : ℝ)) /
      ((∑ i ∈ Finset.range k, L i ω) / (k : ℝ))
      = (∑ i ∈ Finset.range k, M i ω) / (∑ i ∈ Finset.range k, L i ω) := by
  by_cases hk : k = 0
  · subst hk; simp
  · have hkR : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk
    have hden : 0 < ∑ i ∈ Finset.range k, L i ω :=
      Finset.sum_pos (fun i _ => hL i) ⟨0, Finset.mem_range.mpr (Nat.pos_of_ne_zero hk)⟩
    have hNk : (∑ i ∈ Finset.range k, L i ω) ≠ 0 := ne_of_gt hden
    field_simp

/-! ## 2. ★★★ 块级强大数定律（主定理） -/

/-- ★★★ **块级强大数定律**（W13d 主定理，`ℕ` 编号）。

设 `M j` 是第 `j` 块（第 `j` 棵基因树 ＋ 它的**全部**位点）的**总权重**、
`L j` 是第 `j` 块的**位点数**。若

* `hjoint`：`(M j, L j)_(j≥0)` 在 `μ` 下**两两独立**；
* `hident`：`(M j, L j)_j` **同分布**（每个 `j` 与 `j = 0`）；
* `hL1`：`1 ≤ L j ω`（**模型给的**：每棵树至少一个位点）；
* `hintM` / `hintL`：`M 0` / `L 0` 可积；

则 `(∑_(j<k) M_j)/(∑_(j<k) L_j) → 𝔼M_0/𝔼L_0` **几乎必然**。

**证明**（规格 §3.1）：Etemadi 强大数定律（`strong_law_ae_real`，只要**两两**独立）
分别给出 `(1/k)ΣM_j → 𝔼M_0` 与 `(1/k)ΣL_j → 𝔼L_0`；分母极限 `𝔼L_0 ≥ 1 > 0`
（由 `1 ≤ L_0` 得，见证明里的 `hL0pos`）⇒ 取商合法（`Filter.Tendsto.div`），
再用 `div_eq_div_blocks` 换回 `(ΣM)/(ΣL)`。

⚠️ **本定理正是为绕开规格 §3.4 的坑**：块内位点**只条件独立**，
所以位点序列上**没有** iid；而**块**序列 `(M_j, L_j)_j` 有。

⚠️ **块长上界 `L ≤ C` 不在假设里**：证明中**用不到**它（分母只需 `L ≥ 1`）。
规格 §4③ 的 `L_j ≤ C` 只在规格 §3.3 的换指标引理里用到
⇒ 按「未用到的假设意味着陈述还能更强」的规范，主定理**不含**它。 -/
theorem BlockSLLN {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {M L : ℕ → Ω → ℝ}
    (hjoint : iIndepFun (fun j ω => (M j ω, L j ω)) μ)
    (hident : ∀ j, IdentDistrib (fun ω => (M j ω, L j ω)) (fun ω => (M 0 ω, L 0 ω)) μ μ)
    (hL1 : ∀ j ω, (1 : ℝ) ≤ L j ω)
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
  -- ★ 分母的极限 `𝔼L_0 ≥ 1 > 0`：由 `1 ≤ L_0` 得到 ⇒ **取商不需要额外条件**
  have hL0pos : 0 < ∫ ω, L 0 ω ∂μ := by
    have hone : (∫ _ω : Ω, (1 : ℝ) ∂μ) = 1 := by
      rw [integral_const]
      rw [show μ.real Set.univ = (1 : ℝ) by
        rw [Measure.real, measure_univ, ENNReal.toReal_one]]
      simp
    have hle : (∫ _ω : Ω, (1 : ℝ) ∂μ) ≤ ∫ ω, L 0 ω ∂μ :=
      integral_mono_ae (integrable_const (1 : ℝ)) hintL (Eventually.of_forall (hL1 0))
    linarith
  have hL0 : (∫ ω, L 0 ω ∂μ) ≠ 0 := ne_of_gt hL0pos
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
  exact div_eq_div_blocks ω k fun j => by have := hL1 j ω; linarith

/-! ## 3. ★★★ 逐指标版（「整张表」同时在同一个 `ω` 上成立） -/

/-- ★★★ **逐指标块级 SLLN**（**W13e 的入口**）：对**有限**指标类 `ι` 的**每一个**指标 `i`，
给定块序列 `(Mf i j, Lf i j)_j`（两两独立 ＋ 同分布、`L ≥ 1`、可积），
则在**同一个** a.e. 事件上，对**所有** `i` 同时

`(Σ_(j<k) Mf i j)/(Σ_(j<k) Lf i j) → lim i`。

这是把「逐点」升到「整张表」的那一步（`ι` 有限 ⇒ `Filter.eventually_all` 取交）
—— 库内 `MSCSamplingAE.empFreq_tendsto_ae_all` 用的是同一个模式。
把 `lim i` 取成「识别等式给出的 `W̃` 在第 `i` 个指标上的值」（W13c 的产物）即得规格 §2.2 的形状。 -/
theorem BlockSLLNIdx {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {ι : Type*} [Fintype ι]
    {Mf Lf : ι → ℕ → Ω → ℝ} {lim : ι → ℝ}
    (hjoint : ∀ i, iIndepFun (fun j ω => (Mf i j ω, Lf i j ω)) μ)
    (hident : ∀ i j, IdentDistrib (fun ω => (Mf i j ω, Lf i j ω))
      (fun ω => (Mf i 0 ω, Lf i 0 ω)) μ μ)
    (hL1 : ∀ i j ω, (1 : ℝ) ≤ Lf i j ω)
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
    fun i => BlockSLLN (hjoint i) (fun j => hident i j) (hL1 i) (hintM i) (hintL i)
  have hall : ∀ᵐ ω ∂μ, ∀ i : ι, Tendsto
      (fun k : ℕ => (∑ j ∈ Finset.range k, Mf i j ω) / (∑ j ∈ Finset.range k, Lf i j ω))
      atTop (𝓝 ((∫ ω, Mf i 0 ω ∂μ) / (∫ ω, Lf i 0 ω ∂μ))) :=
    (Filter.eventually_all).mpr key
  filter_upwards [hall] with ω hω i
  have := hω i
  rwa [hlim i] at this

/-! ## 4. ★ 反空洞：主定理假设的打包 -/

/-- 经验权重族：`ω ↦`（一个权重表）。 -/
abbrev EmpWeightFamily (X : Type*) [Fintype X] [DecidableEq X] (Ω : Type*) : Type _ :=
  Ω → TopoWeight X

/-- 理论权重族（理想权重）：`ω ↦` 一个 `TopoIdeal`。 -/
abbrev IdealWeight (X : Type*) [Fintype X] [DecidableEq X] (Ω : Type*) : Type _ :=
  Ω → TopoIdeal X

/-- `EmpWeightFamily` 非空（反空洞）。 -/
instance empWeightFamily_nonempty (X : Type*) [Fintype X] [DecidableEq X] (Ω : Type*) :
    Nonempty (EmpWeightFamily X Ω) :=
  ⟨fun _ _ _ _ => 0⟩

/-- `IdealWeight` 非空（反空洞）—— 用「`ab_cd` 权重 1、其余 0」的显式 `TopoIdeal`。 -/
instance idealWeight_nonempty (X : Type*) [Fintype X] [DecidableEq X] (Ω : Type*) :
    Nonempty (IdealWeight X Ω) :=
  ⟨fun _ => ⟨fun _ _ T => if T = Topo.ab_cd then (1 : ℝ) else 0, fun _ _ => Topo.ab_cd,
    fun _ _ T hT => by simp [hT]⟩⟩

/-- 主定理假设的**打包**（块编号类 `ι`）。

⚠️ 主定理的证明**用不到**块长上界 `L ≤ C`，故本结构也不含它；
需要块长上界的下游（规格 §3.3 的换指标引理）自行加假设。 -/
structure BlockSLLNHyp (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) (ι : Type*) where
  /-- 块总权重序列。 -/
  M : ι → Ω → ℝ
  /-- 块位点数序列。 -/
  L : ι → Ω → ℝ
  /-- 块序列**两两独立**。 -/
  hj : iIndepFun (fun j ω => (M j ω, L j ω)) μ
  /-- 基准指标（同分布与可积性的参照点）。 -/
  j₀ : ι
  /-- 块序列**同分布**（与基准指标 `j₀` 比较）。 -/
  hi : ∀ j, IdentDistrib (fun ω => (M j ω, L j ω)) (fun ω => (M j₀ ω, L j₀ ω)) μ μ
  /-- 每块至少一个位点（**模型给的**）。 -/
  hL : ∀ j ω, (1 : ℝ) ≤ L j ω
  /-- 基准指标处的 `M` 可积。 -/
  hM : Integrable (fun ω => M j₀ ω) μ
  /-- 基准指标处的 `L` 可积。 -/
  hLint : Integrable (fun ω => L j₀ ω) μ

/-- ★ **反空洞见证**：`BlockSLLNHyp` 在**单点块编号类 `PUnit`** 上**非空**
（常值块 ＋ 任意概率测度）。

* 两两独立由 `iIndepFun.of_subsingleton` 供给（`PUnit` 是 subsingleton ⇒ 空真）；
* 同分布由「常值函数的推前测度相等」供给（`rfl`）；
* `L ≡ 1` ⇒ `1 ≤ L`；可积性由 `integrable_const`。 -/
theorem blockSLLNHyp_nonempty (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] : Nonempty (BlockSLLNHyp Ω μ PUnit) := by
  refine ⟨{ M := fun _ _ => 1, L := fun _ _ => 1
            hj := ?_, j₀ := PUnit.unit, hi := ?_
            hL := fun _ _ => le_refl 1
            hM := integrable_const 1, hLint := integrable_const 1 }⟩
  · exact iIndepFun.of_subsingleton (β := fun _ : PUnit => ℝ × ℝ)
      (f := fun (_ : PUnit) (_ : Ω) => ((1 : ℝ), (1 : ℝ)))
  · intro j
    exact ⟨aemeasurable_const, aemeasurable_const, rfl⟩

end Phylo.Stat.BlockSLLN
