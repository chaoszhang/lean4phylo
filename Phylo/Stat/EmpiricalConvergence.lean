/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.Stat.MSC
import Mathlib.Probability.StrongLaw

/-!
# `Phylo.Stat.EmpiricalConvergence` —— 大数定律 ⇒ 经验 quartet 频率的**几乎必然**收敛

## 1. 背景与界线（公理化的大数定律 vs 概率论）

`Phylo/Stat/MSC.lean` 把「MSC 采样 + 大数定律」公理化为 `MSCSampling.converges`，
形状是**确定性**的

```text
∀ m ε > 0, ∃ N, ∀ n ≥ N, FreqClose (emp m n) m.freq ε
```

这个形状**没有概率空间**，所以不能由概率论「证」出来。本文件**不修改** `MSC.lean`，
而是**新增**一条**真概率陈述**：在概率空间 `(ℕ → Ω₀, μ)` 上，**iid 位点**使经验 quartet
频率**几乎必然**收敛到理论频率。

## 2. 用的是哪条大数定律（**文件 + 声明名**）

* `Mathlib/Probability/StrongLaw.lean` 第 **786** 行声明的
  **`ProbabilityTheory.strong_law_ae`**（**Etemadi 版强大数定律**）：

  ```text
  theorem strong_law_ae (X : ℕ → Ω → E) (hint : Integrable (X 0) μ)
      (hindep : Pairwise ((· ⟂ᵢ[μ] ·) on X))
      (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) :
      ∀ᵐ ω ∂μ, Tendsto (fun n ↦ (n : ℝ)⁻¹ • (∑ i ∈ range n, X i ω)) atTop (𝓝 μ[X 0])
  ```

  它只要求**两两独立**（Etemadi 的加强）+ **同分布** + `Integrable (X 0) μ`
  （⚠️ 该定理 **`omit [IsProbabilityMeasure μ]`**：它自己从可积 + 独立推出概率性）。
  本文件**直接用它** ⇒ 交付的是**几乎必然**收敛（`∀ᵐ ω ∂μ`），
  **不是**「依概率」，**更不是**确定性 `∃ N`。
* 同一文件的 `strong_law_ae_real`（第 **597** 行）是它的一维（`ℝ` 值）版本，
  用的是同一个 `Pairwise` 独立性假设。

## 3. iid 是**假设**，不是**构造**（逐条说明）

本版 Mathlib **没有**无限乘积测度（`Measure.infinitePi` / Kolmogorov 扩张搜索无结果，
见缺口 K），故本文件**没有构造** iid 概率空间，而把下面几条**逐条列为假设**：

| 条目 | 内容 | 在本文件中的身份 |
|---|---|---|
| 可测性 | `AEMeasurable (fun ω => ind (ω i) S hS q) μ` | **由 `IdentDistrib` 结构自带**（`hident` 的字段），不需单独假设 |
| 独立性 | `iIndepFun (fun i ω => ind (ω i) S hS q) μ`（⇒ 两两独立） | **假设** `hindep`（⚠️ 比 SLLN 所需的**两两**独立更强：这是**保守**选择） |
| 同分布 | `IdentDistrib (X i) (X 0) μ μ` | **假设** `hident` |
| 可积性 | `Integrable (fun ω => ind (ω 0) S hS q) μ` | **假设** `hint` |
| 分布 = MSC 理论频率 | `∫ ω, ind (ω 0) S hS q ∂μ = m.freq.p S hS q` | **假设** `hmean` |
| 0/1 取值（只在方差一节用） | `∀ x, ind x S hS q = 0 ∨ ind x S hS q = 1` | **假设** `hind` |

⇒ 「位点观测的分布恰是 MSC 的理论分布」这一步**没有被形式化**（它需要 MSC 的**测度层**
定义，本库没有；见 `Phylo/Stat/MSCProof.lean` 的诚实边界表）。本文件证明的是**大数定律
这一步**：给定 iid + 正确的边缘期望，经验频率几乎必然收敛 —— 这一步是**真正由概率论推出**的。

## 4. 交付（全部零 `sorry` / 零 `axiom`）

* `empFreq` —— 经验 quartet 频率（`n` 个位点的指示值平均）；
* ★★★ `empFreq_tendsto_ae` —— **几乎必然**收敛（用 `strong_law_ae`）；
* ★★ `empFreq_eventually_close_ae` —— 上面那条的「最终 `ε`-接近」a.e. 形式
  （即 `MSCSampling.converges` 的**概率版**：`∀ᵐ ω, ∀ ε > 0, ∃ N, ∀ n ≥ N, |empFreq n ω − p| < ε`）；
* ★★ `integral_empFreq` —— **无偏性** `∫ empFreq n = p`（`n ≥ 1`；**不需要独立性**）；
* ★★ `integral_sq_sub_of_zero_one` —— 单个 `{0,1}` 值随机变量的**方差**：
  `∫ (Y − E Y)² = E Y · (1 − E Y)`；
* ★★ `integral_sq_sub_empFreq_one` —— **`n = 1` 的方差** `∫ (empFreq 1 − p)² = p(1−p) = p(1−p)/1`。

## 5. 诚实边界（逐条）

| 条目 | 状态 |
|---|---|
| iid **假设下**的**几乎必然**大数定律 | ✅ **已证**（`empFreq_tendsto_ae`，用 `ProbabilityTheory.strong_law_ae`） |
| 上述的「最终 `ε`-接近」a.e. 形式 | ✅ **已证**（`empFreq_eventually_close_ae`） |
| **无偏性** `∫ empFreq n = m.freq.p`（`n ≥ 1`） | ✅ **已证**（`integral_empFreq`；只用同分布 + 可积，**不用独立性**） |
| `{0,1}` 值随机变量的方差恒等式 | ✅ **已证**（`integral_sq_sub_of_zero_one`） |
| **`n = 1` 的经验频率方差** `= p(1−p)/1` | ✅ **已证**（`integral_sq_sub_empFreq_one`） |
| **一般 `n` 的方差** `∫ (empFreq n − p)² = p(1−p)/n` | ❌ **未证**（缺口 V：需要双重和 + 独立性交叉项展开，`Mathlib` 本版**没有** `variance_sum` / `evariance_sum`） |
| **iid 概率空间的存在性**（Kolmogorov 扩张 / 无限乘积测度） | ❌ **未构造**（缺口 K；本版 Mathlib 无 `Measure.infinitePi`） |
| 「位点观测的边缘分布 = MSC 理论频率」 | ⚠️ **是假设**（`hmean`），**不是**证出来的（MSC 的测度层定义不在本库） |
| 「独立性、同分布」 | ⚠️ **是假设**（`hindep` / `hident`），**不是**证出来的 |
| `MSCSampling.converges`（既有公理） | ⚠️ **仍是公理化的**；本文件的 a.e. 形式是它的**概率版**，但**不是**它的推论（后者是确定性的 `∃ N`，没有概率空间） |
| 依概率（`TendstoInMeasure`）形式 | ❌ **未单独陈述**（a.s. 更强；由 `strong_law_Lp` + `tendstoInMeasure_of_tendsto_ae` 可得，本文件未做） |
| `n = 0` | ⚠️ `empFreq 0 = 0`（约定 `0⁻¹ = 0`）；大数定律是 `atTop` 陈述，不受影响 |

### 缺口的确切内容（全文零 `sorry` / 零 `axiom`）

* **缺口 K** —— `kolmogorov_extension_gap`：可数无限乘积概率空间的存在性
  （坐标 iid、边缘 = `μ₀`）。本版 Mathlib 无此设施，故 iid 只能作为假设。
* **缺口 V** —— `variance_empFreq_gap`：一般 `n` 的均方误差 `= p(1−p)/n`。
  缺的不是「展开代数」，而是 Lean 侧的记账：`∫ (∑ᵢ Xᵢ)²` 的双重和
  （对角项 `∫ Xᵢ² = ∫ Xᵢ`，非对角项 `∫ XᵢXⱼ = (∫Xᵢ)(∫Xⱼ)` 依赖独立性）。
-/

open Filter MeasureTheory ProbabilityTheory

open scoped Topology

namespace Phylo.Stat.EmpiricalConvergence

variable {X : Type*} [Fintype X] [DecidableEq X]
variable {Ω₀ : Type*} [MeasurableSpace Ω₀]

/-- **位点观测函数**：`ind x S hS q` 是「位点结果为 `x` 时，在 4-元集 `S` 上展示
（有向）split `q`」的指示值。⚠️ 本文件只把 `ind` 当作**给定的**函数，
不构造它的分布（见文件头 §3）。 -/
abbrev SiteFun (X : Type*) [Fintype X] [DecidableEq X] (Ω₀ : Type*) [MeasurableSpace Ω₀] : Type _ :=
  Ω₀ → (S : Finset X) → (S.card = 4) → Split ↥S → ℝ

variable (ind : SiteFun X Ω₀)

/-- 经验 quartet 频率：`n` 个 iid 位点的指示函数平均
（`ω : ℕ → Ω₀` 是位点结果序列，`ω i` 是第 `i` 个位点的结果）。 -/
noncomputable def empFreq (n : ℕ) (ω : ℕ → Ω₀) (S : Finset X) (hS : S.card = 4)
    (q : Split ↥S) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, ind (ω i) S hS q

/-- 空样本：`empFreq 0 = 0`（约定 `(0 : ℝ)⁻¹ = 0`）。 -/
theorem empFreq_zero (ω : ℕ → Ω₀) (S : Finset X) (hS : S.card = 4) (q : Split ↥S) :
    empFreq ind 0 ω S hS q = 0 := by
  simp [empFreq]

/-- 单样本：`empFreq 1 ω = ind (ω 0)`。 -/
theorem empFreq_one (ω : ℕ → Ω₀) (S : Finset X) (hS : S.card = 4) (q : Split ↥S) :
    empFreq ind 1 ω S hS q = ind (ω 0) S hS q := by
  simp [empFreq]

/-! ## 1. ★★★ 大数定律（**几乎必然**） -/

/-- ★★★ **大数定律（几乎必然）**：`n` 个 iid 位点的经验 quartet 频率
**几乎必然**收敛到 MSC 理论频率 `m.freq.p S hS q`。

证明 = `ProbabilityTheory.strong_law_ae`（Etemadi 版强大数定律，
`Mathlib/Probability/StrongLaw.lean` 第 786 行）作用在
`X i := fun ω => ind (ω i) S hS q` 上：由 `hindep` 得两两独立，由 `hident` 得同分布，
由 `hint` 得可积，由 `hmean` 把 `μ[X 0]` 认成 `m.freq.p S hS q`。

⚠️ 本定理**没有**证明「位点 iid 且其分布是 MSC 分布」——那是**假设**（文件头 §3）。 -/
theorem empFreq_tendsto_ae (m : MSCFreq X) (μ : Measure (ℕ → Ω₀)) [IsProbabilityMeasure μ]
    (S : Finset X) (hS : S.card = 4) (q : Split ↥S)
    (hint : Integrable (fun ω : ℕ → Ω₀ => ind (ω 0) S hS q) μ)
    (hindep : iIndepFun (fun i (ω : ℕ → Ω₀) => ind (ω i) S hS q) μ)
    (hident : ∀ i, IdentDistrib (fun ω : ℕ → Ω₀ => ind (ω i) S hS q)
      (fun ω : ℕ → Ω₀ => ind (ω 0) S hS q) μ μ)
    (hmean : ∫ ω, ind (ω 0) S hS q ∂μ = m.freq.p S hS q) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => empFreq ind n ω S hS q) atTop (𝓝 (m.freq.p S hS q)) := by
  have h := strong_law_ae (μ := μ) (E := ℝ)
    (fun i (ω : ℕ → Ω₀) => ind (ω i) S hS q) hint
    (fun i j hij => hindep.indepFun hij) hident
  filter_upwards [h] with ω hω
  have hω' : Tendsto (fun n => empFreq ind n ω S hS q) atTop
      (𝓝 (∫ ω, ind (ω 0) S hS q ∂μ)) := by
    simpa only [empFreq, smul_eq_mul] using hω
  rwa [hmean] at hω'

/-- ★★ **大数定律的「最终 `ε`-接近」a.e. 形式**（= `MSCSampling.converges` 的**概率版**）：

几乎必然地，对一切 `ε > 0` 都存在 `N`，使 `n ≥ N` 时经验频率与理论频率 `ε`-接近。

⚠️ 与 `MSCSampling.converges` 的区别：那里是**确定性**的 `∃ N, ∀ n ≥ N, …`（对**所有**样本），
这里是 **`μ`-几乎必然**的（对 a.e. `ω`）。两者不可互换：前者没有概率空间，**不是**本定理的推论。 -/
theorem empFreq_eventually_close_ae (m : MSCFreq X) (μ : Measure (ℕ → Ω₀))
    [IsProbabilityMeasure μ] (S : Finset X) (hS : S.card = 4) (q : Split ↥S)
    (hint : Integrable (fun ω : ℕ → Ω₀ => ind (ω 0) S hS q) μ)
    (hindep : iIndepFun (fun i (ω : ℕ → Ω₀) => ind (ω i) S hS q) μ)
    (hident : ∀ i, IdentDistrib (fun ω : ℕ → Ω₀ => ind (ω i) S hS q)
      (fun ω : ℕ → Ω₀ => ind (ω 0) S hS q) μ μ)
    (hmean : ∫ ω, ind (ω 0) S hS q ∂μ = m.freq.p S hS q) :
    ∀ᵐ ω ∂μ, ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ n ≥ N, |empFreq ind n ω S hS q - m.freq.p S hS q| < ε := by
  filter_upwards [empFreq_tendsto_ae ind m μ S hS q hint hindep hident hmean] with ω hω
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hω ε hε
  -- `dist x y` 与 `|x − y|` 对 `ℝ` 是**定义相等**的（`Real.dist_eq` 是 `rfl`），故无需改写
  exact ⟨N, fun n hn => hN n hn⟩

/-! ## 2. ★★ 无偏性（**不需要独立性**） -/

/-- ★★ **无偏性**：`∫ ω, empFreq ind n ω ∂μ = m.freq.p S hS q`（`n ≠ 0`）。

⚠️ 这里只用到**同分布**（`hident`）+ **可积**（`hint`）+ **边缘期望**（`hmean`），
**没有**用到独立性 —— 独立性只在方差（缺口 V）里才需要。 -/
theorem integral_empFreq (m : MSCFreq X) (μ : Measure (ℕ → Ω₀)) [IsProbabilityMeasure μ]
    (S : Finset X) (hS : S.card = 4) (q : Split ↥S)
    (hint : Integrable (fun ω : ℕ → Ω₀ => ind (ω 0) S hS q) μ)
    (hident : ∀ i, IdentDistrib (fun ω : ℕ → Ω₀ => ind (ω i) S hS q)
      (fun ω : ℕ → Ω₀ => ind (ω 0) S hS q) μ μ)
    (hmean : ∫ ω, ind (ω 0) S hS q ∂μ = m.freq.p S hS q) {n : ℕ} (hn : n ≠ 0) :
    ∫ ω, empFreq ind n ω S hS q ∂μ = m.freq.p S hS q := by
  have hX : ∀ i, Integrable (fun ω : ℕ → Ω₀ => ind (ω i) S hS q) μ :=
    fun i => (hident i).symm.integrable_snd hint
  have hInt : ∀ i, ∫ ω, ind (ω i) S hS q ∂μ = m.freq.p S hS q :=
    fun i => by rw [(hident i).integral_eq, hmean]
  simp only [empFreq]
  rw [integral_const_mul, integral_finsetSum (Finset.range n) (fun i _ => hX i),
    Finset.sum_congr rfl (fun i _ => hInt i), Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hn), one_mul]

/-! ## 3. ★★ 方差：`{0,1}` 值随机变量的恒等式与 `n = 1` 实例 -/

/-- ★★ **`{0,1}` 值随机变量的方差恒等式**：若 `Y` 可积且逐点取值 `0` 或 `1`，则
`∫ (Y − E Y)² = E Y · (1 − E Y)`（即 `Var Y = P(Y=1)·(1 − P(Y=1))`）。
证明只用 `Y² = Y` 与积分的线性（**不需要独立性**）。 -/
theorem integral_sq_sub_of_zero_one {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {Y : Ω → ℝ} (hY : Integrable Y μ)
    (h01 : ∀ ω, Y ω = 0 ∨ Y ω = 1) :
    ∫ ω, (Y ω - ∫ ω, Y ω ∂μ) ^ 2 ∂μ = (∫ ω, Y ω ∂μ) * (1 - ∫ ω, Y ω ∂μ) := by
  set e := ∫ ω, Y ω ∂μ with he
  have hsq : ∀ ω, (Y ω - e) ^ 2 = Y ω * (1 - 2 * e) + e ^ 2 := by
    intro ω
    rcases h01 ω with h | h <;> rw [h] <;> ring
  rw [show (fun ω => (Y ω - e) ^ 2) = fun ω => Y ω * (1 - 2 * e) + e ^ 2 from funext hsq]
  rw [integral_add (hY.mul_const _) (integrable_const _), integral_mul_const, ← he,
    integral_const, Measure.real, measure_univ, ENNReal.toReal_one, one_smul]
  ring

/-- ★★ **`n = 1` 的经验频率方差**：`∫ (empFreq 1 − p)² = p(1 − p) = p(1−p)/1`
（`integral_sq_sub_of_zero_one` 用在 `empFreq 1 = ind (ω 0)` 上）。 -/
theorem integral_sq_sub_empFreq_one (m : MSCFreq X) (μ : Measure (ℕ → Ω₀))
    [IsProbabilityMeasure μ] (S : Finset X) (hS : S.card = 4) (q : Split ↥S)
    (hind : ∀ x : Ω₀, ind x S hS q = 0 ∨ ind x S hS q = 1)
    (hint : Integrable (fun ω : ℕ → Ω₀ => ind (ω 0) S hS q) μ)
    (hmean : ∫ ω, ind (ω 0) S hS q ∂μ = m.freq.p S hS q) :
    ∫ ω, (empFreq ind 1 ω S hS q - m.freq.p S hS q) ^ 2 ∂μ
      = m.freq.p S hS q * (1 - m.freq.p S hS q) / 1 := by
  have hfun : (fun ω : ℕ → Ω₀ => (empFreq ind 1 ω S hS q - m.freq.p S hS q) ^ 2)
      = fun ω : ℕ → Ω₀ => (ind (ω 0) S hS q - ∫ ω, ind (ω 0) S hS q ∂μ) ^ 2 := by
    funext ω
    rw [empFreq_one, hmean]
  rw [hfun, integral_sq_sub_of_zero_one (Y := fun ω : ℕ → Ω₀ => ind (ω 0) S hS q) hint
    (fun ω => hind (ω 0)), hmean]
  ring

/-! ## 4. 诚实边界：显式缺口（`def … : Prop`，**不是** `axiom`，也**不是** `sorry`）

下面两条把本文件**没有**做到的东西写成显式命题（规格 §10.3 的要求：宁可留缺口，
不许把未证内容伪装成定理）。它们在本文件中**从未被当作假设使用**。 -/

/-- ❌ **缺口 K（Kolmogorov 扩张 / 无限乘积测度）**：对任意概率测度 `μ₀`，存在
`μ : Measure (ℕ → Ω₀)`，使坐标映射 `ω ↦ ω i` 在 `μ` 下**独立**且每个坐标的边缘恰为 `μ₀`。

**未构造**：本版 Mathlib 没有可数无限乘积测度（`Measure.infinitePi` 不存在）。
把「位点 iid」写成**假设**的根源就在这里：有了本缺口，「iid 位点概率空间」才是可构造的，
`empFreq_tendsto_ae` 的 `hindep` / `hident` 才不必再假设。

⚠️ 诚实说明：对**任意**可测空间 `Ω₀`，可数乘积上 iid 测度的存在性还需额外条件
（如 `Ω₀` 为**标准 Borel / 完美测度**空间）；本 `Prop` 是**最简形式**的存在性陈述，
其充分条件**未**在此讨论。**未证。** -/
def kolmogorov_extension_gap (μ₀ : Measure Ω₀) [IsProbabilityMeasure μ₀] : Prop :=
  ∃ μ : Measure (ℕ → Ω₀), IsProbabilityMeasure μ ∧
    (∀ i : ℕ, Measure.map (fun ω : ℕ → Ω₀ => ω i) μ = μ₀) ∧
    iIndepFun (fun i (ω : ℕ → Ω₀) => ω i) μ

/-- ❌ **缺口 V（一般 `n` 的均方误差 / 方差）**：iid 位点、`ind` 逐点取值 `0/1`、
且 `∫ ind (ω 0) = m.freq.p S hS q` 时

```text
∫ ω, (empFreq n ω − m.freq.p S hS q)² ∂μ = m.freq.p S hS q · (1 − m.freq.p S hS q) / n     (n ≥ 1)
```

**未证**：缺的不是代数（`n = 1` 已在 `integral_sq_sub_empFreq_one` 证出），
而是 Lean 侧的双重和记账：把 `(∑ᵢ Xᵢ)²` 展开成 `∑ᵢ∑ⱼ XᵢXⱼ`，
对角项用 `Xᵢ² = Xᵢ`、非对角项用独立性 `∫XᵢXⱼ = (∫Xᵢ)(∫Xⱼ)`；
本版 Mathlib **没有** `variance_sum` / `evariance_sum` 现成引理（见文件头 §5）。**未证。** -/
def variance_empFreq_gap (m : MSCFreq X) (μ : Measure (ℕ → Ω₀)) [IsProbabilityMeasure μ]
    (S : Finset X) (hS : S.card = 4) (q : Split ↥S) : Prop :=
  (∀ x : Ω₀, ind x S hS q = 0 ∨ ind x S hS q = 1) →
  Integrable (fun ω : ℕ → Ω₀ => ind (ω 0) S hS q) μ →
  iIndepFun (fun i (ω : ℕ → Ω₀) => ind (ω i) S hS q) μ →
  (∀ i, IdentDistrib (fun ω : ℕ → Ω₀ => ind (ω i) S hS q)
    (fun ω : ℕ → Ω₀ => ind (ω 0) S hS q) μ μ) →
  (∫ ω, ind (ω 0) S hS q ∂μ = m.freq.p S hS q) →
  ∀ n : ℕ, 0 < n →
    ∫ ω, (empFreq ind n ω S hS q - m.freq.p S hS q) ^ 2 ∂μ
      = m.freq.p S hS q * (1 - m.freq.p S hS q) / n

end Phylo.Stat.EmpiricalConvergence
