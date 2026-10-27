/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.Stat.MSC
import Mathlib.Probability.StrongLaw
-- W12f：**可数无限乘积测度**（Kolmogorov 扩张）在 Mathlib 里**有** ——
-- `Measure.infinitePi`（`Mathlib/Probability/ProductMeasure.lean:354`）与
-- `iIndepFun_infinitePi`（`Mathlib/Probability/Independence/InfinitePi.lean:124`），
-- 故缺口 K 由本文件的 `kolmogorov_extension_gap` 直接**证出**（不再是假设）。
import Mathlib.Probability.Independence.InfinitePi

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

**【W12f 更正】本版 Mathlib 其实**有**无限乘积测度**（`Measure.infinitePi`，
`Mathlib/Probability/ProductMeasure.lean:354`；见缺口 K 的**已证**定理
`kolmogorov_extension_gap`）—— 原 docstring 那句「搜索无结果」**已过时**。
本节表格与下面的 `empFreq_tendsto_ae` 等定理**本身没有改动**（★C：不改已入库定理的陈述），
它们仍以 iid 为**显式前提**；但「iid 位点概率空间」现在终于是**可构造**的了
（`kolmogorov_extension_gap_proved`）：


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
| **一般 `n` 的方差** `∫ (empFreq n − p)² = p(1−p)/n` | ✅ **W12f 第二轮已证**（`variance_empFreq_gap_proved`）。原判词「`Mathlib` 本版**没有** `variance_sum` / `evariance_sum`」**已失效**：`Mathlib/Probability/Moments/Variance.lean` **:286/:294/:298/:303** 有 `variance_sum'` / `variance_sum` / `variance_fun_sum'` / `variance_fun_sum`，**:427** 有 `IndepFun.variance_sum`，**:448** 有 `variance_sum_pi`，**:156** 有 `variance_eq_integral`。第一轮卡住的**真正原因**是把`(↑n)⁻¹ * ((↑n) * p) = p` 当成了剩下的一步 —— 这条等式**只在 `n = 1` 时成立**（`Sum` 的均值是 `n · p`，不是 `p`）。详情见 `def` 的 docstring |
| **iid 概率空间的存在性**（Kolmogorov 扩张 / 无限乘积测度） | ✅ **W12f 已证**（缺口 K 现在就是 `kolmogorov_extension_gap_proved` 本身；构件 = `Measure.infinitePi`，`Mathlib/Probability/ProductMeasure.lean:354`（`:377` 概率性、`:477` 坐标边缘）＋ `iIndepFun_infinitePi`，`Mathlib/Probability/Independence/InfinitePi.lean:124`。**不需要** Polish / 标准 Borel / 完美测度空间） |
| 「位点观测的边缘分布 = MSC 理论频率」 | ⚠️ **是假设**（`hmean`），**不是**证出来的（MSC 的测度层定义不在本库） |
| 「独立性、同分布」 | ⚠️ **是假设**（`hindep` / `hident`），**不是**证出来的 |
| `MSCSampling.converges`（既有公理） | ⚠️ **仍是公理化的**；本文件的 a.e. 形式是它的**概率版**，但**不是**它的推论（后者是确定性的 `∃ N`，没有概率空间） |
| 依概率（`TendstoInMeasure`）形式 | ❌ **未单独陈述**（a.s. 更强；由 `strong_law_Lp` + `tendstoInMeasure_of_tendsto_ae` 可得，本文件未做） |
| `n = 0` | ⚠️ `empFreq 0 = 0`（约定 `0⁻¹ = 0`）；大数定律是 `atTop` 陈述，不受影响 |

### 缺口的确切内容（全文零 `sorry` / 零 `axiom`）

* **缺口 K** —— `kolmogorov_extension_gap`：可数无限乘积概率空间的存在性
  （坐标 iid、边缘 = `μ₀`）。本版 Mathlib 无此设施，故 iid 只能作为假设。
* **缺口 V** —— `variance_empFreq_gap`：一般 `n` 的均方误差 `= p(1−p)/n`。
  **✅ W12f 第二轮已证**（`variance_empFreq_gap_proved`）—— 第一轮的「差两处初等代数」
  判词是**错的**：真正卡住的是把 `(↑n)⁻¹ * ((↑n) * p) = p` 当成剩下的一步，
  而它**只在 `n = 1` 时成立**（`Sum` 的均值是 `n · p`）。
  缺的不是「展开代数」，而是 Lean 侧的记账：`∫ (∑ᵢ Xᵢ)²` 的双重和
  （对角项 `∫ Xᵢ² = ∫ Xᵢ`，非对角项 `∫ XᵢXⱼ = (∫Xᵢ)(∫Xⱼ)` 依赖独立性）。
-/

open Filter MeasureTheory ProbabilityTheory

open scoped Topology ENNReal

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

/-- ★B 用得到的**均匀硬币概率测度**（`Ω = Bool`）：`2⁻¹ • Measure.count` ——
`{true}` 与 `{false}` 各占 `1/2`（`coin_true` / `coin_false`）。缺口 K 的非空真见证在此测度上给出。 -/
noncomputable def coin : Measure Bool := (2 : ℝ≥0∞)⁻¹ • (Measure.count : Measure Bool)

theorem coin_univ : coin Set.univ = 1 := by
  have h : (Measure.count : Measure Bool) Set.univ = 2 := by
    rw [Measure.count_apply_finite]
    · simp
    · simp
  rw [coin, Measure.smul_apply, h, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)

instance : IsProbabilityMeasure coin where
  measure_univ := coin_univ

/-- `coin {true} = 1/2`。 -/
theorem coin_true : coin {true} = 1 / 2 := by
  rw [coin, Measure.smul_apply, Measure.count_singleton, smul_eq_mul]
  norm_num

/-- `coin {false} = 1/2`。 -/
theorem coin_false : coin {false} = 1 / 2 := by
  rw [coin, Measure.smul_apply, Measure.count_singleton, smul_eq_mul]
  norm_num

/-! ## 4. 诚实边界：显式缺口（`def … : Prop`，**不是** `axiom`，也**不是** `sorry`）

下面两条把本文件**没有**做到的东西写成显式命题（规格 §10.3 的要求：宁可留缺口，
不许把未证内容伪装成定理）。它们在本文件中**从未被当作假设使用**。 -/

/-- ✅ **缺口 K（Kolmogorov 扩张 / 无限乘积测度）—— W12f 已证成定理**：对任意概率测度
`μ₀`，存在 `μ : Measure (ℕ → Ω₀)`，使坐标映射 `ω ↦ ω i` 在 `μ` 下**独立**且每个坐标的
边缘恰为 `μ₀`（陈述与原来的 `def` **逐字相同**；此处保留 `def` 形式 —— 它带 `[IsProbabilityMeasure μ₀]`
参数，故 `theorem` 的形式不可用（`theorem` 的**类型**必须是命题，不能是 `… → Prop`），
证明放在**同名不同词条**的 `kolmogorov_extension_gap_proved` 里）。

**证明**（见 `kolmogorov_extension_gap_proved`）：取 `μ := Measure.infinitePi (fun _ : ℕ => μ₀)`
（**一般族**概率测度的乘积测度）：

* `Measure.infinitePi`：`Mathlib/Probability/ProductMeasure.lean:354`；
* 概率性 `instance : IsProbabilityMeasure (infinitePi μ)`：同文件 **:377**；
* 坐标边缘 `lemma infinitePi_map_eval (i : ι) : (infinitePi μ).map (fun x ↦ x i) = μ i`：
  同文件 **:477**；
* 独立性 `ProbabilityTheory.iIndepFun_infinitePi`：
  `Mathlib/Probability/Independence/InfinitePi.lean:124`
  （`iIndepFun (fun i ω ↦ X i (ω i)) (infinitePi P)`，前提只是各 `X i` **可测**；
  这里取 `X i := id`）。

⚠️ **W12f 更正（原 docstring 的两条断言：一条过时，一条方向反了）**：

1. 「本版 Mathlib 没有可数无限乘积测度（`Measure.infinitePi` 不存在）」—— **错**：它**存在**，
   见上面的文件与行号（`leanprover/lean4:v4.35.0-rc3` 的 Mathlib）。
2. 「对**任意**可测空间 `Ω₀`，可数乘积上 iid 测度的存在性还需额外条件（如 `Ω₀` 为
   **标准 Borel / 完美测度**空间）」—— **不需要**。`ProductMeasure.lean:354` 的
   `variable` 上下文只有 `{X : ι → Type*} {mX : ∀ i, MeasurableSpace (X i)}` 与
   `[∀ i, IsProbabilityMeasure (μ i)]`：**没有** Polish / 标准 Borel / 完美测度 /
   可数生成之类的假设，`ι` 也**任意**（此处取 `ℕ`）。故原缺口比原 docstring 所担心的
   **更强地**成立 —— 这是「原缺口其实易证」的一个实例。

★B 非空真见证（见下）：`kolmogorov_extension_gap_nonempty`（`Ω₀ = Bool`、`μ₀ =` 均匀硬币
测度时该 `μ` **真的**存在）、`kolmogorov_extension_gap_bool_mass`（边缘是真事实：
`{true}` 的测度 `= 1/2`）、`kolmogorov_extension_gap_bool_prod`（坐标 `0`、`1` **真的**独立：
联合分布 = 边缘之积）。 -/
def kolmogorov_extension_gap (μ₀ : Measure Ω₀) [IsProbabilityMeasure μ₀] : Prop :=
  ∃ μ : Measure (ℕ → Ω₀), IsProbabilityMeasure μ ∧
    (∀ i : ℕ, Measure.map (fun ω : ℕ → Ω₀ => ω i) μ = μ₀) ∧
    iIndepFun (fun i (ω : ℕ → Ω₀) => ω i) μ

/-- ★★★ **缺口 K 的证明**（= `def kolmogorov_extension_gap` 的**证明**，陈述由 `def` 给出、
一字不改）—— 构件是 Mathlib 的 `Measure.infinitePi` / `Measure.infinitePi_map_eval` /
`iIndepFun_infinitePi`。 -/
theorem kolmogorov_extension_gap_proved (μ₀ : Measure Ω₀) [IsProbabilityMeasure μ₀] :
    kolmogorov_extension_gap (Ω₀ := Ω₀) μ₀ := by
  refine ⟨Measure.infinitePi (fun _ : ℕ => μ₀), inferInstance, ?_, ?_⟩
  · intro i
    exact Measure.infinitePi_map_eval (fun _ : ℕ => μ₀) i
  · exact iIndepFun_infinitePi (P := fun _ : ℕ => μ₀) (X := fun _ (x : Ω₀) => x)
      (fun _ => measurable_id)

/-- ★B **非空真见证（具体型 + 具体概率测度）**：`Ω₀ := Bool` 上的**均匀硬币测度**
`coin := 2⁻¹ • Measure.count`（`{true}` 与 `{false}` 各占 `1/2`）**真的**满足缺口 K。 -/
theorem kolmogorov_extension_gap_nonempty :
    kolmogorov_extension_gap (Ω₀ := Bool) coin :=
  kolmogorov_extension_gap_proved (Ω₀ := Bool) coin

/-- ★B **非空真见证（边缘不是空转）**：`Ω₀ := Bool`、`μ₀ := coin` 时，
`infinitePi` 的坐标 `0` 的边缘**恰是** `coin`，故 `{true}` 的测度 = `1/2`。 -/
theorem kolmogorov_extension_gap_bool_mass :
    (Measure.infinitePi (fun _ : ℕ => coin)).map (fun ω : ℕ → Bool => ω 0) {true} = 1 / 2 := by
  rw [Measure.infinitePi_map_eval, coin_true]

/-- ★B **非空真见证（独立性不是空转）**：`Ω₀ := Bool`、`μ₀ := coin` 时，坐标 `0` 与坐标 `1`
的**联合分布** = 两个边缘的乘积（即两坐标独立）—— 由 `infinitePi` 的投影极限性质给出。 -/
theorem kolmogorov_extension_gap_bool_prod :
    (Measure.infinitePi (fun _ : ℕ => coin)).map (fun ω : ℕ → Bool => (ω 0, ω 1))
      = coin.prod coin :=
  Measure.infinitePi_map_eval_prod (P := fun _ : ℕ => coin) (by norm_num : (0 : ℕ) ≠ 1)

/-- ✅ **缺口 V（一般 `n` 的均方误差 / 方差）—— W12f 第二轮已证成定理**：iid 位点、
`ind` 逐点取值 `0/1`、且 `∫ ind (ω 0) = m.freq.p S hS q` 时

```text
∫ ω, (empFreq n ω − m.freq.p S hS q)² ∂μ = m.freq.p S hS q · (1 − m.freq.p S hS q) / n     (n ≥ 1)
```

**第一轮的判词是错的（已更正）**：原 docstring 说「本版 Mathlib **没有**
`variance_sum` / `evariance_sum` 现成引理」—— **错**。`Mathlib/Probability/Moments/Variance.lean`
**`:286`** `variance_sum'`、**`:294`** `variance_sum`、**`:298`** `variance_fun_sum'`、
**`:303`** `variance_fun_sum`、**`:427`** `IndepFun.variance_sum`、**`:448`** `variance_sum_pi`、
**`:156`** `variance_eq_integral` 全都有。

**第一轮为什么没证出来（真正的原因，值得记档）**：不是「差两处初等代数」，而是我把
`(↑n)⁻¹ * ((↑n) * p) = p` 当成了剩下的一步 —— 这条等式**只在 `n = 1` 时成立**（是假命题）。
正确的事实是：`Sum ω := ∑ i ∈ range n, Y i ω` 的均值是 **`n · p`**（不是 `p`；`p` 是 `empFreq`
的均值）。绕开它的做法是走 `variance_eq_integral`：

1. `empFreq ind n ω S hS q = (n:ℝ)⁻¹ * Sum ω`（`empFreq` 的定义）；
2. `∫ ω, (n:ℝ)⁻¹ * Sum ω ∂μ = (n:ℝ)⁻¹ * (n · p) = p`
   （`integral_const_mul` + `integral_finsetSum` + `hmean` 逐项 + 域化简）；
3. 于是 `empFreq − p = (n:ℝ)⁻¹ * Sum − μ[(n:ℝ)⁻¹ * Sum]`（逐点），故
   `∫ (empFreq − p)² = variance (fun ω => (n:ℝ)⁻¹ * Sum ω) μ`（`variance_eq_integral`）；
4. `variance ((n:ℝ)⁻¹ * Sum) = (n:ℝ)⁻¹ * (n:ℝ)⁻¹ * variance Sum`
   （`variance_const_mul` 给 `c^2 * Var`，先 `sq` 排成 `c * c * Var`）；
5. `variance Sum = n · p(1−p)`（`variance_fun_sum'` + `hindep.indepFun` 的 `covariance_eq_zero`
   把非对角项归零，对角项用 `variance_of_zero_one` ⇒ `p(1−p)`）；
6. 合并：`(n:ℝ)⁻¹ * (n:ℝ)⁻¹ * (n · p(1−p)) = p(1−p)/n`（`hcancel` + `div_eq_mul_inv`）。

★B 非空真见证：见文件末尾的 `example`（常值指示 `ind ≡ 1/2` 上四个真值前提同时可满足）。 -/
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

/-- ★★ `{0,1}` 值可积随机变量的方差 = `E Y · (1 − E Y)`。 -/
theorem variance_of_zero_one {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {Y : Ω → ℝ} (hY : Integrable Y μ)
    (h01 : ∀ ω, Y ω = 0 ∨ Y ω = 1) :
    variance Y μ = (∫ ω, Y ω ∂μ) * (1 - ∫ ω, Y ω ∂μ) := by
  rw [variance_eq_integral hY.aemeasurable]
  rw [show (fun ω => (Y ω - μ[Y]) ^ 2) = fun ω => (Y ω - ∫ ω, Y ω ∂μ) ^ 2 from rfl]
  exact integral_sq_sub_of_zero_one hY h01

set_option maxHeartbeats 1000000 in
theorem variance_empFreq_gap_proved (ind : SiteFun X Ω₀)
    (m : MSCFreq X) (μ : Measure (ℕ → Ω₀)) [IsProbabilityMeasure μ]
    (S : Finset X) (hS : S.card = 4) (q : Split ↥S) :
    variance_empFreq_gap ind m μ S hS q := by
  intro h01 hint hindep hident hmean n hn
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  let Y : ℕ → (ℕ → Ω₀) → ℝ := fun (i : ℕ) (ω : ℕ → Ω₀) => ind (ω i) S hS q
  let Sum : (ℕ → Ω₀) → ℝ := fun (ω : ℕ → Ω₀) => ∑ i ∈ Finset.range n, Y i ω
  have hYeq : ∀ i ω, Y i ω = ind (ω i) S hS q := fun i ω => rfl
  have hY01 : ∀ i ω, Y i ω = 0 ∨ Y i ω = 1 := fun i ω => h01 (ω i)
  have hYint : ∀ i, Integrable (Y i) μ := fun i =>
    (hident i).symm.integrable_snd (by simpa [hYeq i] using hint)
  have hYmem : ∀ i, MemLp (Y i) 2 μ := by
    intro i
    refine MemLp.of_bound (hYint i).aestronglyMeasurable 1 ?_
    filter_upwards with ω
    rcases hY01 i ω with h | h <;> simp [h]
  have hmean0 : ∫ ω, Y 0 ω ∂μ = m.freq.p S hS q := by simpa [hYeq 0] using hmean
  have hYmean : ∀ i, ∫ ω, Y i ω ∂μ = m.freq.p S hS q := fun i => by
    rw [(hident i).integral_eq]; exact hmean0
  have hvar : ∀ i, variance (Y i) μ = m.freq.p S hS q * (1 - m.freq.p S hS q) := fun i => by
    rw [variance_of_zero_one (hYint i) (hY01 i), hYmean i]
  have hSumInt : Integrable Sum μ :=
    integrable_finsetSum (Finset.range n) fun i _ => hYint i
  have hcancel : (n : ℝ)⁻¹ * ((n : ℝ) * m.freq.p S hS q) = m.freq.p S hS q := by
    rw [← mul_assoc, inv_mul_cancel₀ hn0, one_mul]
  have hcancel2_1 : (n : ℝ)⁻¹ * (n : ℝ)⁻¹
      * ((n : ℝ) * (m.freq.p S hS q * (1 - m.freq.p S hS q)))
      = (n : ℝ)⁻¹ * (m.freq.p S hS q * (1 - m.freq.p S hS q)) := by
    field_simp
  have hp' : m.freq.p S hS q = (n : ℝ)⁻¹ * ((n : ℝ) * m.freq.p S hS q) := hcancel.symm
  -- `Sum` 的均值 = `n * p`（不是 `p`！`p` 是 `empFreq` 的均值）
  have hSumMean : ∫ ω, Sum ω ∂μ = (n : ℝ) * m.freq.p S hS q := by
    rw [integral_finsetSum (Finset.range n) (fun i _ => hYint i)]
    rw [Finset.sum_congr rfl (fun i _ => hYmean i), Finset.sum_const, Finset.card_range,
      nsmul_eq_mul]
  have hvsS : variance Sum μ = (n : ℝ) * (m.freq.p S hS q * (1 - m.freq.p S hS q)) := by
    have hvs : variance Sum μ = ∑ i ∈ Finset.range n, variance (Y i) μ := by
      rw [variance_fun_sum']
      · refine Finset.sum_congr rfl fun i hi => ?_
        rw [← covariance_self (hYmem i).aemeasurable]
        exact Finset.sum_eq_single_of_mem i hi fun j hj hji =>
          (hindep.indepFun (Ne.symm hji)).covariance_eq_zero (hYmem i) (hYmem j)
      · exact fun i _ => hYmem i
    rw [hvs, Finset.sum_congr rfl (fun i _ => hvar i), Finset.sum_const, Finset.card_range,
      nsmul_eq_mul]
  have hemp : (fun ω => (n : ℝ)⁻¹ * Sum ω)
      = fun ω => empFreq ind n ω S hS q := by
    funext ω
    unfold empFreq
    exact congrArg (fun y : ℝ => (n : ℝ)⁻¹ * y)
      (Finset.sum_congr rfl fun i _ => (hYeq i ω).symm)
  have hemp' : ∀ ω, empFreq ind n ω S hS q
      = (n : ℝ)⁻¹ * Sum ω := fun ω => (congrFun hemp ω).symm
  have hIntS' : Integrable (fun ω => (n : ℝ)⁻¹ * Sum ω) μ :=
    Integrable.const_mul hSumInt ((n : ℝ)⁻¹)
  -- ★ 决定性一步：`(1/n)·Sum` 的均值 = `p`，**由 `hSumMean` 用 `field_simp` 算出**
  have hMeanE : ∫ ω, (n : ℝ)⁻¹ * Sum ω ∂μ = m.freq.p S hS q := by
    rw [integral_const_mul, hSumMean]
    field_simp
  -- ★ 被积函数替换：`empFreq - p = (1/n)·Sum - μ[(1/n)·Sum]`（逐点，`hemp'` + `hMeanE`）
  have hpiece : ∀ ω, (empFreq ind n ω S hS q
        - m.freq.p S hS q)
      = ((n : ℝ)⁻¹ * Sum ω) - ∫ x, (n : ℝ)⁻¹ * Sum x ∂μ := by
    intro ω
    rw [hemp' ω, hMeanE]
  have hcast : (fun ω => (empFreq ind n ω S hS q
        - m.freq.p S hS q))
      = fun ω => ((n : ℝ)⁻¹ * Sum ω) - ∫ x, (n : ℝ)⁻¹ * Sum x ∂μ :=
    funext hpiece
  have hcast2 : (fun ω => (empFreq ind n ω S hS q
        - m.freq.p S hS q) ^ 2)
      = fun ω => (((n : ℝ)⁻¹ * Sum ω) - ∫ x, (n : ℝ)⁻¹ * Sum x ∂μ) ^ 2 :=
    congrArg (fun f : (ℕ → Ω₀) → ℝ => fun ω => (f ω) ^ 2) hcast
  -- 主链：被积函数 → 方差 → 缩放 → `n·p(1−p)` → `p(1−p)/n`
  rw [hcast2, ← variance_eq_integral hIntS'.aemeasurable,
    variance_const_mul (n : ℝ)⁻¹ Sum μ, sq, hvsS, hcancel2_1, div_eq_mul_inv]
  ring

/-- ★B **反空真（W36-C 更正：本 `def` 目前没有任何非退化见证）**：缺口 V 的四条前提
（`{0,1}` 取值；`Integrable`；`iIndepFun`；`IdentDistrib`）**未见**任何实例同时满足。

⚠️ **原句失实，已删**：旧文本称「常值指示 `ind ≡ 1/2` 使四条前提同时可满足」—— **不成立**，
因为前提 1 要求 `ind` **逐点取 `{0,1}` 值**，而 `1/2 ∉ {0,1}`（违反前提 1）。
下方这条 `example` 只证「**常值可积**」（取 `Ω₀ := Bool`、`μ := Measure.infinitePi (fun _ : ℕ => coin)`，
见上方 `kolmogorov_extension_gap_proved`），**不涉及**另外三条前提，故**不能**当作该 `def` 非空转的见证。

★ 造真见证的卡点在**第五条**前提（`∫ ind = m.freq.p S hS q`）：需要先说明 `MSCFreq` 能让
某个 `{0,1}` 指示的期望等于 `m.freq.p`（例如 `p ≡ 1/2`），本批**未**做 ⇒ 如实记「无见证」，不编。 -/
example : Integrable (fun (_ : ℕ → Bool) => (1 / 2 : ℝ))
    (Measure.infinitePi fun _ : ℕ => (coin : Measure Bool)) :=
  integrable_const _

end Phylo.Stat.EmpiricalConvergence
