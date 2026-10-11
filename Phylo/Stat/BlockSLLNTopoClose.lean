/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.Stat.BlockSLLN

/-!
# `Phylo.Stat.BlockSLLNTopoClose` —— **从块级 SLLN 到 `TopoClose` 形态的桥**（W13d 补件）

## 1. 为什么要单独一个文件

`Phylo/Stat/BlockSLLN.lean` 交付了 ★★★ `BlockSLLNIdx`：**逐指标**同时 a.e. 收敛。
而 CASTER 主线下一步（`CASTERTopo.topo_statisticallyConsistent`）吃的假设是 **`TopoClose` 形态**：

```
hconv : ∀ ε > 0, ∃ N, ∀ n ≥ N, TopoClose (emp n ω) W̃ ε
```

⇒ 本文件就是那座桥：`BlockSLLNIdx` ＋ **识别等式**（把极限认成 `W̃`）⇒ **`TopoClose` 形态的 a.e. 收敛**。
**不修改**任何已落盘声明（`TopoWeight` / `BlockSLLN.lean` / `CASTERTopo.lean` 一字未动）。

## 2. ★ 关键技术点（已记入 MEMORY）

库内 `CASTERTopo.TopoWeight X := (S : Finset X) → S.card = 4 → Topo → ℝ`
的**第二个参数是依赖证明项**。若把「指标」写成**内嵌 `hS` 的结构**（例如
`structure QuartetIdx where S : Finset X; hS : S.card = 4; T : Topo`），
则两组 `(S, hS, T)` 互相改写时必须同时改写**类型依赖**上的 `S`
⇒ `rw` / `subst` / `cases` **一律拒绝**（实测三种报错：
`motive is not type correct` / `invalid equality proof` / `Did not find an occurrence of the pattern`）。

**绕法（去依赖指标类型）**，三步：

1. **指标取 `QuartetKey X := Finset X × Topo`** —— **不内嵌 `hS`**（`Finset × Topo` 本身是 `Fintype`）；
2. 关于 `W̃` 与经验表的陈述**只量化 `(S, T)`**（`hS` 只在「需要它的那一处」作参数出现）；
3. `hS` 的差异由**证明无关性**（`Subsingleton.elim`，见 `siteWeight_subsingleton` /
   `empWeight_subsingleton`）消化。

## 3. 交付

| 声明 | 内容 |
|---|---|
| ★★ `siteWeight_subsingleton` / `empWeight_subsingleton` | 权重表 / 经验表在 `hS` 上的**证明无关性**（桥的支点） |
| ★★ `QuartetKey` ＋ `Fintype`/`Nonempty` 实例 | 去依赖的 quartet 指标（反空洞见证） |
| ★★★ `empWeight_tendsto_ae` | **`TopoClose` 形态的 a.e. 收敛**（本件验收判据） |
| ★★ `empWeight_eventually_close_ae` | 同一事实的 `∀ᵐ ω, ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ S hS T, …` 直写形态 |

## 4. 诚实边界

| 条目 | 状态 |
|---|---|
| 桥本身 | ✅ **已证**（本文件，零新公理） |
| **识别等式**（`hlim`） | ❌ **仍是假设**：把 `(Σ_(j<k) M_j)/(Σ_(j<k) L_j)` 的期望极限认成 `W̃` 在该坐标上的值，是 **W13c** 的产物 |
| **经验表由块级平均给出**（`hrep`，＝规格 §3.3 的换指标） | ⚠️ **仍是假设**：本文件不证 §3.3（见 `BlockSLLN.lean` 的诚实边界），只把它的**输出形状**接上来 |
| 块长上界 `L ≤ C` | ⚠️ 仍未被用到（与主定理一致） |
| `W̃` 的依赖形状 | ⚠️ 只支持**每个 `(S,T)` 一个期望极限** `W̃ (S,T)`（这正是库内 `TopoIdeal.W` 的形状 `W S hS T`）。若下游要写「同一 quartet 三个拓扑的权重和 = 1」这类**跨 `Topo` 的约束**，需另加假设 —— 本文件不含 |
| 反空洞 | ✅ `QuartetKey X` 有 `Nonempty` 实例 `quartetKey_nonempty`；桥的两个定理本身是定理（不新增 `structure`/`def : Prop`） |
-/

set_option autoImplicit false

noncomputable section

open Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal

namespace Phylo.Stat.BlockSLLNTopoClose

open Phylo.Stat.CASTERWeights
open Phylo.Stat.CASTERTopo
open Phylo.Stat.BlockSLLN (BlockSLLNIdx)

/-! ## 1. 去依赖的「quartet 指标」＋ 证明无关性支点 -/

/-- **去依赖的 quartet 指标**：`(S, T)`（**不内嵌** `hS : S.card = 4`）。
`hS` 由**假设**单独携带，因此不进入任何被索引对象的类型 ⇒ 不需要依赖改写。 -/
abbrev QuartetKey (X : Type*) : Type _ := Finset X × Topo

instance quartetKey_fintype (X : Type*) [Fintype X] : Fintype (QuartetKey X) :=
  inferInstance

instance quartetKey_nonempty (X : Type*) : Nonempty (QuartetKey X) :=
  ⟨(∅, Topo.ab_cd)⟩

/-- ★★ **支点：`hS` 上的证明无关性**（权重表版）。 -/
theorem siteWeight_subsingleton {X : Type*} [Fintype X] [DecidableEq X]
    (Wt : TopoWeight X) (S : Finset X) (h₁ h₂ : S.card = 4) (T : Topo) :
    Wt S h₁ T = Wt S h₂ T := by
  rw [Subsingleton.elim h₁ h₂]

/-- ★★ **支点：`hS` 上的证明无关性**（经验表版）。 -/
theorem empWeight_subsingleton {Ω : Type*} {X : Type*} [Fintype X] [DecidableEq X]
    (emp : ℕ → Ω → TopoWeight X) (n : ℕ) (ω : Ω) (S : Finset X)
    (h₁ h₂ : S.card = 4) (T : Topo) :
    emp n ω S h₁ T = emp n ω S h₂ T := by
  rw [Subsingleton.elim h₁ h₂]

/-! ## 2. ★★★ 桥：`BlockSLLNIdx` ⇒ `TopoClose` 形态的 a.e. 收敛 -/

/-- ★★★ **从块级 SLLN 到 `TopoClose` 形态的 a.e. 收敛**（本件验收判据）。

设

* `Wtilde : Finset X → Topo → ℝ`：**每个 `(S,T)` 一个期望极限** —— 这正是库内 `TopoIdeal.W`
  （`W S hS T`）的形状（对 `hS` 无实质依赖，仅因 `TopoWeight` 的定义才带该槽）；
* `emp : ℕ → Ω → TopoWeight X`：第 `n` 个样本的**经验权重表**；
* `Mf k j` / `Lf k j`：第 `k = (S,T)` 个 quartet 指标、第 `j` 块的总权重 / 位点数，满足
  ★★★ `BlockSLLNIdx` 的全部假设（块层两两独立 ＋ 同分布 ＋ `L ≥ 1` ＋ 可积）；
* `hlim`：**识别等式**（W13c 的产物）—— 第 `k` 个指标的块级平均之期望极限 `= Wtilde k.1 k.2`；
* `hrep`：经验表由块级平均给出（＝规格 §3.3 的换指标）。

则**几乎必然** `∀ ε > 0, ∃ N, ∀ n ≥ N, TopoClose (emp n ω) W̃ ε`，其中 `W̃ S _ T := Wtilde S T`。

⚠️ 全程**无需依赖改写**：所有陈述只量化 `(S,T)`；`hS` 只在 `hrep` 的左边出现一次，
由 `empWeight_subsingleton`（证明无关性）消化 —— 这就是内嵌 `hS` 的结构过不去、本绕法能过的原因。 -/
theorem empWeight_tendsto_ae {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Type*} [Fintype X] [DecidableEq X]
    (Wtilde : Finset X → Topo → ℝ) (emp : ℕ → Ω → TopoWeight X)
    {Mf Lf : QuartetKey X → ℕ → Ω → ℝ}
    (hjoint : ∀ k : QuartetKey X, iIndepFun (fun j ω => (Mf k j ω, Lf k j ω)) μ)
    (hident : ∀ (k : QuartetKey X) (j : ℕ),
      IdentDistrib (fun ω => (Mf k j ω, Lf k j ω)) (fun ω => (Mf k 0 ω, Lf k 0 ω)) μ μ)
    (hL1 : ∀ (k : QuartetKey X) (j : ℕ) (ω : Ω), (1 : ℝ) ≤ Lf k j ω)
    (hintM : ∀ k : QuartetKey X, Integrable (fun ω => Mf k 0 ω) μ)
    (hintL : ∀ k : QuartetKey X, Integrable (fun ω => Lf k 0 ω) μ)
    (hlim : ∀ k : QuartetKey X,
      (∫ ω, Mf k 0 ω ∂μ) / (∫ ω, Lf k 0 ω ∂μ) = Wtilde k.1 k.2)
    (hrep : ∀ (n : ℕ) (ω : Ω) (S : Finset X) (hS : S.card = 4) (T : Topo),
      emp n ω S hS T
        = (∑ j ∈ Finset.range n, Mf (S, T) j ω) / (∑ j ∈ Finset.range n, Lf (S, T) j ω)) :
    ∀ᵐ ω ∂μ, ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N,
      TopoClose (emp n ω) (fun S _ T => Wtilde S T) ε := by
  classical
  -- 逐指标同时 a.e. 收敛（`BlockSLLNIdx`，指标类取去依赖的 `QuartetKey X`）
  have hpt : ∀ᵐ ω ∂μ, ∀ k : QuartetKey X, Tendsto
      (fun n : ℕ => (∑ j ∈ Finset.range n, Mf k j ω) / (∑ j ∈ Finset.range n, Lf k j ω))
      atTop (𝓝 (Wtilde k.1 k.2)) :=
    BlockSLLNIdx (μ := μ) hjoint hident hL1 hintM hintL hlim
  filter_upwards [hpt] with ω hω
  intro ε hε
  -- 有限指标集上取**共同**的 `N`
  have hfin : ∀ k : QuartetKey X, ∃ N : ℕ, ∀ n ≥ N,
      |(∑ j ∈ Finset.range n, Mf k j ω) / (∑ j ∈ Finset.range n, Lf k j ω)
        - Wtilde k.1 k.2| < ε :=
    fun k => Metric.tendsto_atTop.mp (hω k) ε hε
  choose N hN using hfin
  refine ⟨Finset.univ.sup N, fun n hn S hS T => ?_⟩
  have hle : N (S, T) ≤ Finset.univ.sup N :=
    Finset.le_sup (Finset.mem_univ ((S, T) : QuartetKey X))
  have hbase := hN (S, T) n (le_trans hle hn)
  -- 目标：`|emp n ω S hS T - Wtilde S T| < ε`；用 `hrep` 把 `emp` 换成块级平均
  have hstep : emp n ω S hS T
      = (∑ j ∈ Finset.range n, Mf (S, T) j ω) / (∑ j ∈ Finset.range n, Lf (S, T) j ω) :=
    hrep n ω S hS T
  rw [hstep]
  exact hbase

/-- ★★ 上一条的**直写形态**（把 `∀ ε > 0` 放在 `∀ᵐ` 之内，下游引用更顺手）。 -/
theorem empWeight_eventually_close_ae {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Type*} [Fintype X] [DecidableEq X]
    (Wtilde : Finset X → Topo → ℝ) (emp : ℕ → Ω → TopoWeight X)
    {Mf Lf : QuartetKey X → ℕ → Ω → ℝ}
    (hjoint : ∀ k : QuartetKey X, iIndepFun (fun j ω => (Mf k j ω, Lf k j ω)) μ)
    (hident : ∀ (k : QuartetKey X) (j : ℕ),
      IdentDistrib (fun ω => (Mf k j ω, Lf k j ω)) (fun ω => (Mf k 0 ω, Lf k 0 ω)) μ μ)
    (hL1 : ∀ (k : QuartetKey X) (j : ℕ) (ω : Ω), (1 : ℝ) ≤ Lf k j ω)
    (hintM : ∀ k : QuartetKey X, Integrable (fun ω => Mf k 0 ω) μ)
    (hintL : ∀ k : QuartetKey X, Integrable (fun ω => Lf k 0 ω) μ)
    (hlim : ∀ k : QuartetKey X,
      (∫ ω, Mf k 0 ω ∂μ) / (∫ ω, Lf k 0 ω ∂μ) = Wtilde k.1 k.2)
    (hrep : ∀ (n : ℕ) (ω : Ω) (S : Finset X) (hS : S.card = 4) (T : Topo),
      emp n ω S hS T
        = (∑ j ∈ Finset.range n, Mf (S, T) j ω) / (∑ j ∈ Finset.range n, Lf (S, T) j ω)) :
    ∀ᵐ ω ∂μ, ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N,
      ∀ (S : Finset X) (hS : S.card = 4) (T : Topo), |emp n ω S hS T - Wtilde S T| < ε := by
  filter_upwards [empWeight_tendsto_ae (μ := μ) Wtilde emp hjoint hident hL1 hintM hintL
    hlim hrep] with ω hω ε hε
  exact hω ε hε

end Phylo.Stat.BlockSLLNTopoClose
