/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.Stat.MassMajorizes
import Phylo.Stat.SiteSamplingAE

/-!
# `Phylo.Stat.MassModel` —— 锚间距模型 → `MSCSite`：identifiability 由**定理**给出，不是假设

## 这一层做什么

`Phylo/Stat/MassMajorizes.lean`（W43-S1）证了裸的组合事实 `mass(r) < mass(q_true)`。
本文件把它包成**模型**并**构造** `MSCSite` —— 其中 `majorizes` 这条字段在 `Parsimony.lean`
是**假设**，在这里是**定理** `AnchorModel.majorizes`：

```text
AnchorModel（物种树 ＋ 相容 split 族 ＋ 正权重 ＋ 真 quartet）
  ├─ inducing_split : ∃ s ∈ F 诱导 q           （由 displays ＋ hF，不是假设）
  ├─ majorizes      : mass(r) < mass(q_true)   ★ 由 MASS_MAJORIZES 得到
  └─ toMSCSite      : cnt = λ·mass 的 MSCSite
       ├─ anchor_iso_ae        （③，复用 parsimony 的 a.e. pipeline）
       └─ MSCSite.ofWeighted   （多拷贝凸组合，P2）⇒ anchorMulti_iso_ae（④）
```

## 三条交付（W43 派单 §1 的 ②③④）

| 条 | 定理 | 相对 `parsimony_iso_ae` 多的假设 |
|---|---|---|
| ③ | `anchor_iso_ae` | 只有 `hmean`（`E[mass_G] = mass`，派单 §3(b)-ii，**已点名**） |
| ② | `parsimonyMulti_iso_ae` | 逐个体组合的 `majorizes` ＋ 权重 `≥0`、`∑=1` |
| ④ | `anchorMulti_iso_ae` | ③ ＋ 每个个体组合一个 `(F_y, w_y)`（逐个由 S1 兑现 `majorizes`） |

## 诚实边界（派单要求逐条点名）

* **`hmean` 就是「`E[d_G] = d`」在表层面的形态**：`∫ ω, ind (ω 0) S hS r ∂μ = λ · mass r`。
  本文件**不证**它（要真建带枝长的溯祖模型，派单 §3(b)-i 的成本），按 §3(b)-ii 的规矩
  作为**显式假设**放在签名里，并在报告里点名。
* `AnchorModel` 的 `tree`/`q`/`q_card`/`displays` 是**模型数据**（「`q` 是树在 `S` 上诱导的 quartet」）；
  对 binary 树可导（`Phylo.Stat.QuartetDecides`），本文件不重复造。
* 「位点 iid」仍是 `SiteSamplingAE` 的 `hint/hindep/hident`，与 parsimony 那条**完全共用**。
* 多拷贝权重只要求 `≥ 0`、`∑ = 1`（派单 §4-P2）；`1/(非 N 数)`、均匀、按质量皆可。
-/

noncomputable section

open Finset MeasureTheory ProbabilityTheory

open scoped Topology ENNReal

namespace Phylo.Stat.MassModel

open Phylo.Stat.MassMajorizes
open Phylo.Stat.SiteSamplingAE (SupportTable empSupport)
open Phylo.Stat.EmpiricalConvergence (SiteFun)

universe u v

variable {X : Type u} [Fintype X] [DecidableEq X]

/-! ## 1. 锚间距模型 -/

/-- **锚间距模型**：物种树 `tree` ＋ 它的 split 权重 `(F, w)` ＋ 真 quartet `q`。

`hF`：「树的每条 split 都在 `F` 里」。于是 `displays` 直接给出「某条 `s ∈ F` 在 `S` 上诱导 `q`」，
`mass_pos` 的前提自动到手 —— 即 `m_Q > 0` 是**推出**的，不是另加的假设。 -/
structure AnchorModel (X : Type u) [Fintype X] [DecidableEq X] where
  /-- 真物种树。 -/
  tree : Cladogram.{u, v} X
  /-- 真 quartet（每个 4-元集上一个有向 split）。 -/
  q : (S : Finset X) → S.card = 4 → Split ↥S
  /-- 真 quartet 是 `2|2` 划分。 -/
  q_card : ∀ (S : Finset X) (hS : S.card = 4), (q S hS).sideA.card = 2
  /-- 真 quartet 确实被树展示。 -/
  displays : ∀ (S : Finset X) (hS : S.card = 4), tree.DisplaysSplitOn S (q S hS)
  /-- 参与加权的 split 族。 -/
  F : Finset (Split X)
  /-- split 权重（= 树度量的边长表示）。 -/
  w : Split X → ℝ
  /-- `F` 两两相容（= 一棵树的 split 系统）。 -/
  hcompat : ∀ s ∈ F, ∀ t ∈ F, Split.Compatible s t
  /-- 权重为正。 -/
  hw : ∀ s ∈ F, 0 < w s
  /-- 树的每条 split 都在 `F` 里。 -/
  hF : ∀ s : Split X, tree.IsSplitOf s → s ∈ F

namespace AnchorModel

variable (A : AnchorModel.{u, v} X)

/-- 真 quartet 被 `F` 的某条 split 诱导（由 `displays` ＋ `hF` 得到）。 -/
theorem inducing_split (S : Finset X) (hS : S.card = 4) :
    ∃ s ∈ A.F, Induces s S (A.q S hS) := by
  obtain ⟨s, hs, hdis⟩ := A.displays S hS
  exact ⟨s, A.hF s hs, Or.inl hdis⟩

/-- ★★★ **`MSCSite.majorizes` 那条字段，在这里是定理**（由 MASS_MAJORIZES）。 -/
theorem majorizes (S : Finset X) (hS : S.card = 4) (r : Split ↥S)
    (hr1 : r ≠ A.q S hS) (hr2 : r ≠ (A.q S hS).swap) :
    mass A.F A.w S r < mass A.F A.w S (A.q S hS) :=
  mass_majorizes A.hw A.hcompat (A.q_card S hS) hS (A.inducing_split S hS) hr1 hr2

/-- 把模型装成 `MSCSite`：`cnt := λ · mass`（`λ` = 每位点每单位枝长的期望替换数）。 -/
noncomputable def toMSCSite (info : (S : Finset X) → S.card = 4 → ℝ) (lam : ℝ)
    (hlam : 0 < lam) : MSCSite.{u, v} X where
  info := info
  cnt S hS r := lam * mass A.F A.w S r
  cnt_nonneg S hS r := mul_nonneg hlam.le (mass_nonneg A.hw S r)
  cnt_swap S hS r := by rw [mass_swap A.F A.w S hS r]
  tree := A.tree
  q := A.q
  q_card := A.q_card
  displays := A.displays
  majorizes S hS r hr1 hr2 := by
    have := A.majorizes S hS r hr1 hr2
    exact mul_lt_mul_of_pos_left this hlam

@[simp] theorem toMSCSite_q (info : (S : Finset X) → S.card = 4 → ℝ) (lam : ℝ)
    (hlam : 0 < lam) : (A.toMSCSite info lam hlam).q = A.q := rfl

end AnchorModel

/-! ## 2. 多拷贝层（P2）：权重非负、和为 1 的凸组合保持 `majorizes` -/

/-- ★★ **P2**：若每个个体组合的表在真 quartet 上严格最大，则**非负权重凸组合**也严格最大。 -/
theorem majorizes_convex {ι : Type*} [Fintype ι] (wt : ι → ℝ) (hwt : ∀ y, 0 ≤ wt y)
    (hsum : ∑ y, wt y = 1) {S : Finset X} {q r : Split ↥S} (cnt : ι → Split ↥S → ℝ)
    (hmaj : ∀ y, cnt y r < cnt y q) :
    (∑ y, wt y * cnt y r) < ∑ y, wt y * cnt y q := by
  obtain ⟨y₀, hy₀⟩ : ∃ y, 0 < wt y := by
    by_contra hcon
    push Not at hcon
    have hzero : ∑ y, wt y = 0 :=
      Finset.sum_eq_zero fun y _ => le_antisymm (hcon y) (hwt y)
    linarith
  refine Finset.sum_lt_sum (fun y _ => ?_) ⟨y₀, Finset.mem_univ _, ?_⟩
  · have := hmaj y
    nlinarith [hwt y]
  · have := hmaj y₀
    nlinarith [hy₀]

/-- 多拷贝模型：把逐个体组合的表 `cnt y` 按权重 `wt` 凸组合，**`majorizes` 由 P2 兑现**。 -/
noncomputable def MSCSite.ofWeighted {ι : Type*} [Fintype ι] (base : MSCSite.{u, v} X)
    (wt : ι → ℝ) (hwt : ∀ y, 0 ≤ wt y) (hsum : ∑ y, wt y = 1)
    (cnt : ι → (S : Finset X) → S.card = 4 → Split ↥S → ℝ)
    (cnt_nonneg : ∀ y S hS r, 0 ≤ cnt y S hS r)
    (cnt_swap : ∀ y S hS r, cnt y S hS r.swap = cnt y S hS r)
    (major : ∀ y S hS r, r ≠ base.q S hS → r ≠ (base.q S hS).swap →
      cnt y S hS r < cnt y S hS (base.q S hS))
    (info : (S : Finset X) → S.card = 4 → ℝ) : MSCSite.{u, v} X where
  info := info
  cnt S hS r := ∑ y, wt y * cnt y S hS r
  cnt_nonneg S hS r :=
    Finset.sum_nonneg fun y _ => mul_nonneg (hwt y) (cnt_nonneg y S hS r)
  cnt_swap S hS r := Finset.sum_congr rfl fun y _ => by rw [cnt_swap y S hS r]
  tree := base.tree
  q := base.q
  q_card := base.q_card
  displays := base.displays
  majorizes S hS r hr1 hr2 :=
    majorizes_convex wt hwt hsum (fun y => cnt y S hS) (fun y => major y S hS r hr1 hr2)

@[simp] theorem MSCSite.ofWeighted_q {ι : Type*} [Fintype ι] (base : MSCSite.{u, v} X)
    (wt : ι → ℝ) (hwt : ∀ y, 0 ≤ wt y) (hsum : ∑ y, wt y = 1)
    (cnt : ι → (S : Finset X) → S.card = 4 → Split ↥S → ℝ)
    (cnt_nonneg) (cnt_swap) (major) (info) :
    (MSCSite.ofWeighted base wt hwt hsum cnt cnt_nonneg cnt_swap major info).q = base.q := rfl

/-! ## 3. 三条交付（③ `anchor_iso_ae` ／ ② `parsimonyMulti_iso_ae` ／ ④ `anchorMulti_iso_ae`）

三条都只是「造 `MSCSite` ＋ 调 `SiteSamplingAE.parsimony_iso_ae`」——
管线（SLLN → `stable_argmax` → `QuartetDecidesTree`）**一行都没重写**（派单 §2 的要求）。 -/

section Deliverables

variable {Ω₀ : Type*} [MeasurableSpace Ω₀]

/-- 概率侧的公共假设（与 `SiteSamplingAE` 逐字相同，抽出来只为省重复）。 -/
abbrev SiteHyps (ind : SiteFun X Ω₀) (μ : Measure (ℕ → Ω₀)) [IsProbabilityMeasure μ] : Prop :=
  (∀ (S : Finset X) (hS : S.card = 4) (q : Split ↥S),
      Integrable (fun ω : ℕ → Ω₀ => ind (ω 0) S hS q) μ) ∧
  (∀ (S : Finset X) (hS : S.card = 4) (q : Split ↥S),
      iIndepFun (fun i (ω : ℕ → Ω₀) => ind (ω i) S hS q) μ) ∧
  (∀ (S : Finset X) (hS : S.card = 4) (q : Split ↥S), ∀ i,
      IdentDistrib (fun ω : ℕ → Ω₀ => ind (ω i) S hS q)
        (fun ω : ℕ → Ω₀ => ind (ω 0) S hS q) μ μ)

/-- ★★★ **③ `anchor_iso_ae`** —— 锚间距管线的**几乎必然**树层统计一致性。

相对 `SiteSamplingAE.parsimony_iso_ae`，**唯一**多出来的是 `hmean`：
`∫ ω, ind (ω 0) S hS r ∂μ = λ · mass r`，即 **`E[d_G] = d`**（派单 §3(b)）。
`majorizes` 不再假设 —— 它由 `AnchorModel.majorizes`（= MASS_MAJORIZES，W43-S1）兑现。 -/
theorem anchor_iso_ae (A : AnchorModel.{u, v} X) (info : (S : Finset X) → S.card = 4 → ℝ)
    (lam : ℝ) (hlam : 0 < lam) (ind : SiteFun X Ω₀) (h : SupportTable ind)
    (hT : A.tree.IsBinary) (μ : Measure (ℕ → Ω₀)) [IsProbabilityMeasure μ]
    (hint : ∀ (S : Finset X) (hS : S.card = 4) (q : Split ↥S),
      Integrable (fun ω : ℕ → Ω₀ => ind (ω 0) S hS q) μ)
    (hindep : ∀ (S : Finset X) (hS : S.card = 4) (q : Split ↥S),
      iIndepFun (fun i (ω : ℕ → Ω₀) => ind (ω i) S hS q) μ)
    (hident : ∀ (S : Finset X) (hS : S.card = 4) (q : Split ↥S), ∀ i,
      IdentDistrib (fun ω : ℕ → Ω₀ => ind (ω i) S hS q)
        (fun ω : ℕ → Ω₀ => ind (ω 0) S hS q) μ μ)
    (hmean : ∀ (S : Finset X) (hS : S.card = 4) (r : Split ↥S),
      ∫ ω, ind (ω 0) S hS r ∂μ = lam * mass A.F A.w S r)
    {E : SiteSupport X → QuartetTree.{u, v} X} (hE : ∀ D, IsParsimony D (E D))
    (hEbin : ∀ D, (E D).tree.IsBinary)
    (hNE : ∃ q : QuartetChoice X, ¬ AgreesWith A.q q) :
    ∀ᵐ ω ∂μ, ∃ N : ℕ, ∀ n ≥ N,
      Nonempty (Iso (E (empSupport ind h (A.toMSCSite info lam hlam) n ω)).tree A.tree) :=
  SiteSamplingAE.parsimony_iso_ae (X := X) (Ω₀ := Ω₀) ind h (A.toMSCSite info lam hlam)
    hT μ hint hindep hident hmean hE hEbin hNE

/-- ★★★ **② `parsimonyMulti_iso_ae`** —— **多拷贝** parsimony：每个个体组合一张支持表，
按非负权重凸组合（`∑ = 1`）后再走同一条 pipeline。

多拷贝的**全部**新内容就是 P2（`majorizes_convex`）：凸组合保持「真 quartet 严格最大」。 -/
theorem parsimonyMulti_iso_ae {ι : Type u} [Fintype ι] (best : MSCSite.{u, v} X)
    (cnt : ι → (S : Finset X) → S.card = 4 → Split ↥S → ℝ)
    (cnt_nonneg : ∀ y S hS r, 0 ≤ cnt y S hS r)
    (cnt_swap : ∀ y S hS r, cnt y S hS r.swap = cnt y S hS r)
    (major : ∀ y S hS r, r ≠ best.q S hS → r ≠ (best.q S hS).swap →
      cnt y S hS r < cnt y S hS (best.q S hS))
    (wt : ι → ℝ) (hwt : ∀ y, 0 ≤ wt y) (hsum : ∑ y, wt y = 1)
    (info : (S : Finset X) → S.card = 4 → ℝ)
    (ind : SiteFun X Ω₀) (h : SupportTable ind) (hT : best.tree.IsBinary)
    (μ : Measure (ℕ → Ω₀)) [IsProbabilityMeasure μ]
    (hint : ∀ (S : Finset X) (hS : S.card = 4) (q : Split ↥S),
      Integrable (fun ω : ℕ → Ω₀ => ind (ω 0) S hS q) μ)
    (hindep : ∀ (S : Finset X) (hS : S.card = 4) (q : Split ↥S),
      iIndepFun (fun i (ω : ℕ → Ω₀) => ind (ω i) S hS q) μ)
    (hident : ∀ (S : Finset X) (hS : S.card = 4) (q : Split ↥S), ∀ i,
      IdentDistrib (fun ω : ℕ → Ω₀ => ind (ω i) S hS q)
        (fun ω : ℕ → Ω₀ => ind (ω 0) S hS q) μ μ)
    (hmean : ∀ (S : Finset X) (hS : S.card = 4) (r : Split ↥S),
      ∫ ω, ind (ω 0) S hS r ∂μ = ∑ y, wt y * cnt y S hS r)
    {E : SiteSupport X → QuartetTree.{u, v} X} (hE : ∀ D, IsParsimony D (E D))
    (hEbin : ∀ D, (E D).tree.IsBinary)
    (hNE : ∃ q : QuartetChoice X, ¬ AgreesWith best.q q) :
    ∀ᵐ ω ∂μ, ∃ N : ℕ, ∀ n ≥ N,
      Nonempty (Iso
        (E (empSupport ind h
          (MSCSite.ofWeighted best wt hwt hsum cnt cnt_nonneg cnt_swap major info) n ω)).tree
        best.tree) :=
  SiteSamplingAE.parsimony_iso_ae (X := X) (Ω₀ := Ω₀) ind h
    (MSCSite.ofWeighted best wt hwt hsum cnt cnt_nonneg cnt_swap major info)
    hT μ hint hindep hident hmean hE hEbin hNE

/-- ★★★ **④ `anchorMulti_iso_ae`** —— 锚间距 ＋ 多拷贝：每个个体组合给**自己的**
相容 split 族 `(F_y, w_y)`（各自由 S1 兑现 `majorizes`），凸组合后再走同一条 pipeline。

⇒ 「简约＋无缺失」「简约＋多个体」「锚间距＋无缺失」「锚间距＋多个体」四格全齐
（① = 库内既有的 `parsimony_iso_ae`）。

★ 口径：`hmean` 写成 `∑ y, wt y * (λ · mass_y)`；它与「`λ · ∑ y, wt y · mass_y`」只差
`Finset.mul_sum`（`∑ y, wt y * (λ * c y) = λ * ∑ y, wt y * c y`）。 -/
theorem anchorMulti_iso_ae {ι : Type u} [Fintype ι] [Nonempty ι]
    (A : AnchorModel.{u, v} X)
    (Fm : ι → Finset (Split X)) (wm : ι → Split X → ℝ)
    (hcompat : ∀ y, ∀ s ∈ Fm y, ∀ t ∈ Fm y, Split.Compatible s t)
    (hw : ∀ y, ∀ s ∈ Fm y, 0 < wm y s)
    (hind : ∀ y (S : Finset X) (hS : S.card = 4), ∃ s ∈ Fm y, Induces s S (A.q S hS))
    (wt : ι → ℝ) (hwt : ∀ y, 0 ≤ wt y) (hsum : ∑ y, wt y = 1)
    (info : (S : Finset X) → S.card = 4 → ℝ) (lam : ℝ) (hlam : 0 < lam)
    (ind : SiteFun X Ω₀) (h : SupportTable ind) (hT : A.tree.IsBinary)
    (μ : Measure (ℕ → Ω₀)) [IsProbabilityMeasure μ]
    (hint : ∀ (S : Finset X) (hS : S.card = 4) (q : Split ↥S),
      Integrable (fun ω : ℕ → Ω₀ => ind (ω 0) S hS q) μ)
    (hindep : ∀ (S : Finset X) (hS : S.card = 4) (q : Split ↥S),
      iIndepFun (fun i (ω : ℕ → Ω₀) => ind (ω i) S hS q) μ)
    (hident : ∀ (S : Finset X) (hS : S.card = 4) (q : Split ↥S), ∀ i,
      IdentDistrib (fun ω : ℕ → Ω₀ => ind (ω i) S hS q)
        (fun ω : ℕ → Ω₀ => ind (ω 0) S hS q) μ μ)
    (hmean : ∀ (S : Finset X) (hS : S.card = 4) (r : Split ↥S),
      ∫ ω, ind (ω 0) S hS r ∂μ = ∑ y, wt y * (lam * mass (Fm y) (wm y) S r))
    {E : SiteSupport X → QuartetTree.{u, v} X} (hE : ∀ D, IsParsimony D (E D))
    (hEbin : ∀ D, (E D).tree.IsBinary)
    (hNE : ∃ q : QuartetChoice X, ¬ AgreesWith A.q q) :
    ∀ᵐ ω ∂μ, ∃ N : ℕ, ∀ n ≥ N,
      Nonempty (Iso
        (E (empSupport ind h
          (MSCSite.ofWeighted (A.toMSCSite info lam hlam) wt hwt hsum
            (fun y (S : Finset X) (hS : S.card = 4) (r : Split ↥S) =>
              lam * mass (Fm y) (wm y) S r)
            (fun y S _hS r => mul_nonneg hlam.le (mass_nonneg (hw y) S r))
            (fun y S _hS r => by rw [mass_swap (Fm y) (wm y) S _hS r])
            (fun y S hS r hr1 hr2 =>
              mul_lt_mul_of_pos_left
                (mass_majorizes (hw y) (hcompat y) (A.q_card S hS) hS (hind y S hS) hr1 hr2)
                hlam)
            info) n ω)).tree
        A.tree) :=
  parsimonyMulti_iso_ae (X := X) (Ω₀ := Ω₀) (ι := ι)
    (best := A.toMSCSite info lam hlam)
    (fun y (S : Finset X) (hS : S.card = 4) (r : Split ↥S) => lam * mass (Fm y) (wm y) S r)
    (fun y S _hS r => mul_nonneg hlam.le (mass_nonneg (hw y) S r))
    (fun y S hS r => by rw [mass_swap (Fm y) (wm y) S hS r])
    (fun y S hS r hr1 hr2 =>
      mul_lt_mul_of_pos_left
        (mass_majorizes (hw y) (hcompat y) (A.q_card S hS) hS (hind y S hS) hr1 hr2) hlam)
    wt hwt hsum info ind h hT μ hint hindep hident hmean hE hEbin hNE

end Deliverables

end Phylo.Stat.MassModel
