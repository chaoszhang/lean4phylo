/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.Stat.MSCSamplingAE
import Phylo.Stat.MSCProof

/-!
# `Phylo.Stat.GeneTreeSamplingAE` —— **基因树层**的几乎必然一致性（W13g ⭐ ASTRAL 捷径）

## 1. 这个文件做什么（W13 规格 §2.3）

库内 ASTRAL 侧的端到端「几乎必然一致」定理
（`Phylo.Stat.MSCSamplingAE.astral_iso_ae`）挂着一条**测度层假设**

```text
hmean : ∫ ω, ind (ω 0) S hS q ∂μ = m.freq.p S hS q
```

即「**位点观测的边缘分布 = MSC 理论分布**」。本文件把这条假设**升级为定理**，
**只走生成模型的第 1 步**（规格 §1 / §2.3）：

> 物种树 `σ` ⇒ `k` 棵 **iid 基因树** ⇒ 经验 quartet 频率 ⇒ **基因树层大数定律** ⇒ `astral_iso`。

**不经过位点层、不需要块级 SLLN**（规格 §3.1 的块级收缩是给 CASTER 侧用的）。

## 2. 模型（`GeneTreeModel`）

最小可用版本**不建模树的类型**，只建模「每棵基因树给出一张 quartet 频率表」：

```text
structure GeneTreeModel (X) where
  G      : 基因树空间
  ν      : Measure G   （概率测度）
  freqOf : G → QuartetFreq X
  hmeas  : 逐 `(S, hS, q)` 可测（技术性 —— 见 §5 诚实边界）
  m      : MSCFreq X   （真物种树 ＋ MSC 核心不等式，库内既有对象）
  hpush  : ∀ S hS q, ∫ g, (freqOf g).p S hS q ∂ν = m.freq.p S hS q
```

`hpush` 就是**缺口 G2**（`Phylo.Stat.SplitProbabilities.msc_split_probability_object_gap`，
`Phylo/Stat/SplitProbabilities.lean:541` 附近）的**正面陈述**：「理论频率 = 基因树分布的**推前**」。
即规格 §7.1 所说的那个「诱导」。

## 3. 核心交付（**`hmean` 不再是假设**）

1. ★★★ `GeneTreeModel.meanFreq` —— **推前均值表**：`p S hS q := ∫ g, (freqOf g).p S hS q ∂ν`
   （三条字段真证）。这就是「由基因树分布**诱导**出来的频率表」。
2. ★★★ `GeneTreeModel.meanFreq_eq_law` —— **识别等式**：`meanFreq M = M.m.freq`
   （由 `hpush` 逐点得到）。⇒ 于是 **`hmean` 是这条等式的展开**，不再是假设。
3. ★★★ `GeneTreeModel.emp_eventually_close_ae` —— **基因树层大数定律**：
   在**无穷乘积测度** `μ = Measure.infinitePi (fun _ : ℕ => ν)`（`ℕ → G` 上、坐标 iid 边缘 `ν`）下，
   经验表 `emp k ω` **几乎必然**最终 `ε`-接近 `m.freq`。
4. ★★★ `astral_iso_ae_of_geneTrees` —— **端到端**（**零 `hmean`**）：

   ```text
   ∀ᵐ ω ∂μ, ∃ N, ∀ k ≥ N, Nonempty (Iso (E (emp k ω)).tree m.tree)
   ```

   假设面只剩：`GeneTreeModel` 的字段（`ν` 是概率测度 ＋ `hpush`）＋
   估计量 `E` 的两条算法性质（`IsASTRAL` / binary）＋ `hNE`。

## 4. 走的是**哪条**技术路线

* 概率空间**真的构造出来了**：`Measure.infinitePi (fun _ : ℕ => ν)`
  （`Mathlib/Probability/ProductMeasure.lean`；`Mathlib/Probability/Independence/InfinitePi.lean` 的
  `iIndepFun_infinitePi`），坐标 iid 与边缘律都是**定理**（`sampleMeasure_map_eval`）；
  **不是**把 iid 当假设。
* 大数定律套 `ProbabilityTheory.strong_law_ae`；「整张表同时收敛」＝**有限交**
  ——这两步都**复用** `Phylo/Stat/MSCSamplingAE.lean` 的现成结果
  （`empFreq_tendsto_ae_all` / `empTable_eventually_close_ae`），**另起炉灶 0 行**。
* 收口复用 `MSCSamplingAE.astral_statisticallyConsistent_fixed`（**零 `hmean`**）
  ＋ `QuartetDecidesTree`（`Phylo/Stat/QuartetDecides.lean:330`）。

## 5. 诚实边界（逐条）

| 条目 | 状态 |
|---|---|
| 物种树 → `k` 棵 iid 基因树（**测度层**） | ✅ **本文件**：`sampleMeasure` 是 `ℕ → G` 上的真无穷乘积测度，坐标 iid ＋ 边缘 `ν` 都是定理 |
| 「基因树分布 = MSC(σ) 的推前」（缺口 G2） | ✅ **本文件**：`hpush` ＋ `meanFreq_eq_law`。⚠️ 但 `hpush` 是**模型的字段**：MSC 溯祖过程本身**没有**从 `kingmanMSCMeasure` 推出整棵树的分布（那是缺口 B1 的**完整版**，规格 §9 明确不在本批内） |
| `hmean`（位点边缘分布 = 理论频率） | ✅ **本文件**（`meanFreq_eq_law`）：它现在是**定理**，不是假设 |
| 单棵基因树「给出一张 `QuartetFreq`」这一抽象 | ⚠️ **是模型的建模选择**（规格 §2.3 的「最小可用版本」）：不建模 `G` 的内部结构（拓扑/枝长），只要求它给出一张频率表 |
| `freqOf` 的**逐点可测性**（`hmeas`） | ⚠️ **模型字段**：这是规格 §6 的缺口 **B2**（`patternProb` / `geneScore` 的 `Measurable` 库内没有）。它不是数学内容，是 Lean 侧的技术条件；`integrable_freqOf` 由它 ＋ `p ≤ 1` 推出 |
| 基因树层 iid 的**概率空间存在性** | ✅ **本文件构造**（`sampleMeasure`），不再是假设 |
| 「位点 iid」/「位点层」 | ❌ **本文件完全不碰**（规格 §2.3：ASTRAL 不需要位点层） |
| ★D：`hpush` 与 `majorizes` 可同时满足？ | ✅ **可以**（§5.2 显式居民）；⚠️ 但「两棵点质量树各 `1/2`」那个**候选居民是假的**（两类并列 ⇒ `majorizes` 失败） |
| ★8④：`ν` 为 Dirac 时退化到库内确定性形态 | ✅ **本文件**（`diracModel_emp_eq` / `diracModel_converges`，`N = 0`） |
| `k` **固定**时结论为真 | ❌ **为假**（规格 §4.1）：固定 `k` 时极限 `(1/k) Σ_{j≤k} freqOf (ω j)` 依赖实现到的基因树，一般 ≠ 常数 `m.freq` |
| `π` / `κ`（老师第三次补充） | ❌ 与 ASTRAL 侧**无关**（那是 CASTER / F84 的位点权重层，子批 W13h） |

## 6. 术语说明

`m.freq` 在库内被注释为「观测到的 quartet 频率（理想样本下 = MSC 理论分布）」
（`Phylo/Stat/MSC.lean`）。本文件之后，这句话在**基因树层**可以读成一条**定理**：
`m.freq = ∫ freqOf ∂ν`（`meanFreq_eq_law`）。
-/

set_option autoImplicit false

noncomputable section

open Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal

namespace Phylo.Stat.GeneTreeSamplingAE

universe u v w

variable {X : Type u} [Fintype X] [DecidableEq X]

/-! ## 0. 预备：`QuartetFreq` 的相等性只看 `p` -/

namespace QuartetFreq

/-- ★ **`QuartetFreq` 相等性只看 `p`**（其余三条字段是 `Prop`，由证明无关性决定）。

与 `KPartition.eq_iff_parts`（`Phylo/Stat/Split.lean`）同一个套路。 -/
theorem eq_iff_p {D D' : QuartetFreq X} : D = D' ↔ D.p = D'.p := by
  constructor
  · intro h
    rw [h]
  · intro h
    cases D with
    | mk p pn ps pw =>
      cases D' with
      | mk p' pn' ps' pw' =>
        simp only at h
        subst h
        congr 1

end QuartetFreq

/-! ## 1. 基因树采样模型 -/

/-- ★★★ **基因树采样模型**（W13 规格 §1 的**第 1 步**）。

* `G` / `ν`：基因树空间与其分布（`G` 用自己的宇宙 `w` —— 与叶集 `X` 无关）；
* `freqOf`：单棵基因树给出的 quartet 频率表（**不建模树的内部结构** —— 规格 §2.3）；
* `hmeas`：逐 `(S, hS, q)` 可测（技术性条件，见文件头 §5；缺口 B2）；
* `m`：真物种树 ＋ MSC 核心不等式（`Phylo.Stat.MSC` 的既有对象）；
* `hpush`：★★ **识别等式** —— 理论频率 = 基因树分布的**推前**
  （即缺口 G2「`P` 必须由 gene tree 分布诱导」的**正面陈述**）。

⚠️ `hpush` 是**模型的字段**：本文件**不**从 `kingmanMSCMeasure` 推出整棵树的分布
（那是缺口 B1 的完整版，规格 §9 明确不在本批内）。 -/
structure GeneTreeModel (X : Type u) [Fintype X] [DecidableEq X] where
  /-- 基因树空间。 -/
  G : Type w
  /-- 基因树空间的可测结构。 -/
  [meas : MeasurableSpace G]
  /-- 基因树分布（概率测度）。 -/
  ν : Measure G
  /-- `ν` 是概率测度。 -/
  [isProb : IsProbabilityMeasure ν]
  /-- 单棵基因树的 quartet 频率表。 -/
  freqOf : G → QuartetFreq X
  /-- **技术性可测性**（缺口 B2）：逐 `(S, hS, q)` 可测。 -/
  hmeas : ∀ (S : Finset X) (hS : S.card = 4) (q : Split ↥S),
    Measurable fun g => (freqOf g).p S hS q
  /-- 真物种树 ＋ MSC 核心不等式（库内既有对象）。 -/
  m : MSCFreq.{u, v} X
  /-- ★★ **识别等式（缺口 G2 的正面陈述）**：理论频率 = 基因树分布的推前。 -/
  hpush : ∀ (S : Finset X) (hS : S.card = 4) (q : Split ↥S),
    ∫ g, (freqOf g).p S hS q ∂ν = m.freq.p S hS q

attribute [instance] GeneTreeModel.isProb GeneTreeModel.meas

namespace GeneTreeModel

/-! ### 1.1 基本估计 -/

/-- 任一 `QuartetFreq` 的任一分量 `≤ 1`（由非负 ＋ 求和为 `1`）。 -/
theorem QuartetFreq.p_le_one (D : QuartetFreq X) (S : Finset X) (hS : S.card = 4)
    (q : Split ↥S) : D.p S hS q ≤ 1 := by
  have hle := Finset.single_le_sum (s := (Finset.univ : Finset (Split ↥S)))
    (f := fun q => D.p S hS q) (fun i _ => D.p_nonneg S hS i) (Finset.mem_univ q)
  have hsum := D.p_sum_one S hS
  linarith

/-- 每棵基因树的频率分量都在 `[0,1]` 内。 -/
theorem freqOf_le_one (M : GeneTreeModel.{u, v, w} X) (S : Finset X) (hS : S.card = 4)
    (q : Split ↥S) (g : M.G) : (M.freqOf g).p S hS q ≤ 1 :=
  QuartetFreq.p_le_one (M.freqOf g) S hS q

/-- ★ **可积性**：由可测性（`hmeas`）＋ 有界性（`≤ 1`）得到。
对应规格 §6 的缺口 B3（在模型条件下**自动成立**），故它不是模型的额外字段。 -/
theorem integrable_freqOf (M : GeneTreeModel.{u, v, w} X) (S : Finset X) (hS : S.card = 4)
    (q : Split ↥S) : Integrable (fun g => (M.freqOf g).p S hS q) M.ν :=
  Integrable.of_bound (M.hmeas S hS q).aestronglyMeasurable 1
    (Eventually.of_forall fun g => by
      rw [Real.norm_eq_abs, abs_of_nonneg ((M.freqOf g).p_nonneg S hS q)]
      exact M.freqOf_le_one S hS q g)

/-! ### 1.2 ★★★ 推前均值表：**缺口 G2 的正面对象** -/

/-- ★★★ **推前均值表**（「由基因树分布**诱导**出来的 quartet 频率表」）：

```text
meanFreq.p S hS q := ∫ g, (freqOf g).p S hS q ∂ν
```

三条字段（非负 / 和为 `1` / `swap` 不变）**逐条真证**。
这是 ASTRAL 侧那条测度层假设 `hmean` 的**定义侧**：
`hmean` 说「`m.freq.p` 等于这个积分」，而在这里它**就是**这个积分（见 `meanFreq_eq_law`）。 -/
noncomputable def meanFreq (M : GeneTreeModel.{u, v, w} X) : QuartetFreq X where
  p S hS q := ∫ g, (M.freqOf g).p S hS q ∂M.ν
  p_nonneg S hS q := integral_nonneg fun g => (M.freqOf g).p_nonneg S hS q
  p_sum_one S hS := by
    rw [← integral_finsetSum Finset.univ (fun q _ => M.integrable_freqOf S hS q)]
    have h1 : (fun g => ∑ q : Split ↥S, (M.freqOf g).p S hS q) = fun _ => (1 : ℝ) := by
      funext g
      exact (M.freqOf g).p_sum_one S hS
    rw [h1, integral_const, Measure.real, measure_univ, ENNReal.toReal_one, one_smul]
  p_swap S hS q := by
    show (∫ g, (M.freqOf g).p S hS q.swap ∂M.ν) = ∫ g, (M.freqOf g).p S hS q ∂M.ν
    rw [show (fun g => (M.freqOf g).p S hS q.swap) = fun g => (M.freqOf g).p S hS q from
      funext fun g => (M.freqOf g).p_swap S hS q]

/-- ★★★ **识别等式（`hmean` 变成定理）**：由基因树分布诱导的频率表**就是** `m.freq`。

即库内那条假设 `hmean : ∫ ω, ind (ω 0) S hS q ∂μ = m.freq.p S hS q`
的「理论频率」一侧现在有一个**正面对象**（`meanFreq`），且它与 `m.freq` 的相等
**由 `hpush` 逐点给出** —— 不再是额外假设。 -/
theorem meanFreq_eq_law (M : GeneTreeModel.{u, v, w} X) : M.meanFreq = M.m.freq :=
  (QuartetFreq.eq_iff_p (D := M.meanFreq) (D' := M.m.freq)).mpr (by
    funext S hS q
    exact M.hpush S hS q)

/-! ### 1.3 概率空间：`ℕ → G` 上的**无穷乘积测度** -/

/-- ★★★ **基因树样本空间**：`Measure.infinitePi (fun _ : ℕ => ν)` ——
`ℕ → G` 上的可数无穷乘积测度（坐标 iid、边缘 `ν`；两者都由下文**证明**）。 -/
noncomputable abbrev sampleMeasure (M : GeneTreeModel.{u, v, w} X) : Measure (ℕ → M.G) :=
  Measure.infinitePi fun _ : ℕ => M.ν

/-- 乘积测度是概率测度（Mathlib 的 `instance : IsProbabilityMeasure (infinitePi μ)`）。 -/
instance instIsProbabilityMeasureSampleMeasure (M : GeneTreeModel.{u, v, w} X) :
    IsProbabilityMeasure M.sampleMeasure := by
  rw [sampleMeasure]
  infer_instance

/-- ★★ 坐标 `i` 的**边缘律**是 `ν`（Mathlib `Measure.infinitePi_map_eval`）。
⇒ `ω i` 与 `ω 0` **同分布**（`identDistrib_eval`），且 `ω i` 的期望给出 `hpush`。 -/
theorem sampleMeasure_map_eval (M : GeneTreeModel.{u, v, w} X) (i : ℕ) :
    (M.sampleMeasure).map (fun ω : ℕ → M.G => ω i) = M.ν := by
  rw [sampleMeasure]
  exact Measure.infinitePi_map_eval (fun _ : ℕ => M.ν) i

/-! ### 1.4 iid 三件套 ＋ 边缘期望（**都是定理，不是假设**） -/

/-- ★★★ **独立性**：`ω ↦ (freqOf (ω j)).p S hS q` 作为 `j` 的族**相互独立**
（`iIndepFun_infinitePi`，坐标 iid）。 -/
theorem iIndepFun_eval (M : GeneTreeModel.{u, v, w} X) (S : Finset X) (hS : S.card = 4)
    (q : Split ↥S) :
    iIndepFun (fun j (ω : ℕ → M.G) => (M.freqOf (ω j)).p S hS q) M.sampleMeasure := by
  rw [sampleMeasure]
  exact iIndepFun_infinitePi (P := fun _ : ℕ => M.ν)
    (X := fun _ => fun g => (M.freqOf g).p S hS q) (fun _ => M.hmeas S hS q)

/-- ★★ **同分布**：每个坐标的推前律都是 `Measure.map (freqOf ·).p ν`
（由 `sampleMeasure_map_eval` ＋ `Measure.map_map`）。 -/
theorem map_eval_freqOf (M : GeneTreeModel.{u, v, w} X) (S : Finset X) (hS : S.card = 4)
    (q : Split ↥S) (j : ℕ) :
    Measure.map (fun ω : ℕ → M.G => (M.freqOf (ω j)).p S hS q) M.sampleMeasure
      = Measure.map (fun g => (M.freqOf g).p S hS q) M.ν := by
  rw [show (fun ω : ℕ → M.G => (M.freqOf (ω j)).p S hS q)
      = (fun g => (M.freqOf g).p S hS q) ∘ (fun ω : ℕ → M.G => ω j) from rfl]
  rw [← Measure.map_map (M.hmeas S hS q) (measurable_pi_apply j), M.sampleMeasure_map_eval j]

/-- ★★ **同分布（`IdentDistrib` 形式）**：`ω j` 与 `ω 0` 上的分量同分布。 -/
theorem identDistrib_eval (M : GeneTreeModel.{u, v, w} X) (S : Finset X) (hS : S.card = 4)
    (q : Split ↥S) (j : ℕ) :
    IdentDistrib (fun ω : ℕ → M.G => (M.freqOf (ω j)).p S hS q)
      (fun ω : ℕ → M.G => (M.freqOf (ω 0)).p S hS q) M.sampleMeasure M.sampleMeasure := by
  refine IdentDistrib.mk ?_ ?_ ?_
  · exact ((M.hmeas S hS q).comp (measurable_pi_apply j)).aemeasurable
  · exact ((M.hmeas S hS q).comp (measurable_pi_apply 0)).aemeasurable
  · rw [M.map_eval_freqOf S hS q j, M.map_eval_freqOf S hS q 0]

/-- ★★★ **边缘期望（这就是 `hmean`）**：`∫ ω, (freqOf (ω 0)).p S hS q ∂μ = m.freq.p S hS q`。

证明 = 边缘律 `μ.map (· 0) = ν`（`sampleMeasure_map_eval`）＋ `integral_map`
＋ **模型的识别等式** `hpush`。 -/
theorem integral_eval (M : GeneTreeModel.{u, v, w} X) (S : Finset X) (hS : S.card = 4)
    (q : Split ↥S) :
    ∫ ω, (M.freqOf (ω 0)).p S hS q ∂M.sampleMeasure = M.m.freq.p S hS q := by
  have h1 := integral_map (μ := M.sampleMeasure) (φ := fun ω : ℕ → M.G => ω 0)
    (f := fun g => (M.freqOf g).p S hS q) (measurable_pi_apply 0).aemeasurable
    (M.hmeas S hS q).aestronglyMeasurable
  rw [M.sampleMeasure_map_eval 0] at h1
  rw [← h1]
  exact M.hpush S hS q

/-- ★★ **可积性**（`ω ↦ (freqOf (ω 0)).p S hS q`）：由 `integrable_freqOf` 经边缘律运输。 -/
theorem integrable_eval (M : GeneTreeModel.{u, v, w} X) (S : Finset X) (hS : S.card = 4)
    (q : Split ↥S) :
    Integrable (fun ω : ℕ → M.G => (M.freqOf (ω 0)).p S hS q) M.sampleMeasure := by
  have h1 : Integrable (fun g => (M.freqOf g).p S hS q)
      ((M.sampleMeasure).map (fun ω : ℕ → M.G => ω 0)) := by
    rw [M.sampleMeasure_map_eval 0]
    exact M.integrable_freqOf S hS q
  have h2 := h1.comp_aemeasurable (measurable_pi_apply 0).aemeasurable
  simpa [Function.comp_def] using h2

/-! ## 2. 经验 quartet 频率表（基因树层） -/

/-- 把「基因树」当作「观测」送进 `MSCSamplingAE` 的接口（现成模板）。 -/
abbrev siteFun (M : GeneTreeModel.{u, v, w} X) :
    Phylo.Stat.EmpiricalConvergence.SiteFun X M.G := fun g S hS q => (M.freqOf g).p S hS q

/-- 「每棵基因树本身给出一个概率分布」⇒ `SiteTable`（三条字段由 `QuartetFreq` 的字段给出）。 -/
theorem siteTable (M : GeneTreeModel.{u, v, w} X) : MSCSamplingAE.SiteTable M.siteFun :=
  ⟨fun g S hS q => (M.freqOf g).p_nonneg S hS q,
   fun g S hS => (M.freqOf g).p_sum_one S hS,
   fun g S hS q => (M.freqOf g).p_swap S hS q⟩

/-- ★★ **经验 quartet 频率表**（＝基因树层的「位点」，每个「位点」是一棵基因树）：

```text
emp k ω 的 p S hS q = if k = 0 then m.freq.p S hS q
                       else (k : ℝ)⁻¹ * ∑ j ∈ range k, (freqOf (ω j)).p S hS q
```

`k = 0` 的退化分支沿用 `MSCSamplingAE.empTable` 的**全函数**技巧
（`k = 0` 时 `∑ = 0`，不是频率表，故取先验 `m.freq`；数学上 `k = 0` 从不被用到）。 -/
noncomputable def emp (M : GeneTreeModel.{u, v, w} X) (k : ℕ) (ω : ℕ → M.G) : QuartetFreq X :=
  MSCSamplingAE.empTable M.siteFun M.siteTable M.m k ω

/-- ★★ **经验表的显式公式**（即上面 docstring 里那条）。 -/
theorem emp_p (M : GeneTreeModel.{u, v, w} X) (k : ℕ) (ω : ℕ → M.G) (S : Finset X)
    (hS : S.card = 4) (q : Split ↥S) :
    (M.emp k ω).p S hS q
      = if k = 0 then M.m.freq.p S hS q
        else (k : ℝ)⁻¹ * ∑ j ∈ Finset.range k, (M.freqOf (ω j)).p S hS q := by
  simp only [emp, MSCSamplingAE.empTable, siteFun,
    Phylo.Stat.EmpiricalConvergence.empFreq]

/-! ## 3. ★★★ 基因树层大数定律 -/

/-- ★★★ **基因树层大数定律**（**整张表**、**同一个零测集**）：

在无穷乘积测度下，**几乎必然**地，对**所有** 4-元集 `S` 与所有 split `q` **同时**，
经验频率收敛到理论频率 `m.freq.p S hS q`。

证明 = 直接套 `MSCSamplingAE.empFreq_tendsto_ae_all`
（`strong_law_ae` ＋ **有限指标集取交**），四个前提全部由模型字段给出（见 §1.4）。 -/
theorem emp_tendsto_ae_all (M : GeneTreeModel.{u, v, w} X) :
    ∀ᵐ ω ∂M.sampleMeasure, ∀ (S : Finset X) (hS : S.card = 4) (q : Split ↥S),
      Tendsto (fun k : ℕ => (k : ℝ)⁻¹ * ∑ j ∈ Finset.range k, (M.freqOf (ω j)).p S hS q)
        atTop (𝓝 (M.m.freq.p S hS q)) := by
  have h := MSCSamplingAE.empFreq_tendsto_ae_all M.siteFun M.m M.sampleMeasure
    (fun S hS q => M.integrable_eval S hS q)
    (fun S hS q => M.iIndepFun_eval S hS q)
    (fun S hS q j => M.identDistrib_eval S hS q j)
    (fun S hS q => M.integral_eval S hS q)
  filter_upwards [h] with ω hω S hS q
  simpa only [Phylo.Stat.EmpiricalConvergence.empFreq] using hω S hS q

/-- ★★★ **统一的 `N`**：`∀ᵐ ω, ∀ ε > 0, ∃ N, ∀ k ≥ N, FreqClose (emp k ω) m.freq ε`
—— 这正是 `Phylo.Stat.MSC.MSCSampling.converges` 那条**确定性公理**的**几乎必然版**
（共同 `N` 由有限指标集上的 `sup'` 取得；**零 `hmean`**）。 -/
theorem emp_eventually_close_ae (M : GeneTreeModel.{u, v, w} X) :
    ∀ᵐ ω ∂M.sampleMeasure, ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ k ≥ N,
      FreqClose (M.emp k ω) M.m.freq ε := by
  have h := MSCSamplingAE.empTable_eventually_close_ae M.siteFun M.siteTable M.m M.sampleMeasure
    (fun S hS q => M.integrable_eval S hS q)
    (fun S hS q => M.iIndepFun_eval S hS q)
    (fun S hS q j => M.identDistrib_eval S hS q j)
    (fun S hS q => M.integral_eval S hS q)
  filter_upwards [h] with ω hω
  exact hω

/-! ## 4. ★★★ 接线：`MSCSamplingFixed` ⇒ quartet 层 ⇒ 树层 -/

/-- ★★★ **公理化的采样结构被基因树数据 a.e. 实现**
（真律 `= m`，经验表 `= emp · ω`）—— 于是 `MSCSamplingFixed` 有了**非退化**的居民。 -/
theorem exists_mscSamplingFixed_ae (M : GeneTreeModel.{u, v, w} X) :
    ∀ᵐ ω ∂M.sampleMeasure, ∃ sm : MSCSamplingAE.MSCSamplingFixed.{u, v} X,
      sm.law = M.m ∧ ∀ k : ℕ, sm.emp k = M.emp k ω := by
  filter_upwards [M.emp_eventually_close_ae] with ω hω
  exact ⟨⟨M.m, fun k => M.emp k ω, hω⟩, rfl, fun _ => rfl⟩

/-- ★★★ **ASTRAL 的几乎必然统计一致性（基因树层）**：假设面**零 `hmean`**。

证明 = `emp_eventually_close_ae` ＋ 库内
`MSCSamplingAE.astral_statisticallyConsistent_fixed`（该定理本身**没有** `hmean` 参数）。 -/
theorem astral_statisticallyConsistent_ae_of_geneTrees (M : GeneTreeModel.{u, v, w} X)
    {E : QuartetFreq X → QuartetTree.{u, v} X} (hE : ∀ D, IsASTRAL D (E D))
    (hNE : ∃ q : QuartetChoice X, ¬ IsTrueChoice M.m q) :
    ∀ᵐ ω ∂M.sampleMeasure, ∃ N : ℕ, ∀ k ≥ N, IsTrueChoice M.m (E (M.emp k ω)).q := by
  filter_upwards [M.emp_eventually_close_ae] with ω hω
  exact MSCSamplingAE.astral_statisticallyConsistent_fixed
    ⟨M.m, fun k => M.emp k ω, hω⟩ hE hNE

/-- ★★★ **端到端：从物种树出发的真·几乎必然一致（树层）** —— **W13g 的主定理**。

```text
∀ᵐ ω ∂(Measure.infinitePi (fun _ : ℕ => M.ν)), ∃ N, ∀ k ≥ N,
    Nonempty (Iso (E (emp k ω)).tree M.m.tree)
```

**假设面**（逐条，`set_option autoImplicit false` 下无隐式变量）：

* `M : GeneTreeModel X` —— 即 `ν` 是概率测度 ＋ `freqOf` 逐点可测 ＋ `m : MSCFreq X` ＋ `hpush`；
  ⚠️ **其中不含** `hmean` / `hint` / `hindep` / `hident`；
* `hT : M.m.tree.IsBinary`、`hE : ∀ D, IsASTRAL D (E D)`、`hEbin : ∀ D, (E D).tree.IsBinary`
  —— 真树与估计量的**算法性质**；
* `hNE` —— 真 quartet 不与任何竞争 quartet 并列（库内既有口径，用于取正间隙 `δ`）。

证明 = `astral_statisticallyConsistent_ae_of_geneTrees`（quartet 层）
＋ `QuartetDecidesTree`（quartet 一致 ⇒ 树同构）。 -/
theorem astral_iso_ae_of_geneTrees (M : GeneTreeModel.{u, v, w} X) (hT : M.m.tree.IsBinary)
    {E : QuartetFreq X → QuartetTree.{u, v} X} (hE : ∀ D, IsASTRAL D (E D))
    (hEbin : ∀ D, (E D).tree.IsBinary)
    (hNE : ∃ q : QuartetChoice X, ¬ IsTrueChoice M.m q) :
    ∀ᵐ ω ∂M.sampleMeasure, ∃ N : ℕ, ∀ k ≥ N,
      Nonempty (Iso (E (M.emp k ω)).tree M.m.tree) := by
  filter_upwards [M.astral_statisticallyConsistent_ae_of_geneTrees hE hNE] with ω hω
  obtain ⟨N, hN⟩ := hω
  exact ⟨N, fun k hk =>
    QuartetDecidesTree X (E (M.emp k ω)) M.m.toQuartetTree (hEbin _) hT (hN k hk)⟩

end GeneTreeModel

/-! ## 5. ★D 反空洞：`GeneTreeModel` 的显式居民

### 5.1 ★D 判定（**先判真假，再谈怎么证**）

**结论：`hpush` 与 `MSCFreq.majorizes` 可以同时满足** ✓ —— 见 §5.3 的显式居民。

⚠️ **但「最省事」的那个候选居民是假的** ✗：取 `G = Bool`、公平硬币、两棵基因树各 `1/2`、
分别展示 `01|23` 与 `02|13`，且**每棵树的表都是点质量**时，平均后两个 quartet 类**并列**
（各 `1/4`），而 `MSCFreq.majorizes` 要的是**严格**不等式 ⇒ **`majorizes` 失败**
⇒ 该候选**不是** `GeneTreeModel` 的居民。两条出路：

1. **权重不等**（本文件采用，见 §5.3）；或
2. **表不是点质量**（在一类上多放一点质量）。

数值复核（含失败候选的显式见证）见 `scripts/msc/w13g_gap_check.py`。 -/

/-- `Split.swap` **没有不动点**（`Split` 的两侧都非空）：`s.swap ≠ s`。 -/
theorem split_swap_ne_self {α : Type*} [Fintype α] [DecidableEq α] (s : Split α) :
    s.swap ≠ s := by
  intro h
  have hb : s.sideB = s.sideA := by
    have h1 := congrArg Split.sideA h
    rwa [Split.swap_sideA] at h1
  obtain ⟨x, hx⟩ := s.nonempty 0
  have hx' : x ∈ s.sideB := by rw [hb]; exact hx
  rw [Split.sideB_eq_sdiff, Finset.mem_sdiff] at hx'
  exact hx'.2 hx

/-- **点质量 quartet 表**：在 `c S hS` 及其 `swap` 上各放 `1/2`（有向口径），其余为 `0`。

这是「单棵基因树在 `S` 上展示 quartet `c S hS`」的退化频率表。 -/
noncomputable abbrev pointTable (c : (S : Finset X) → (hS : S.card = 4) → Split ↥S) :
    QuartetFreq X where
  p S hS r := if r = c S hS then (1 / 2 : ℝ) else if r = (c S hS).swap then (1 / 2 : ℝ) else 0
  p_nonneg S hS r := by
    by_cases h1 : r = c S hS
    · simp [h1]
    · by_cases h2 : r = (c S hS).swap <;> simp [h1, h2]
  p_sum_one S hS := by
    set a := c S hS with ha
    have hne : a ≠ a.swap := fun h => split_swap_ne_self a h.symm
    have hne' : a.swap ≠ a := fun h => hne h.symm
    have hterm : ∀ r : Split ↥S,
        (if r = a then (1 / 2 : ℝ) else if r = a.swap then (1 / 2 : ℝ) else 0)
        = (if r = a then (1 / 2 : ℝ) else 0)
          + (if r = a.swap then (1 / 2 : ℝ) else 0) := by
      intro r
      by_cases h1 : r = a
      · rw [h1]; simp [hne]
      · by_cases h2 : r = a.swap
        · rw [h2]; simp [hne']
        · simp [h1, h2]
    rw [Finset.sum_congr rfl (fun r _ => hterm r), Finset.sum_add_distrib,
      Finset.sum_ite_eq' Finset.univ a (fun _ => (1 / 2 : ℝ)),
      Finset.sum_ite_eq' Finset.univ a.swap (fun _ => (1 / 2 : ℝ))]
    simp only [Finset.mem_univ, ↓reduceIte]
    norm_num
  p_swap S hS r := by
    have h1 : (r.swap = c S hS) ↔ (r = (c S hS).swap) := by
      constructor
      · intro h; rw [← h, Split.swap_swap]
      · intro h; rw [h, Split.swap_swap]
    have h2 : (r.swap = (c S hS).swap) ↔ (r = c S hS) := by
      constructor
      · intro h; exact Split.swap_injective h
      · intro h; rw [h]
    have hne : c S hS ≠ (c S hS).swap := fun h => split_swap_ne_self (c S hS) h.symm
    have hne' : (c S hS).swap ≠ c S hS := fun h => hne h.symm
    simp only [h1, h2]
    by_cases hP : r = c S hS
    · rw [hP]; simp [hne]
    · by_cases hQ : r = (c S hS).swap
      · rw [hQ]; simp [hne']
      · simp [hP, hQ]

/-- 点质量表在 `c S hS` 上取值 `1/2`。 -/
theorem pointTable_p_self (c : (S : Finset X) → (hS : S.card = 4) → Split ↥S)
    (S : Finset X) (hS : S.card = 4) : (pointTable c).p S hS (c S hS) = 1 / 2 := by
  simp

/-- 点质量表在 `c S hS` 与其 `swap` 之外取值 `0`。 -/
theorem pointTable_p_of_ne (c : (S : Finset X) → (hS : S.card = 4) → Split ↥S)
    (S : Finset X) (hS : S.card = 4) {r : Split ↥S} (h1 : r ≠ c S hS)
    (h2 : r ≠ (c S hS).swap) : (pointTable c).p S hS r = 0 := by
  simp [h1, h2]

/-- 点质量表处处 `≤ 1/2`。 -/
theorem pointTable_p_le (c : (S : Finset X) → (hS : S.card = 4) → Split ↥S)
    (S : Finset X) (hS : S.card = 4) (r : Split ↥S) : (pointTable c).p S hS r ≤ 1 / 2 := by
  by_cases h1 : r = c S hS
  · simp [h1]
  · by_cases h2 : r = (c S hS).swap <;> simp [h1, h2]

/-- 两张频率表的**凸组合**（权重非负、和为 `1`）—— 仍是 `QuartetFreq`。 -/
noncomputable abbrev mixFreq (D E : QuartetFreq X) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) : QuartetFreq X where
  p S hS r := a * D.p S hS r + b * E.p S hS r
  p_nonneg S hS r :=
    add_nonneg (mul_nonneg ha (D.p_nonneg S hS r)) (mul_nonneg hb (E.p_nonneg S hS r))
  p_sum_one S hS := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, D.p_sum_one S hS,
      E.p_sum_one S hS, mul_one, mul_one, hab]
  p_swap S hS r := by
    rw [D.p_swap S hS r, E.p_swap S hS r]

/-! ### 5.2 公平硬币上的积分 -/

/-- 公平硬币测度（`Phylo.Stat.EmpiricalConvergence.coin`）上的积分：
`∫ b, f b ∂coin = (f true + f false) / 2`。 -/
theorem integral_coin (f : Bool → ℝ) :
    ∫ b : Bool, f b ∂EmpiricalConvergence.coin = (f true + f false) / 2 := by
  have hcount : ∫ b : Bool, f b ∂(Measure.count : Measure Bool) = f true + f false := by
    rw [integral_count, Fintype.sum_bool]
  rw [EmpiricalConvergence.coin, integral_smul_measure, hcount, smul_eq_mul,
    ENNReal.toReal_inv, ENNReal.toReal_ofNat]
  ring

/-! ### 5.3 ★D 的显式居民（`X = Fin 4`、`G = Bool`、公平硬币） -/

open Phylo.Stat.MSCProof

/-- `Fin 4` 上**另一个** quartet 类的显式 split：`sideA4 = {0, 2}`（即 `02|13`）。 -/
noncomputable def altChoice (S : Finset (Fin 4)) (hS : S.card = 4) : Split ↥S :=
  Phylo.splitOf (Finset.univ.filter fun x : ↥S => (x : Fin 4) ∈ ({0, 2} : Finset (Fin 4)))
    ⟨⟨0, mem_of_card_four S hS 0⟩, by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      simp⟩
    ⟨⟨1, mem_of_card_four S hS 1⟩, by
      simp only [Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and]
      simp⟩

theorem altChoice_sideA (S : Finset (Fin 4)) (hS : S.card = 4) :
    (altChoice S hS).sideA
      = Finset.univ.filter (fun x : ↥S => (x : Fin 4) ∈ ({0, 2} : Finset (Fin 4))) :=
  Phylo.splitOf_sideA _ _ _

theorem altChoice_sideA4 (S : Finset (Fin 4)) (hS : S.card = 4) :
    sideA4 (altChoice S hS) = ({0, 2} : Finset (Fin 4)) := by
  obtain rfl : S = Finset.univ := eq_univ_of_card_four S hS
  rw [sideA4, altChoice_sideA]
  exact image_liftU _

/-- 真 quartet 类（`01|23`）与 `02|13` 类**不同**（`sideA4` 不同）。 -/
theorem qChoice_ne_altChoice (S : Finset (Fin 4)) (hS : S.card = 4) :
    (mscQuartetTree).q S hS ≠ altChoice S hS := by
  intro h
  have h1 : sideA4 (S := S) (qSplit S hS) = sideA4 (S := S) (altChoice S hS) :=
    congrArg (sideA4 (S := S)) h
  rw [sideA4_qSplit, altChoice_sideA4] at h1
  exact absurd h1 (by decide)

/-- 真 quartet 类（`01|23`）与 `02|13` 类的 **`swap`** 也**不同**。 -/
theorem qChoice_ne_altChoice_swap (S : Finset (Fin 4)) (hS : S.card = 4) :
    (mscQuartetTree).q S hS ≠ (altChoice S hS).swap := by
  have h2 : sideA4 (S := S) (altChoice S hS).swap = ({1, 3} : Finset (Fin 4)) := by
    obtain rfl : S = Finset.univ := eq_univ_of_card_four S hS
    rw [sideA4_swap, altChoice_sideA4]
    decide
  intro h
  have h1 : sideA4 (S := S) (qSplit S hS) = sideA4 (S := S) (altChoice S hS).swap :=
    congrArg (sideA4 (S := S)) h
  rw [sideA4_qSplit, h2] at h1
  exact absurd h1 (by decide)

/-- 反方向的同一不等式（`altChoice` 写在左边，便于 `pointTable_p_of_ne` 使用）。 -/
theorem altChoice_ne_qChoice (S : Finset (Fin 4)) (hS : S.card = 4) :
    altChoice S hS ≠ (mscQuartetTree).q S hS :=
  (qChoice_ne_altChoice S hS).symm

/-- 反方向的同一不等式（`swap` 口径）。 -/
theorem altChoice_ne_qChoice_swap (S : Finset (Fin 4)) (hS : S.card = 4) :
    altChoice S hS ≠ ((mscQuartetTree).q S hS).swap := by
  intro h
  refine qChoice_ne_altChoice_swap S hS ?_
  rw [h, Split.swap_swap]

/-- ★D 见证的第一张表：点质量在**真** quartet 类 `01|23` 上。 -/
noncomputable abbrev witnessQTable : QuartetFreq (Fin 4) :=
  pointTable fun S hS => (mscQuartetTree).q S hS

/-- ★D 见证的第二张表：点质量在另一个 quartet 类 `02|13` 上。 -/
noncomputable abbrev witnessATable : QuartetFreq (Fin 4) :=
  pointTable altChoice

/-- ★D 见证的「两棵树混合」表：`(1/2) • Q + (1/2) • A`。 -/
noncomputable abbrev witnessMixTable : QuartetFreq (Fin 4) :=
  mixFreq witnessQTable witnessATable (1 / 2) (1 / 2) (by norm_num) (by norm_num) (by norm_num)

/-- ★D 见证的**理论频率表**：`(3/4) • Q + (1/4) • A`
（`01|23` 上 `3/8`、`02|13` 上 `1/8`、其余 `0` ⇒ **严格唯一最大**）。 -/
noncomputable abbrev witnessFreq : QuartetFreq (Fin 4) :=
  mixFreq witnessQTable witnessATable (3 / 4) (1 / 4) (by norm_num) (by norm_num) (by norm_num)

/-- ★D 见证的**理论律**：真树 `= 01|23` 二叉树，频率表 `= witnessFreq`，且
**`majorizes` 成立**（`3/8 > 1/8 ≥` 其余）。 -/
noncomputable def witnessMSC : MSCFreq (Fin 4) where
  toQuartetTree := mscQuartetTree
  freq := witnessFreq
  majorizes := by
    intro S hS r hr hrs
    have hpq : witnessFreq.p S hS ((mscQuartetTree).q S hS) = 3 / 8 := by
      show (3 / 4) * witnessQTable.p S hS ((mscQuartetTree).q S hS)
        + (1 / 4) * witnessATable.p S hS ((mscQuartetTree).q S hS) = 3 / 8
      rw [pointTable_p_self, pointTable_p_of_ne _ S hS (qChoice_ne_altChoice S hS)
        (qChoice_ne_altChoice_swap S hS)]
      norm_num
    have hpr : witnessFreq.p S hS r ≤ 1 / 8 := by
      show (3 / 4) * witnessQTable.p S hS r + (1 / 4) * witnessATable.p S hS r ≤ 1 / 8
      rw [pointTable_p_of_ne _ S hS hr hrs]
      have h := pointTable_p_le altChoice S hS r
      linarith
    show witnessFreq.p S hS r < witnessFreq.p S hS ((mscQuartetTree).q S hS)
    rw [hpq]
    linarith

/-- ★★★ **★D 的显式居民（反空洞）**：`X = Fin 4`、`G = Bool`、`ν = coin`（公平硬币）。

* `freqOf false = witnessQTable`（点质量在 `01|23` 类）；
* `freqOf true = witnessMixTable`（`01|23` 与 `02|13` 各半）；
* 两者**平均** = `witnessFreq` ⇒ **`hpush`** ✓（`integral_coin` ＋ `ring`）；
* 平均表在 `01|23` 上 `3/8`、`02|13` 上 `1/8` ⇒ **`majorizes`** ✓（`witnessMSC`）。

⇒ **`hpush` 与 `majorizes` 可同时满足，`GeneTreeModel` 不是空类型。** -/
noncomputable abbrev witnessModel : GeneTreeModel.{0, 0, 0} (Fin 4) where
  G := Bool
  ν := EmpiricalConvergence.coin
  freqOf b := match b with
    | true => witnessMixTable
    | false => witnessQTable
  hmeas S hS q := measurable_of_finite _
  m := witnessMSC
  hpush S hS q := by
    show (∫ b : Bool, (match b with
        | true => witnessMixTable
        | false => witnessQTable).p S hS q ∂EmpiricalConvergence.coin)
      = witnessFreq.p S hS q
    rw [integral_coin]
    show (((1 / 2) * witnessQTable.p S hS q + (1 / 2) * witnessATable.p S hS q)
        + witnessQTable.p S hS q) / 2
      = (3 / 4) * witnessQTable.p S hS q + (1 / 4) * witnessATable.p S hS q
    ring

/-- ★★ **非空性（反空洞）**：`Fin 4` 上 `GeneTreeModel` **有居民**。 -/
theorem geneTreeModel_nonempty : Nonempty (GeneTreeModel.{0, 0, 0} (Fin 4)) :=
  ⟨witnessModel⟩

/-- ★★ **居民的 `freqOf` 不是常值** —— 基因树确实在随机（故经验表确实在跑大数定律，
不是「恒定输出」）。两张表在 `02|13` 上取值 `1/2` 与 `0`。 -/
theorem witnessModel_freqOf_ne :
    witnessModel.freqOf true ≠ witnessModel.freqOf false := by
  have h4 : (Finset.univ : Finset (Fin 4)).card = 4 := by decide
  intro h
  have h1 := congrArg (fun D : QuartetFreq (Fin 4) =>
    D.p Finset.univ h4 (altChoice Finset.univ h4)) h
  have hqA : (mscQuartetTree).q Finset.univ h4 ≠ altChoice Finset.univ h4 :=
    qChoice_ne_altChoice _ _
  have hqA' : (mscQuartetTree).q Finset.univ h4
      ≠ (altChoice Finset.univ h4).swap := qChoice_ne_altChoice_swap _ _
  have hL : witnessMixTable.p Finset.univ h4 (altChoice Finset.univ h4) = 1 / 4 := by
    show (1 / 2) * witnessQTable.p Finset.univ h4 (altChoice Finset.univ h4)
      + (1 / 2) * witnessATable.p Finset.univ h4 (altChoice Finset.univ h4) = 1 / 4
    rw [pointTable_p_of_ne _ _ _ (altChoice_ne_qChoice _ _) (altChoice_ne_qChoice_swap _ _),
      pointTable_p_self]
    norm_num
  have hR : witnessQTable.p Finset.univ h4 (altChoice Finset.univ h4) = 0 :=
    pointTable_p_of_ne _ _ _ (altChoice_ne_qChoice _ _) (altChoice_ne_qChoice_swap _ _)
  rw [hL, hR] at h1
  exact absurd h1 (by norm_num)

/-- ★ **规格 §4.1 的同族反例（基因树层）**：**固定 `k = 1`** 时经验表**不是**常数 `m.freq`
—— 它是**依赖实现**的随机量。这里把 `ω 0 = true` 的那一半显式写出：
`emp 1 ω = freqOf true = witnessMixTable`，而它在 `02|13` 上取 `1/4`，不等于
`witnessFreq` 的 `1/8`。

⇒ 这正是「`k` 必须 `→ ∞`」这条硬性要求（规格 §4①）在基因树层的**可编译护栏**；
与 `astral_iso_ae_of_geneTrees` 的 `∃ N, ∀ k ≥ N` 形态**不矛盾**（那里 `k` 无界增长）。 -/
theorem witnessModel_emp_one_ne (ω : ℕ → Bool) (hω : ω 0 = true) :
    (witnessModel).emp 1 ω ≠ witnessModel.m.freq := by
  have h4 : (Finset.univ : Finset (Fin 4)).card = 4 := by decide
  have hemp : ((witnessModel).emp 1 ω).p Finset.univ h4 (altChoice Finset.univ h4)
      = witnessMixTable.p Finset.univ h4 (altChoice Finset.univ h4) := by
    rw [(witnessModel).emp_p 1 ω Finset.univ h4 (altChoice Finset.univ h4)]
    simp only [one_ne_zero, ↓reduceIte, Finset.sum_range_one, hω, Nat.cast_one, inv_one,
      one_mul]
  have hL : witnessMixTable.p Finset.univ h4 (altChoice Finset.univ h4) = 1 / 4 := by
    show (1 / 2) * witnessQTable.p Finset.univ h4 (altChoice Finset.univ h4)
      + (1 / 2) * witnessATable.p Finset.univ h4 (altChoice Finset.univ h4) = 1 / 4
    rw [pointTable_p_of_ne _ _ _ (altChoice_ne_qChoice _ _) (altChoice_ne_qChoice_swap _ _),
      pointTable_p_self]
    norm_num
  have hR : witnessFreq.p Finset.univ h4 (altChoice Finset.univ h4) = 1 / 8 := by
    show (3 / 4) * witnessQTable.p Finset.univ h4 (altChoice Finset.univ h4)
      + (1 / 4) * witnessATable.p Finset.univ h4 (altChoice Finset.univ h4) = 1 / 8
    rw [pointTable_p_of_ne _ _ _ (altChoice_ne_qChoice _ _) (altChoice_ne_qChoice_swap _ _),
      pointTable_p_self]
    norm_num
  intro h
  have hR' : witnessModel.m.freq.p Finset.univ h4 (altChoice Finset.univ h4) = 1 / 8 := hR
  have h1 := congrArg (fun D : QuartetFreq (Fin 4) =>
    D.p Finset.univ h4 (altChoice Finset.univ h4)) h
  rw [hemp, hL, hR'] at h1
  exact absurd h1 (by norm_num)

/-! ## 6. ★8④ 退化一致性检查：`ν` 为 Dirac（每棵基因树都是同一张**确定**的表）

取 `ν = Measure.dirac false`、`freqOf ≡ m.freq`（「**每棵基因树确定地给出同一张表**」），
则经验表**恒等于** `m.freq`（对一切 `k`、一切 `ω`），于是 §3 的 a.e. 结论
**退化为库内 `MSCSamplingFixed.converges` 的确定性形态**（`N = 0` 即可）。
这是「新结论没有写歪」的**最强探针**（规格 §8④）。 -/

/-- 退化模型：`G = Bool`、`ν = Measure.dirac false`、`freqOf` 常值 `= m.freq`。 -/
noncomputable abbrev diracModel (m : MSCFreq.{u, v} X) : GeneTreeModel.{u, v, 0} X where
  G := Bool
  ν := Measure.dirac false
  freqOf _ := m.freq
  hmeas _ _ _ := measurable_const
  m := m
  hpush _ _ _ := by rw [integral_dirac]

/-- ★8④ **退化一致性**：常值模型下经验表**恒等于**理论表（对一切 `k`、一切 `ω`）。 -/
theorem diracModel_emp_eq (m : MSCFreq.{u, v} X) (k : ℕ) (ω : ℕ → (diracModel m).G) :
    (diracModel m).emp k ω = (diracModel m).m.freq := by
  refine (QuartetFreq.eq_iff_p (D := (diracModel m).emp k ω)
    (D' := (diracModel m).m.freq)).mpr ?_
  funext S hS q
  rw [(diracModel m).emp_p k ω S hS q]
  by_cases hk : k = 0
  · simp only [hk, ↓reduceIte]
  · simp only [hk, ↓reduceIte]
    have hk0 : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk
    have hconst : ∀ j ∈ Finset.range k,
        ((diracModel m).freqOf (ω j)).p S hS q = (diracModel m).m.freq.p S hS q :=
      fun j _ => rfl
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      ← mul_assoc, inv_mul_cancel₀ hk0, one_mul]

/-- ★8④ **退化一致性（结论）**：`MSCSamplingFixed.converges` 的**确定性**形态在常值模型下
以 `N = 0` 成立 —— 即新结论确实**退回**库内既有的确定性大数定律。 -/
theorem diracModel_converges (m : MSCFreq.{u, v} X) (ω : ℕ → (diracModel m).G) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ k ≥ N,
      FreqClose ((diracModel m).emp k ω) (diracModel m).m.freq ε :=
  fun ε hε => ⟨0, fun k _ => by
    show ∀ (S : Finset X) (hS : S.card = 4) (q : Split ↥S),
      |((diracModel m).emp k ω).p S hS q - ((diracModel m).m.freq).p S hS q| < ε
    intro S hS q
    rw [diracModel_emp_eq m k ω, sub_self, abs_zero]
    exact hε⟩

end Phylo.Stat.GeneTreeSamplingAE
