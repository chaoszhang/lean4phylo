/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.Stat.GeneTreeSamplingAE
import Phylo.Stat.SiteWeightMeasurable
import Phylo.Stat.MultiLocusLaw

set_option autoImplicit false

/-!
# `Phylo.Stat.GeneTreeHmeasDischarge` —— 缺口 **B2** 从「模型字段」变成「位点层定理」（W13i）

## 0. 这个文件做什么（三件）

1. ★★ **消掉 `GeneTreeModel.hmeas`**：`Phylo/Stat/GeneTreeSamplingAE.lean` 的 `GeneTreeModel` 把

   ```text
   hmeas : ∀ (S) (hS) (q), Measurable fun g => (freqOf g).p S hS q
   ```

   当作**模型字段**（该文件 §5 诚实边界把它标为 W13 规格 §6 的缺口 **B2**）。
   本文件给出一个**不需要 `hmeas` 作为输入**的构造子 `GeneTreeModel.ofSiteWeights`：
   位点层（W13a 的 `measurable_geneScore` 一族）**供出**分量的可测性，
   于是 `hmeas` 由 `Measurable.comp` ＋ 有限和**推出**（§1–§4）。

2. ★ **把 `hmean`-free 的覆盖扩到 `MultiLocusLaw`**（规格 §7「不另起炉灶」）：
   `Phylo/Stat/MultiLocusLaw.lean` 的四个端点（约 `:277` / `:307` / `:343` / `:374`）挂着
   `hint` / `hindep` / `hident` / `hmean` 四条假设；其中 `hmean` 就是 `GeneTreeModel.hpush`
   （基因树分布 = MSC 理论频率的**推前**）。本文件在**新文件**里给出变体 `…_of_geneTrees`
   （**不改**任何既有声明）：假设面里 `hmean` **与** iid 三件套**全部消失**
   （后三条由 `GeneTreeModel.sampleMeasure` 的无穷乘积测度**构造**出来，见 W13g §1.4）。

3. ★D **口径裁定（逐条，先判真假）**：

   * `MultiLocusLaw` 的基因座表值随机变量 `locus : Ω₀ → QuartetFreq X` **就是**
     「每棵基因树给出一张 quartet 频率表」⇒ **基因树层是它的正确工具** ✓；
   * `EmpiricalConvergence.variance_empFreq_gap`（`:379`）**不是** —— 它是**位点层**对象
     （`ind : Ω₀ → …` 是**单位点**的观测函数，`hmean` 是**位点**的边缘律），
     且把它的第 5 个前提 `hmean` 删掉之后**命题为假**（见 §7 的显式反例），
     故**不**给它造变体 ✗。

## 1. ★D：为什么「`freqOf` 的分量 = `geneScore`」是**做不出来**的

规格/派单的措辞是「`freqOf` 的每个分量由 `geneScore` 沿某个可测参数化给出」。逐条核过之后，
**字面版本为假**，必须换一个诚实形态：

* `geneScore S l lx T = ∑_σ wJCR T σ · patternProb (canonLen S l lx) (σ ∘ perm S)`
  （`Phylo/Stat/CASTERGeneTree.lean`），而 `wJCR T σ = (wJC T σ).toReal` 取值于 `{1, −1/2, 0}`
  —— 库内 `Phylo/Stat/CASTERWeights.lean` 已证 `card_neg`：**恰有 `48` 个模式取 `−1/2`**。
  ⇒ 一个「分量就是 `geneScore`」的表**可以有负分量** ⇒ `QuartetFreq.p_nonneg` **必然失败**
  ⇒ 它根本不是 `QuartetFreq`。
* 而且 `geneScore` 是一个**估计量**（ASTRAL 位点权重），不是概率：
  库内**没有**（也不应有）`∑_{T : Topo} geneScore S l lx T = 1`。

⇒ **诚实形态**：`geneScore` 进入的**不是表的取值**，而是**可测的「单位分解」驱动量**：

```text
siteCoeff φ T g := ((geneScore T (φ g).1 (φ g).2 T)² + 1) / ∑ T', ((geneScore T' (φ g).1 (φ g).2 T')² + 1)
siteTable D φ g := ∑ T : Topo, siteCoeff φ T g * (D T).p     （`D` 是任意的基准表族）
```

`siteCoeff` **非负**、**对 `T` 求和为 `1`**（分母 ≥ 3），且它的**可测性**是
`measurable_geneScore_comp`（W13a 的 B2 主件）＋ `Measurable.pow_const` ＋ `Measurable.add`
＋ `Measurable.div` ＋ `Finset.measurable_sum`（有限和）**推出来的**。
⇒ 于是 `siteTable` 是一张**真正的** `QuartetFreq`（三条字段逐条由 `siteCoeff` 的性质给出），
而它的**逐分量可测性不再需要假设** —— 这就是「B2 由位点层供应的定理」。

⚠️ **这个换法不是「绕过」**：负权重不但不损害机制，反而是**必须**走这条路的原因；
`(·)²` 把任意实值权重压成非负，归一化把它变成单位分解 —— 而**可测性沿这两步都不丢**
（`Measurable.pow_const` / `Measurable.div` 都是 W13a 器材的直接复合）。

## 2. 一般机制（与 `geneScore` 无关的那一半）

`hmeas_of_measurable_param`：可测参数化 `φ : G → β` **搬运**表族 `F : β → QuartetFreq X` 的
逐分量可测性（纯 `Measurable.comp`）。这是下面所有构造的骨架，也说明了 `hmeas` 的本质：
**它是「表族沿参数的拉回」的可测性，不是一个独立的模型条件。**

## 3. ★8④ 退化一致性

* `convexCombo_const`：基准表族为**常值**时（＝位点层不产生任何变异，对应 `ρ ≡ 1`、`r ≡ 1`），
  `siteTable` **恒等于**该常值表 —— 即新构造退回库内的确定性形态（`N = 0`）。
* `siteWeightModel`（§5）：`Fin 4` 上的**显式居民**，`freqOf ≡ witnessFreq = witnessMSC.freq`
  ⇒ `meanFreq = m.freq`（`siteWeightModel_meanFreq`），与 W13g 的 `diracModel` 同族。
  ⇒ **反空洞**：`GeneTreeModel.ofSiteWeights` **不是空构造**。

## 4. 诚实边界（逐条）

| 条目 | 状态 |
|---|---|
| `hmeas` 对**位点层构造的** `freqOf` 是定理（B2 消解） | ✅ 本文件（`measurable_siteTable` / `ofSiteWeights`） |
| 「分量**就是** `geneScore`」 | ❌ **为假**（§1：负权重 ⇒ `p_nonneg` 失败）；本文件用单位分解形态替代 |
| `hpush`（缺口 G2：基因树分布 = MSC 推前） | ⚠️ **仍是输入**（与 W13g 一致；那是缺口 B1 的完整版，规格 §9 明确不在本批内） |
| `MultiLocusLaw` 的 `hmean` 被消掉 | ✅ 本文件（§6 的 `…_of_geneTrees`） |
| `MultiLocusLaw` 的 `hint` / `hindep` / `hident` 被消掉 | ✅ **顺带**（`sampleMeasure` 是构造出来的无穷乘积测度） |
| `variance_empFreq_gap` 的 `hmean` 被消掉 | ❌ **不可能**：删掉后命题为**假**（§7 反例）；**不**造变体 |
| `GeneTreeModel` 的既有声明 | ✅ **一字未动**（★C：只加变体）；`hpush` 仍是其字段 |
| 上游 `kingmanMSCMeasure` → 整棵树的分布 | ❌ 缺口 B1 完整版，不在本批（规格 §9）|
-/

noncomputable section

open Filter MeasureTheory ProbabilityTheory Finset
open scoped Topology ENNReal NNReal

namespace Phylo.Stat.GeneTreeHmeasDischarge

open Phylo.Stat.CASTERWeights (Topo Val wJC wJCR perm)
open Phylo.Stat.CASTERGeneTree (canonLen geneScore)
open Phylo.Stat.GeneTreeSamplingAE (GeneTreeModel)
open Phylo.Stat.MultiLocusLaw (multiLocusData multiLocusData_avg_p multiLocus_maximizer_agrees_close)

universe u v w

variable {X : Type u} [Fintype X] [DecidableEq X]

/-! ## 1. 一般机制：可测参数化**搬运** `hmeas`（纯 `Measurable.comp`） -/

/-- ★★ **`hmeas` 的搬运引理**：若表族 `F : β → QuartetFreq X` 的每个分量在 `β` 上可测，
则沿**任意可测参数化** `φ : G → β` 拉回之后仍然可测。

⇒ 这就是 `GeneTreeModel.hmeas` 的**本质**：它是「表族沿参数的可测性」，不是独立模型条件。
证明是 `Measurable.comp` 一步（无任何额外假设）。 -/
theorem hmeas_of_measurable_param {G : Type w} [MeasurableSpace G]
    {β : Type*} [MeasurableSpace β] (φ : G → β) (hφ : Measurable φ)
    (F : β → QuartetFreq X)
    (hF : ∀ (S : Finset X) (hS : S.card = 4) (q : Split ↥S),
      Measurable fun b => (F b).p S hS q) :
    ∀ (S : Finset X) (hS : S.card = 4) (q : Split ↥S),
      Measurable fun g : G => (F (φ g)).p S hS q := by
  intro S hS q
  convert (hF S hS q).comp hφ using 1
  funext g
  rfl

/-! ## 2. 位点层供应的可测系数（`geneScore` 驱动） -/

/-- ★★ **位点层系数**（`Topo` 上的**单位分解**，由 `geneScore` 驱动）：

```text
siteCoeff φ T g = ((geneScore T (φ g).1 (φ g).2 T)² + 1) / ∑ T', ((geneScore T' (φ g).1 (φ g).2 T')² + 1)
```

* 分子 `(·)² + 1 ≥ 1` ⇒ **严格正**（故不能被 `0` 除、也不会退化）；
* 分母 `= ∑ T' (…² + 1) ≥ 3`（`Topo` 有 3 个元素，每项 ≥ 1）；
* ⇒ 非负 ＋ 求和为 `1`（`siteCoeff_nonneg` / `siteCoeff_sum_one`），即**单位分解**；
* ⇒ 可测（`measurable_siteCoeff`），**完全**由 W13a 的 `measurable_geneScore_comp` 推出。

⚠️ 为什么是「平方 ＋ 归一化」而不是直接用 `geneScore`：见文件头 §1 —— `wJCR` 有 `48` 个模式取
`−1/2`，故 `geneScore` 可负，直接拿它当分量会让 `QuartetFreq.p_nonneg` 失败。 -/
noncomputable def siteCoeff {G : Type w} [MeasurableSpace G]
    (φ : G → (Fin 4 → ℝ) × ℝ) (T : Topo) (g : G) : ℝ :=
  ((geneScore T (φ g).1 (φ g).2 T) ^ 2 + 1)
    / ∑ T' : Topo, ((geneScore T' (φ g).1 (φ g).2 T') ^ 2 + 1)

/-- ★★ **缺口 B2 的实质步骤**：`siteCoeff` 关于 `g` 可测。

证明只用 W13a 的 `measurable_geneScore_comp`（＝ `measurable_geneScore` 与 `Measurable.comp`）
＋ `Measurable.pow_const` ＋ `Measurable.add` ＋ `Measurable.div` ＋ `Finset.measurable_sum`
（**有限和**）—— 没有任何新的可测性假设。 -/
theorem measurable_siteCoeff {G : Type w} [MeasurableSpace G]
    (φ : G → (Fin 4 → ℝ) × ℝ) (hφ : Measurable φ) (T : Topo) :
    Measurable (siteCoeff φ T) := by
  have hbase : ∀ T' : Topo, Measurable (fun g : G => geneScore T' (φ g).1 (φ g).2 T') :=
    fun T' => Phylo.Stat.SiteWeightMeasurable.measurable_geneScore_comp T' T' hφ
  have hnum : Measurable (fun g : G => (geneScore T (φ g).1 (φ g).2 T) ^ 2 + 1) := by
    have h := ((hbase T).pow_const 2).add (measurable_const : Measurable fun _ : G => (1 : ℝ))
    convert h using 1
  have hden : Measurable
      (fun g : G => ∑ T' : Topo, ((geneScore T' (φ g).1 (φ g).2 T') ^ 2 + 1)) := by
    have h := Finset.measurable_sum (Finset.univ : Finset Topo) (fun T' _ =>
      ((hbase T').pow_const 2).add (measurable_const : Measurable fun _ : G => (1 : ℝ)))
    convert h using 1
  have hdiv := hnum.div hden
  convert hdiv using 1
  funext g
  rfl

/-- ★★ `siteCoeff` 非负。 -/
theorem siteCoeff_nonneg {G : Type w} [MeasurableSpace G]
    (φ : G → (Fin 4 → ℝ) × ℝ) (T : Topo) (g : G) : 0 ≤ siteCoeff φ T g := by
  have hden_pos : 0 < ∑ T' : Topo, ((geneScore T' (φ g).1 (φ g).2 T') ^ 2 + 1) := by
    have h1 : ∀ T' : Topo, 0 ≤ (geneScore T' (φ g).1 (φ g).2 T') ^ 2 + 1 :=
      fun T' => by nlinarith [sq_nonneg (geneScore T' (φ g).1 (φ g).2 T')]
    have h2 : 0 < (geneScore Topo.ab_cd (φ g).1 (φ g).2 Topo.ab_cd) ^ 2 + 1 :=
      by nlinarith [sq_nonneg (geneScore Topo.ab_cd (φ g).1 (φ g).2 Topo.ab_cd)]
    have hle := Finset.single_le_sum (s := (Finset.univ : Finset Topo))
      (f := fun T' : Topo => (geneScore T' (φ g).1 (φ g).2 T') ^ 2 + 1) (fun T' _ => h1 T')
      (Finset.mem_univ Topo.ab_cd)
    linarith
  exact div_nonneg (by nlinarith [sq_nonneg (geneScore T (φ g).1 (φ g).2 T)]) hden_pos.le

/-- ★★★ **`siteCoeff` 是单位分解**：`∑ T, siteCoeff φ T g = 1`。

⇒ 这是「`geneScore` 用来驱动一张**概率**表」的关键一步（与它自身不是概率无关）。 -/
theorem siteCoeff_sum_one {G : Type w} [MeasurableSpace G]
    (φ : G → (Fin 4 → ℝ) × ℝ) (g : G) : (∑ T : Topo, siteCoeff φ T g) = 1 := by
  have hden_ne : (∑ T : Topo, ((geneScore T (φ g).1 (φ g).2 T) ^ 2 + 1)) ≠ 0 := by
    have h1 : ∀ T : Topo, 0 ≤ (geneScore T (φ g).1 (φ g).2 T) ^ 2 + 1 :=
      fun T => by nlinarith [sq_nonneg (geneScore T (φ g).1 (φ g).2 T)]
    have h2 : 0 < (geneScore Topo.ab_cd (φ g).1 (φ g).2 Topo.ab_cd) ^ 2 + 1 :=
      by nlinarith [sq_nonneg (geneScore Topo.ab_cd (φ g).1 (φ g).2 Topo.ab_cd)]
    have hle := Finset.single_le_sum (s := (Finset.univ : Finset Topo))
      (f := fun T : Topo => (geneScore T (φ g).1 (φ g).2 T) ^ 2 + 1) (fun T _ => h1 T)
      (Finset.mem_univ Topo.ab_cd)
    exact ne_of_gt (lt_of_lt_of_le h2 hle)
  simp only [siteCoeff, div_eq_mul_inv]
  rw [← Finset.sum_mul]
  exact mul_inv_cancel₀ hden_ne

/-! ## 3. 位点权重表：`Topo` 上的凸组合 -/

/-- ★★ **`Topo` 上、系数为非负单位分解的凸组合**（仍是 `QuartetFreq`；三条字段逐条真证）。

`Topo` 的三个元素＝三个（无向）quartet 类；`D` 给每一类一张基准表。
⚠️ 本构造**不**声明组合后的表一定满足 MSC 的 `majorizes`（那是 `MSCFreq` 的事，
与 `hmeas` 无关；`majorizes` 在 §5 里对具体居民单独核）。 -/
noncomputable def convexCombo (D : Topo → QuartetFreq X) (c : Topo → ℝ)
    (hc0 : ∀ T, 0 ≤ c T) (hc1 : ∑ T : Topo, c T = 1) : QuartetFreq X where
  p S hS q := ∑ T : Topo, c T * (D T).p S hS q
  p_nonneg S hS q := Finset.sum_nonneg fun T _ => mul_nonneg (hc0 T) ((D T).p_nonneg S hS q)
  p_sum_one S hS := by
    rw [Finset.sum_comm]
    have h : ∀ T : Topo, (∑ q : Split ↥S, c T * (D T).p S hS q) = c T := by
      intro T
      rw [← Finset.mul_sum, (D T).p_sum_one S hS, mul_one]
    rw [Finset.sum_congr rfl fun T _ => h T, hc1]
  p_swap S hS q := by
    refine Finset.sum_congr rfl fun T _ => ?_
    rw [(D T).p_swap S hS q]

/-- ★★ **位点权重表**：`D` 沿可测参数 `φ` 的 `geneScore` 驱动凸组合。

⚠️ 这个 `def` **没有** `hmeas` 参数 —— 它的逐分量可测性是定理（`measurable_siteTable`）。 -/
noncomputable def siteTable {G : Type w} [MeasurableSpace G] (D : Topo → QuartetFreq X)
    (φ : G → (Fin 4 → ℝ) × ℝ) (g : G) : QuartetFreq X :=
  convexCombo D (fun T => siteCoeff φ T g) (fun T => siteCoeff_nonneg φ T g)
    (siteCoeff_sum_one φ g)

/-- ★★★ **`hmeas` 被推出**（缺口 B2 的**位点层**答复）：
`siteTable D φ` 的每个分量关于 `g` 可测。

证明 = `siteCoeff` 的逐 `T` 可测性（`measurable_siteCoeff`，其源头是 W13a 的
`measurable_geneScore_comp`）＋ `Measurable.mul` ＋ `Finset.measurable_sum`（有限和）。 -/
theorem measurable_siteTable {G : Type w} [MeasurableSpace G] (D : Topo → QuartetFreq X)
    (φ : G → (Fin 4 → ℝ) × ℝ) (hφ : Measurable φ) :
    ∀ (S : Finset X) (hS : S.card = 4) (q : Split ↥S),
      Measurable fun g : G => (siteTable D φ g).p S hS q := by
  intro S hS q
  have hf : ∀ T : Topo, Measurable fun g : G => siteCoeff φ T g * (D T).p S hS q := fun T => by
    have h := (measurable_siteCoeff φ hφ T).mul
      (measurable_const : Measurable fun _ : G => (D T).p S hS q)
    convert h using 1
  have hsum : Measurable fun g : G => ∑ T : Topo, siteCoeff φ T g * (D T).p S hS q :=
    Finset.measurable_sum (Finset.univ : Finset Topo) (fun T _ => hf T)
  convert hsum using 1
  funext g
  rfl

/-! ## 4. ★★ 不需要 `hmeas` 的构造子 -/

/-- ★★★ **`GeneTreeModel` 的构造子（假设面里没有 `hmeas`）**。

输入是**位点层**的东西：可测的枝长参数化 `φ`、基准表族 `D`、概率测度 `ν`；
`freqOf` **由它们定义**（`siteTable D φ`），`hmeas` **由 `measurable_siteTable` 推出**。

⇒ **缺口 B2 从 `GeneTreeModel` 的字段变成了「由位点层供应的定理」** ✓：
`GeneTreeSamplingAE.GeneTreeModel.hmeas` 依然存在（★C：**不改**既有声明），
但凡是走本构造子的居民，**都不再需要**把可测性当假设。

⚠️ `hpush`（缺口 G2：基因树分布 = MSC 理论频率的推前）**仍是输入** ——
那是缺口 B1 的完整版（规格 §9 明确不在本批内），与 W13g 的口径一致。 -/
noncomputable def GeneTreeModel.ofSiteWeights {G : Type w} [MeasurableSpace G]
    (ν : Measure G) [IsProbabilityMeasure ν] (D : Topo → QuartetFreq X)
    (φ : G → (Fin 4 → ℝ) × ℝ) (hφ : Measurable φ) (m : MSCFreq.{u, v} X)
    (hpush : ∀ (S : Finset X) (hS : S.card = 4) (q : Split ↥S),
      ∫ g, (siteTable D φ g).p S hS q ∂ν = m.freq.p S hS q) :
    GeneTreeModel.{u, v, w} X where
  G := G
  ν := ν
  freqOf g := siteTable D φ g
  hmeas := measurable_siteTable D φ hφ
  m := m
  hpush := hpush

/-! ## 5. ★8④ 退化 ＋ 反空洞居民 -/

/-- ★★ **退化一致性（`ρ ≡ 1` 侧的代数形态）**：基准表族为**常值**时，
`convexCombo` **恒等于**该常值表 —— 即「位点层不产生任何变异」时新构造退回库内确定性形态。

证明只用系数是单位分解（`hc1`）＋ `Finset.sum_mul`。 -/
theorem convexCombo_const (D₀ : QuartetFreq X) (c : Topo → ℝ)
    (hc0 : ∀ T, 0 ≤ c T) (hc1 : ∑ T : Topo, c T = 1) :
    convexCombo (fun _ => D₀) c hc0 hc1 = D₀ := by
  refine (Phylo.Stat.GeneTreeSamplingAE.QuartetFreq.eq_iff_p
    (D := convexCombo (fun _ => D₀) c hc0 hc1) (D' := D₀)).mpr ?_
  funext S hS q
  show (∑ T : Topo, c T * D₀.p S hS q) = D₀.p S hS q
  rw [← Finset.sum_mul, hc1, one_mul]

/-- ★★ **位点权重表的退化形态**：`D` 常值时 `siteTable` 与 `g` 无关。 -/
theorem siteTable_const (D₀ : QuartetFreq X) {G : Type w} [MeasurableSpace G]
    (φ : G → (Fin 4 → ℝ) × ℝ) (g : G) :
    siteTable (fun _ => D₀) φ g = D₀ :=
  convexCombo_const D₀ (fun T => siteCoeff φ T g) (fun T => siteCoeff_nonneg φ T g)
    (siteCoeff_sum_one φ g)

/-- ★★★ **常值表下的 `meanFreq`**：若 `M.freqOf` 常值 `= D₀`（＝`ρ ≡ 1` 的退化），
则 `M.meanFreq = D₀`，**与 `ν` 的取法无关**。

⇒ 这就是「新结论没有写歪」的探针（★8④）：退化时 `meanFreq` 就是那张常值表。 -/
theorem meanFreq_of_const (M : GeneTreeModel.{u, v, w} X) (D₀ : QuartetFreq X)
    (h : ∀ g : M.G, M.freqOf g = D₀) : M.meanFreq = D₀ := by
  refine (Phylo.Stat.GeneTreeSamplingAE.QuartetFreq.eq_iff_p
    (D := M.meanFreq) (D' := D₀)).mpr ?_
  funext S hS q
  show (∫ g, (M.freqOf g).p S hS q ∂M.ν) = D₀.p S hS q
  rw [show (fun g : M.G => (M.freqOf g).p S hS q) = fun _ : M.G => D₀.p S hS q from
    funext fun g => by rw [h g]]
  rw [integral_const, Measure.real, measure_univ, ENNReal.toReal_one, one_smul]

/-- ★★ **常值基准表族下的 `hpush`**（把「积分常函数」这一步打包，供居民直接引用）：
若 `D₀.p S hS q = m.freq.p S hS q`，则常值表族的 `siteTable` 满足 `hpush`。 -/
theorem ofSiteWeights_const_hpush {G : Type w} [MeasurableSpace G]
    (ν : Measure G) [IsProbabilityMeasure ν] (D₀ : QuartetFreq X)
    (φ : G → (Fin 4 → ℝ) × ℝ) (m : MSCFreq.{u, v} X)
    (hpush : ∀ (S : Finset X) (hS : S.card = 4) (q : Split ↥S), D₀.p S hS q = m.freq.p S hS q) :
    ∀ (S : Finset X) (hS : S.card = 4) (q : Split ↥S),
      ∫ g, (siteTable (fun _ => D₀) φ g).p S hS q ∂ν = m.freq.p S hS q := by
  intro S hS q
  have hfun : (fun g : G => (siteTable (fun _ => D₀) φ g).p S hS q)
      = fun _ : G => m.freq.p S hS q := by
    funext g
    rw [siteTable_const, hpush S hS q]
  rw [hfun, integral_const, Measure.real, measure_univ, ENNReal.toReal_one, one_smul]

/-- ★★★ **显式居民（反空洞）**：取位点参数空间 `G = (Fin 4 → ℝ) × ℝ`、
`ν = Measure.dirac 0`、`φ = id`、基准表族**常值** `= witnessFreq`、真律 `= witnessMSC`。

* `hmeas` **由 `measurable_siteTable` 推出**（无该假设）；
* `freqOf ≡ witnessFreq = witnessMSC.freq` ⇒ `hpush` 由 `ofSiteWeights_const_hpush` 给出。

⇒ `GeneTreeModel.ofSiteWeights` **不是空构造**。⚠️ 本居民的 `D` 取常值 ⇒ 表与 `g` 无关
（这正是 §5 的退化形态）；要**非常值**居民还须额外核 `MSCFreq.majorizes`，
那与 `hmeas` 无关，故不在此展开（三张点质量表按 `1/3` 混合时两个 quartet 类会**并列**，
`majorizes` 的**严格**不等式失败 —— 见 W13g §5.1 的 ★D 记录）。 -/
noncomputable def siteWeightModel : GeneTreeModel.{0, 0, 0} (Fin 4) :=
  GeneTreeModel.ofSiteWeights (Measure.dirac (0 : (Fin 4 → ℝ) × ℝ))
    (fun _ => Phylo.Stat.GeneTreeSamplingAE.witnessFreq) id measurable_id
    Phylo.Stat.GeneTreeSamplingAE.witnessMSC
    (ofSiteWeights_const_hpush _ _ _ _
      (fun _ _ _ => rfl))

/-- ★★ **反空洞**：`hmeas`-free 的构造子**有居民**（`Fin 4` 上）。 -/
theorem geneTreeModel_ofSiteWeights_nonempty : Nonempty (GeneTreeModel.{0, 0, 0} (Fin 4)) :=
  ⟨siteWeightModel⟩

/-- ★★ 居民的 `freqOf` 取常值 `witnessFreq`。 -/
theorem siteWeightModel_freqOf (g : (Fin 4 → ℝ) × ℝ) :
    siteWeightModel.freqOf g = Phylo.Stat.GeneTreeSamplingAE.witnessFreq :=
  siteTable_const _ _ g

/-- ★★ **退化一致性（结论）**：居民的 `meanFreq` 就是 `witnessMSC.freq`
（`meanFreq_of_const`；与 W13g 的 `diracModel` 同族）。 -/
theorem siteWeightModel_meanFreq :
    siteWeightModel.meanFreq = Phylo.Stat.GeneTreeSamplingAE.witnessMSC.freq :=
  meanFreq_of_const _ _ siteWeightModel_freqOf

/-! ## 6. ★ `hmean`-free 变体：`MultiLocusLaw` 的基因树层版本

**口径（★D 结论：基因树层是这里的正确工具）**：`MultiLocusLaw` 的
`locus : Ω₀ → QuartetFreq X` 是「**每个基因座给出一张 quartet 频率表**」，
即「每棵基因树给出一张表」的逐基因座读法 ⇒ 它**就是** `GeneTreeModel.freqOf`
（`Ω₀ := M.G`、`ν := M.ν`）。于是：

* `MultiLocusLaw` 的 `hmean` ≡ `GeneTreeModel.hpush`（**推前**口径）；
* `MultiLocusLaw` 的 `hint` / `hindep` / `hident` **在本层是定理**：
  `M.sampleMeasure` 是**构造出来**的无穷乘积测度（W13g §1.4 的
  `integrable_eval` / `iIndepFun_eval` / `identDistrib_eval`）。

⇒ 下面的变体把**四条假设一起删掉**（★C：全是**新**声明，既有 4 个端点的字面**一字未动**）。 -/

/-- ★★ **桥**（`L ≥ 1` 时）：基因树层的经验表 `M.emp L ω` **就是**
多标记数据 `M.freqOf` 的平均表。

⇒ 于是 `MultiLocusLaw` 的整套「平均表」代数（`avg_p_sub_le` / `avg_FreqClose` /
`multiLocus_maximizer_agrees_close`）可以**直接**用在基因树层上。 -/
theorem emp_eq_avg (M : GeneTreeModel.{u, v, w} X) (L : ℕ) (hL : 0 < L) (ω : ℕ → M.G) :
    M.emp L ω = (multiLocusData M.freqOf L hL ω).avg := by
  refine (Phylo.Stat.GeneTreeSamplingAE.QuartetFreq.eq_iff_p
    (D := M.emp L ω) (D' := (multiLocusData M.freqOf L hL ω).avg)).mpr ?_
  funext S hS q
  have hLne : L ≠ 0 := Nat.pos_iff_ne_zero.mp hL
  rw [M.emp_p L ω S hS q, multiLocusData_avg_p]
  simp only [hLne, ↓reduceIte, div_eq_inv_mul]

/-- ★★★ **多标记平均表的 a.e. 收敛（基因树层，零 `hmean` / 零 iid 三件套）**：

与 `MultiLocusLaw.multiLocus_avg_eventually_close_ae` 结论**逐字同形**，
但假设面**只剩** `GeneTreeModel` 的字段（`ν` 是概率测度 ＋ `hpush`）。 -/
theorem multiLocus_avg_eventually_close_ae_of_geneTrees (M : GeneTreeModel.{u, v, w} X) :
    ∀ᵐ ω ∂M.sampleMeasure, ∀ ε : ℝ, 0 < ε → ∃ L₀ : ℕ, ∀ L ≥ L₀, ∀ hL : 0 < L,
      FreqClose (multiLocusData M.freqOf L hL ω).avg M.m.freq ε := by
  filter_upwards [M.emp_eventually_close_ae] with ω hω
  intro ε hε
  obtain ⟨N, hN⟩ := hω ε hε
  refine ⟨max N 1, fun L hL hLpos => ?_⟩
  rw [← emp_eq_avg M L hLpos ω]
  exact hN L (le_trans (le_max_left N 1) hL)

/-- ★★★ **多标记 ASTRAL 的 a.e. 统计一致性（quartet 层，基因树层版）**：

与 `MultiLocusLaw.multiLocus_statisticallyConsistent_ae` 结论**逐字同形**，
假设面里**没有** `hint` / `hindep` / `hident` / `hmean`。 -/
theorem multiLocus_statisticallyConsistent_ae_of_geneTrees (M : GeneTreeModel.{u, v, w} X)
    (hNE : ∃ q : QuartetChoice X, ¬ IsTrueChoice M.m q)
    {E : QuartetFreq X → QuartetTree.{u, v} X} (hE : ∀ D, IsASTRAL D (E D)) :
    ∀ᵐ ω ∂M.sampleMeasure, ∃ L₀ : ℕ, ∀ L ≥ L₀, ∀ hL : 0 < L,
      IsTrueChoice M.m (E (multiLocusData M.freqOf L hL ω).avg).q := by
  obtain ⟨δ, hδ, hgap⟩ := exists_gap M.m hNE
  have hfac : (0 : ℝ) < 2 * (Fintype.card {S : Finset X // S.card = 4} : ℝ) + 1 := by
    positivity
  have hεpos : 0 < δ / (2 * (Fintype.card {S : Finset X // S.card = 4} : ℝ) + 1) :=
    div_pos hδ hfac
  filter_upwards [multiLocus_avg_eventually_close_ae_of_geneTrees M] with ω hω
  obtain ⟨L₀, hL₀⟩ := hω _ hεpos
  refine ⟨L₀, fun L hL hLpos => ?_⟩
  exact multiLocus_maximizer_agrees_close M.m (multiLocusData M.freqOf L hLpos ω)
    hδ hgap ((multiLocus_isASTRAL (multiLocusData M.freqOf L hLpos ω)).mpr
      (hE (multiLocusData M.freqOf L hLpos ω).avg)) (hL₀ L hL hLpos)

/-- ★★★ **多标记 ASTRAL 的 a.e. 统计一致性（树层，基因树层版）**：
经库内 `QuartetDecidesTree` 升到树同构。零 `hmean`。 -/
theorem multiLocus_iso_ae_of_geneTrees (M : GeneTreeModel.{u, v, w} X)
    (hT : M.m.tree.IsBinary) (hNE : ∃ q : QuartetChoice X, ¬ IsTrueChoice M.m q)
    {E : QuartetFreq X → QuartetTree.{u, v} X} (hE : ∀ D, IsASTRAL D (E D))
    (hEbin : ∀ D, (E D).tree.IsBinary) :
    ∀ᵐ ω ∂M.sampleMeasure, ∃ L₀ : ℕ, ∀ L ≥ L₀, ∀ hL : 0 < L,
      Nonempty (Iso (E (multiLocusData M.freqOf L hL ω).avg).tree M.m.tree) := by
  filter_upwards [multiLocus_statisticallyConsistent_ae_of_geneTrees M hNE hE] with ω hω
  obtain ⟨L₀, hL₀⟩ := hω
  refine ⟨L₀, fun L hL hLpos => ?_⟩
  exact QuartetDecidesTree X (E (multiLocusData M.freqOf L hLpos ω).avg) M.m.toQuartetTree
    (hEbin _) hT (hL₀ L hL hLpos)

/-- ★★ **★8④ 退化一致性（多标记层）**：W13g 的 `diracModel m`（`ν` 为 Dirac、
`freqOf ≡ m.freq`）下，`L` 个基因座的平均表**恒等于** `m.freq`（对一切 `L ≥ 1`、一切 `ω`）
—— 即新变体的结论在退化情形**退回**库内 `MSCSampling.converges` 的确定性形态。 -/
theorem diracModel_multiLocus_avg_eq (m : MSCFreq.{u, v} X) (L : ℕ) (hL : 0 < L)
    (ω : ℕ → (Phylo.Stat.GeneTreeSamplingAE.diracModel m).G) :
    (multiLocusData (Phylo.Stat.GeneTreeSamplingAE.diracModel m).freqOf L hL ω).avg
      = m.freq := by
  rw [← emp_eq_avg (Phylo.Stat.GeneTreeSamplingAE.diracModel m) L hL ω]
  exact Phylo.Stat.GeneTreeSamplingAE.diracModel_emp_eq m L ω

/-- ★★ **变体的非空真（反空洞）**：把 §6 的 a.e. 变体**实例化**在 `diracModel m` 上，
假设面**一个不剩**（`hmean` / iid 三件套都没有）—— 故该变体不是空账目。 -/
theorem diracModel_multiLocus_avg_close_ae (m : MSCFreq.{u, v} X) :
    ∀ᵐ ω ∂(Phylo.Stat.GeneTreeSamplingAE.diracModel m).sampleMeasure, ∀ ε : ℝ, 0 < ε →
      ∃ L₀ : ℕ, ∀ L ≥ L₀, ∀ hL : 0 < L,
        FreqClose (multiLocusData (Phylo.Stat.GeneTreeSamplingAE.diracModel m).freqOf L hL ω).avg
          m.freq ε :=
  multiLocus_avg_eventually_close_ae_of_geneTrees _

/-! ## 7. ★D：`variance_empFreq_gap` **不**适用基因树层（**不**造变体）

`Phylo/Stat/EmpiricalConvergence.lean:379` 的

```text
variance_empFreq_gap （原文件中的 def ... : Prop；其陈述本文件一字未动，此处只复述形状）:
  (∀ x, ind x S hS q = 0 ∨ ind x S hS q = 1) →
  Integrable (fun ω => ind (ω 0) S hS q) μ →
  iIndepFun (fun i ω => ind (ω i) S hS q) μ →
  (∀ i, IdentDistrib …) →
  (∫ ω, ind (ω 0) S hS q ∂μ = m.freq.p S hS q) →        -- ← 第 5 个前提 = `hmean`
  ∀ n, 0 < n → ∫ ω, (empFreq ind n ω S hS q − m.freq.p S hS q)² ∂μ
                 = m.freq.p S hS q * (1 − m.freq.p S hS q) / n
```

（`ind : SiteFun X Ω₀` 是**该 `def` 所在文件的 `variable`**，故它在陈述里是显式参数。）

**结论：这里**不能**用基因树层工具，而且「删掉 `hmean` 的变体」是【假命题】。** 两条理由：

1. **层次不同**：`ind x S hS q` 是**单位点**的观测函数（点 `x` 是**位点结果**），
   `empFreq ind n ω` 是**位点**的经验频率；而 `GeneTreeModel.freqOf` 是**整棵基因树**
   给出的一张 quartet 频率表（`GeneTreeModel` 的 `emp` 是**基因树层**的经验表，
   它的下标 `k` 数的是**基因树**，不是位点）。把 `GeneTreeModel` 套到这里，等于要求
   「一棵基因树 ⇒ 一个位点」，那**不是**本库的模型（规格 §2.1/§3.4：位点层是 CASTER 侧的东西，
   且同树位点只**条件**独立）。
2. **命题为假（不是「难证」）**：取 `Ω₀ := Bool`、`μ := Measure.dirac false`、
   `ind ≡ 1`（常值指示）、`m.freq.p S hS q = 1/2`。则四个前提**全部成立**
   （`{0,1}` 取值；`dirac` 上可积；常值族独立、同分布；且 `empFreq ind n ≡ 1`），
   而结论要求 `∫ (1 − 1/2)² = (1/2)(1 − 1/2)/n`，即 `1/4 = 1/(4n)`（对一切 `n > 0`）
   —— 取 `n = 2` 即矛盾。⇒ **`hmean` 在此处不可省**（与 `MultiLocusLaw.empFreq_const_locus`
   同一机制，W12f 的 ★B 记录）。故本文件**不**给这一条造变体（★D：先判真假，再谈怎么证）。 -/

end Phylo.Stat.GeneTreeHmeasDischarge
