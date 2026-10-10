/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.Stat.MSCInstance
import Phylo.Stat.MSCProof
import Phylo.Stat.KingmanCoalescent

/-!
# `Phylo.Stat.MSCKingmanMeasure` —— `KingmanΘ` 上的**真 MSC 测度**（缺口 **G5″**）

## 1. 这条缺口是什么

`Phylo/Stat/MSCKingman.lean`（W9）已经给出 `MSCTopoSym KingmanΘ` 的**具体实例**
`kingmanMSCTopoSym`（字段 `deep` / `τd`）。但 `Phylo/Stat/MSCInstance.lean` 的端到端定理

    jc69_caster_statisticallyConsistent_kingman (ν : Measure KingmanΘ) [IsProbabilityMeasure ν]
        (hdeep : MeasurableSet {θ | kingmanMSCTopoSym.deep θ})
        (hpos  : 0 < ν {θ | ¬ kingmanMSCTopoSym.deep θ}) …

仍把 **`ν`（`KingmanΘ` 上的概率测度）** 与 **`hdeep` / `hpos`** 当**假设参数**
（`MSCKingman.lean` §5「诚实边界」把它留给 Phase 2）。**本文件构造出 `ν`**，
并证明 `hdeep` / `hpos` **是定理**（不再是参数）。

## 2. 构造（按 `e^{−a}` / `e^{−b}` 赋权）

真树 `((a,b),(c,d))` 的**根以下两段内枝长**记为 `a`、`b`（`t = a + b`）。

* **等待时间**：`{a,b}` 两条谱系在根以下未合并 ⟺ 其溯祖等待时间 `> a`；
  `{c,d}` 侧同。两段是**各自独立**的速率 `d₂ = 1` 的指数律
  （`Phylo/Stat/KingmanCoalescent.sojournLaw 2 = expMeasure 1`，K82 (1.7)）。
* **参数空间** `KingmanParam := ((Fin 4 → ℝ) × ℝ≥0 × ℝ≥0) × (ℝ × ℝ)`
  （叶长 × `(a,b)` × 两支的等待时间）；
* **前推** `toKingmanΘ : KingmanParam → KingmanΘ`：内枝长分量取 `a + b`，
  `Bool` 分量取「等待时间 **>** 该侧枝长」的**指示**；
* ★★★ **真测度** `kingmanMSCMeasure ρ := map toKingmanΘ (ρ ⊗ (sojournLaw 2 ⊗ sojournLaw 2))`
  —— `ρ` 是**物种树侧**（叶长 ＋ 两段内枝长）的任意概率测度
  （MSC 不指定枝长先验，故 `ρ` 是**参数**，不是本文件的缺口）。

## 3. 交付（全部零 `sorry` / 零 `axiom` / 零 `native_decide`）

| 条目 | 状态 |
|---|---|
| `ν = kingmanMSCMeasure ρ` 是**概率测度** | ✅ `isProbabilityMeasure_kingmanMSCMeasure` |
| **`hdeep` 是定理** | ✅ `measurableSet_kingmanMSCTopoSym_deep`（不依赖 `ν`） |
| **`ν (deep) = ∫⁻ e^{−a}·e^{−b} dρ`**（`e^{−a}`/`e^{−b}` **赋权**的准确内容） | ✅ `kingmanMSCMeasure_deep` |
| `ν (¬deep)` 的积分形式 | ✅ `kingmanMSCMeasure_notDeep` |
| **`hpos` 是定理**（`ρ` 在 `{a>0 或 b>0}` 上正质量时） | ✅ `kingmanMSCMeasure_notDeep_pos` |
| 确定物种树（`ρ = dirac`）时的闭式 `ν(deep) = e^{−a}e^{−b}` | ✅ `kingmanMSCMeasure_dirac_deep` |
| 确定物种树时 `ν(¬deep) = 1 − e^{−a}e^{−b}` | ✅ `kingmanMSCMeasure_dirac_notDeep` |
| **`hpos` 在确定物种树下是定理**（`a + b > 0`） | ✅ `kingmanMSCMeasure_dirac_notDeep_pos` |
| ★C 端到端：`1·P(¬deep) + ⅓·P(deep) = pConcordant (a+b)` | ✅ `kingmanMSCMeasure_dirac_concordant` |
| ★C 最小实例 `a = b = 0` ⇒ 一致概率 `= 1/3 = pConcordant 0` | ✅ `kingmanMSCMeasure_dirac_concordant_zero` |
| ★★★ 端到端定理（`hdeep`/`hpos` **已消掉**） | ✅ `jc69_caster_statisticallyConsistent_kingman_measure` |

**仍然是假设的**（与本缺口无关，属解析正则性 / 渐近层）：`hf_int` / `hf_pos`（幅度可积且正）、
`hint`（权重一致有界）、`hconv`（大数定律）—— 见 `Phylo/Stat/MSCInstance.lean` §3 的边界表。

## 4. 反例检查（★B）：「按 `e^{−a}`/`e^{−b}` 赋权，归一吗？两次抽样还是**一次**？」

1. **归一是的**：`ν(deep) + ν(¬deep) = 1` 由 `Measure` 的可加性给出（`ν` 是概率测度）；
   数值上 `e^{−a}e^{−b} + (1 − e^{−a}e^{−b}) = 1` ✓。
2. **⚠️ 必须**两段各抽**一次**指数（参数 `a`、`b` 分开），**不能**拿同一段时间 `t = a + b` 抽一次：
   后者给 `P(deep) = e^{−2t}`（`t = 1` 时 `≈ 0.1353`），而正确的值是
   `e^{−a}e^{−b} = e^{−(a+b)} = e^{−t} ≈ 0.3679`。**两者不等**
   （脚本 `scripts/msc/w11f_g5_check.py` 用精确有理数复刻了这个对照）。
   本文件的构造把 `(a, b)` 与两次独立抽样都在 `KingmanParam` 里**显式**记下，
   故不可能滑进这个陷阱。
3. **`0 ≤ a, b` 是必需的**（不是可以省的）：`sojournLaw_Ioi` 只在 `0 ≤ t` 上给出 `e^{−t}`；
   `t < 0` 时正确的概率是 `1`，而 `e^{−t} > 1`（`KingmanCoalescent.lean` §「方向与参数域的
   两条纪律」）。本文件因此把 `(a, b)` 直接放在 `ℝ≥0` 里，而非事后补假设。
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Phylo.Stat.MSCKingmanMeasure

open Phylo.Stat.MSCKingman
open Phylo.Stat.KingmanCoalescent (sojournLaw sojournLaw_Ioi sojournLaw_Iic
  isProbabilityMeasure_sojournLaw)

-- `haveI` 在本文件里是**必需的**：`Measure.prod_prod` / `measure_univ`
-- 都要从「因子是概率测度」这个**实例**里取。库内已有先例
-- （`KingmanCoalescent.lean:130`、`MSCMeasure.lean:53`）。
set_option linter.style.haveILetI false

/-! ## 1. 参数空间与前推 -/

/-- **物种树侧参数空间**：叶长 `Fin 4 → ℝ` × 根以下两段内枝长 `(a, b) : ℝ≥0 × ℝ≥0`
× 两支的溯祖等待时间 `ℝ × ℝ`。

⚠️ `(a, b)` 放在 `ℝ≥0` 里是**数学上必需的**（见文件头 §4.3）。 -/
abbrev KingmanParam : Type := ((Fin 4 → ℝ) × ℝ≥0 × ℝ≥0) × (ℝ × ℝ)

/-- **前推** `KingmanParam → KingmanΘ`：内枝长分量取 `a + b`（MSC 的总内枝长 `t`），
`Bool` 分量取「该侧溯祖等待时间 **>** 该侧枝长」（即「该侧在根以下**未能**合并」）。 -/
def toKingmanΘ (p : KingmanParam) : KingmanΘ :=
  ((p.1.1, (p.1.2.1 : ℝ) + (p.1.2.2 : ℝ)),
   (decide ((p.1.2.1 : ℝ) < p.2.1), decide ((p.1.2.2 : ℝ) < p.2.2)))

/-- `Bool` 指示 `(c, x) ↦ [c < x]` 可测（`Bool` 上逐点验证 `{true}` / `{false}` 的原像）。 -/
theorem measurable_decide_lt : Measurable (fun p : ℝ × ℝ => decide (p.1 < p.2)) := by
  refine measurable_to_countable' fun b => ?_
  cases b
  · rw [show (fun p : ℝ × ℝ => decide (p.1 < p.2)) ⁻¹' {false} = {p : ℝ × ℝ | p.2 ≤ p.1} from
      Set.ext fun p => by simp [decide_eq_false_iff_not, not_lt]]
    exact measurableSet_le measurable_snd measurable_fst
  · rw [show (fun p : ℝ × ℝ => decide (p.1 < p.2)) ⁻¹' {true} = {p : ℝ × ℝ | p.1 < p.2} from
      Set.ext fun p => by simp]
    exact measurableSet_lt measurable_fst measurable_snd

theorem measurable_toKingmanΘ : Measurable toKingmanΘ := by
  have h121 : Measurable fun p : KingmanParam => (p.1.2.1 : ℝ) :=
    measurable_subtype_coe.comp measurable_fst.snd.fst
  have h122 : Measurable fun p : KingmanParam => (p.1.2.2 : ℝ) :=
    measurable_subtype_coe.comp measurable_fst.snd.snd
  have h21 : Measurable fun p : KingmanParam => p.2.1 := measurable_snd.fst
  have h22 : Measurable fun p : KingmanParam => p.2.2 := measurable_snd.snd
  unfold toKingmanΘ
  refine Measurable.prodMk (Measurable.prodMk measurable_fst.fst ?_) (Measurable.prodMk ?_ ?_)
  · exact h121.add h122
  · exact measurable_decide_lt.comp (h121.prodMk h21)
  · exact measurable_decide_lt.comp (h122.prodMk h22)

/-! ## 2. ★★★ 真 MSC 测度 -/

/-- ★★★ **`KingmanΘ` 上的真 MSC 测度**：先按 `ρ` 抽物种树侧的 `(叶长, a, b)`，
在 `a`、`b` 上**各自**抽一个速率 `1` 的指数等待时间（`sojournLaw 2 = expMeasure 1`），
再前推到 `KingmanΘ`。

* `deep` 的概率（**给定的 `a`、`b`**）`= e^{−a} · e^{−b} = e^{−(a+b)}`（见 `kingmanMSCMeasure_deep`）；
* 与 `kingmanMSCTopoSym`（W9）拼起来就是**完整的 MSC 分布**：
  条件拓扑在 `deep` 上三拓扑各 `1/3`、在 `¬deep` 上点质量 `ab|cd`。 -/
def kingmanMSCMeasure (ρ : Measure ((Fin 4 → ℝ) × ℝ≥0 × ℝ≥0)) : Measure KingmanΘ :=
  Measure.map toKingmanΘ (ρ.prod ((sojournLaw 2).prod (sojournLaw 2)))

/-- **深合并事件**（`kingmanMSCTopoSym.deep` 的集合形式）。 -/
def DeepSet : Set KingmanΘ := {θ | kingmanMSCTopoSym.deep θ}

/-- **`deep` 可测** —— 它是两个 `Bool` 分量等于 `true` 的合取，**不依赖** `ν`。
⇒ `MSCInstance` 里的假设 `hdeep` 从此是**定理**。 -/
theorem measurableSet_kingmanMSCTopoSym_deep : MeasurableSet DeepSet := by
  show MeasurableSet ({θ : KingmanΘ | θ.2.1 = true} ∩ {θ : KingmanΘ | θ.2.2 = true})
  exact MeasurableSet.inter
    ((measurable_fst.comp measurable_snd) (measurableSet_singleton true))
    ((measurable_snd.comp measurable_snd) (measurableSet_singleton true))

/-- **`¬deep` 可测**（`hdeep` 的补集形式，供下游使用）。 -/
theorem measurableSet_notDeep : MeasurableSet DeepSetᶜ :=
  measurableSet_kingmanMSCTopoSym_deep.compl

/-- ★★★ **`ν` 是概率测度**（`ρ` 是概率测度时）。 -/
instance isProbabilityMeasure_kingmanMSCMeasure {ρ : Measure ((Fin 4 → ℝ) × ℝ≥0 × ℝ≥0)}
    [IsProbabilityMeasure ρ] : IsProbabilityMeasure (kingmanMSCMeasure ρ) := by
  haveI : IsProbabilityMeasure (sojournLaw 2) := isProbabilityMeasure_sojournLaw (by norm_num)
  exact (Measure.isProbabilityMeasure_map_iff measurable_toKingmanΘ.aemeasurable).mpr inferInstance

/-! ## 3. ★★★ `e^{−a}` / `e^{−b}` 赋权的准确内容 -/

/-- ★★★ **深合并的概率**：`ν(deep) = ∫⁻ e^{−a(u)} · e^{−b(u)} dρ`
—— 这就是「按 `e^{−a}` / `e^{−b}` 赋权」的**逐点**内容（两段**各自**的指数生存概率之积）。

证明：`Measure.map_apply`（前推）＋ `Measure.prod_apply`（Fubini）＋ `Measure.prod_prod`
＋ `sojournLaw_Ioi`（K82 (1.7) 的生存函数 `e^{−t}`）。 -/
theorem kingmanMSCMeasure_deep (ρ : Measure ((Fin 4 → ℝ) × ℝ≥0 × ℝ≥0)) :
    kingmanMSCMeasure ρ DeepSet
      = ∫⁻ u, ENNReal.ofReal (Real.exp (-(u.2.1 : ℝ))) * ENNReal.ofReal (Real.exp (-(u.2.2 : ℝ)))
          ∂ρ := by
  haveI : IsProbabilityMeasure (sojournLaw 2) := isProbabilityMeasure_sojournLaw (by norm_num)
  have hpre : ∀ u : (Fin 4 → ℝ) × ℝ≥0 × ℝ≥0,
      Prod.mk u ⁻¹' (toKingmanΘ ⁻¹' DeepSet)
        = Set.Ioi (u.2.1 : ℝ) ×ˢ Set.Ioi (u.2.2 : ℝ) := by
    intro u
    ext v
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_prod, Set.mem_Ioi, toKingmanΘ,
      DeepSet, kingmanMSCTopoSym, KingmanDeep, decide_eq_true_eq]
  rw [kingmanMSCMeasure, Measure.map_apply measurable_toKingmanΘ
      measurableSet_kingmanMSCTopoSym_deep,
    Measure.prod_apply (measurable_toKingmanΘ measurableSet_kingmanMSCTopoSym_deep)]
  refine lintegral_congr fun u => ?_
  rw [hpre u, Measure.prod_prod, sojournLaw_Ioi (show 2 ≤ 2 by norm_num) (u.2.1 : ℝ)
      (by positivity),
    sojournLaw_Ioi (show 2 ≤ 2 by norm_num) (u.2.2 : ℝ) (by positivity)]
  simp only [Coalescent.survival_two]

/-- **`ν(¬deep)` 的积分形式**：把「至少一侧在根以下完成合并」的指示函数积分。 -/
theorem kingmanMSCMeasure_notDeep (ρ : Measure ((Fin 4 → ℝ) × ℝ≥0 × ℝ≥0)) :
    kingmanMSCMeasure ρ DeepSetᶜ
      = ∫⁻ u, ((sojournLaw 2).prod (sojournLaw 2))
          {v : ℝ × ℝ | ¬ ((u.2.1 : ℝ) < v.1 ∧ (u.2.2 : ℝ) < v.2)} ∂ρ := by
  haveI : IsProbabilityMeasure (sojournLaw 2) := isProbabilityMeasure_sojournLaw (by norm_num)
  have hpre : ∀ u : (Fin 4 → ℝ) × ℝ≥0 × ℝ≥0,
      Prod.mk u ⁻¹' (toKingmanΘ ⁻¹' DeepSetᶜ)
        = {v : ℝ × ℝ | ¬ ((u.2.1 : ℝ) < v.1 ∧ (u.2.2 : ℝ) < v.2)} := by
    intro u
    ext v
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_compl_iff, toKingmanΘ,
      DeepSet, kingmanMSCTopoSym, KingmanDeep, decide_eq_true_eq]
  rw [kingmanMSCMeasure, Measure.map_apply measurable_toKingmanΘ measurableSet_notDeep,
    Measure.prod_apply (measurable_toKingmanΘ measurableSet_notDeep)]
  exact lintegral_congr fun u => by rw [hpre u]

/-- ★★★ **`hpos` 是定理**（一般 `ρ`）：只要物种树侧在「有正的内枝长」（`a > 0` 或 `b > 0`）
上有正质量，则 `ν(¬deep) > 0`。

证明：`ν(¬deep) = ∫⁻ g dρ`（`g ≥ 0`），其中 `g u ≠ 0` 当 `u` 有正的枝长
（此时 `{v | v.1 ≤ a}` 落在 `¬deep` 里，其 `γ`-测度是 `1 − e^{−a} > 0`）；
再用 `lintegral_pos_iff_support` ＋ `measure_mono`。 -/
theorem kingmanMSCMeasure_notDeep_pos (ρ : Measure ((Fin 4 → ℝ) × ℝ≥0 × ℝ≥0))
    (hρ : 0 < ρ {u : (Fin 4 → ℝ) × ℝ≥0 × ℝ≥0 | 0 < (u.2.1 : ℝ) ∨ 0 < (u.2.2 : ℝ)}) :
    0 < kingmanMSCMeasure ρ DeepSetᶜ := by
  haveI : IsProbabilityMeasure (sojournLaw 2) := isProbabilityMeasure_sojournLaw (by norm_num)
  rw [kingmanMSCMeasure_notDeep ρ]
  have hg : Measurable fun u : (Fin 4 → ℝ) × ℝ≥0 × ℝ≥0 =>
      ((sojournLaw 2).prod (sojournLaw 2))
        {v : ℝ × ℝ | ¬ ((u.2.1 : ℝ) < v.1 ∧ (u.2.2 : ℝ) < v.2)} := by
    have hbase : Measurable fun q : ℝ × ℝ =>
        ((sojournLaw 2).prod (sojournLaw 2))
          {v : ℝ × ℝ | ¬ (q.1 < v.1 ∧ q.2 < v.2)} := by
      have hb : MeasurableSet {p : (ℝ × ℝ) × (ℝ × ℝ) | ¬ (p.1.1 < p.2.1 ∧ p.1.2 < p.2.2)} :=
        (((measurableSet_lt (measurable_fst.comp measurable_fst)
            (measurable_fst.comp measurable_snd)).inter
          (measurableSet_lt (measurable_snd.comp measurable_fst)
            (measurable_snd.comp measurable_snd)))).compl
      have hk := measurable_measure_prodMk_left (ν := (sojournLaw 2).prod (sojournLaw 2)) hb
      rw [show (fun x : ℝ × ℝ => ((sojournLaw 2).prod (sojournLaw 2))
            (Prod.mk x ⁻¹' {p : (ℝ × ℝ) × (ℝ × ℝ) | ¬ (p.1.1 < p.2.1 ∧ p.1.2 < p.2.2)}))
          = (fun q : ℝ × ℝ => ((sojournLaw 2).prod (sojournLaw 2))
            {v : ℝ × ℝ | ¬ (q.1 < v.1 ∧ q.2 < v.2)}) from
        funext fun q => congrArg _ (by
          ext v
          simp only [Set.mem_preimage, Set.mem_ofPred_eq])] at hk
      exact hk
    have hcoe : Measurable fun u : (Fin 4 → ℝ) × ℝ≥0 × ℝ≥0 =>
        ((u.2.1 : ℝ), (u.2.2 : ℝ)) :=
      (measurable_subtype_coe.comp measurable_snd.fst).prodMk
        (measurable_subtype_coe.comp measurable_snd.snd)
    simpa only [Function.comp_def] using hbase.comp hcoe
  rw [lintegral_pos_iff_support hg]
  refine lt_of_lt_of_le hρ (measure_mono ?_)
  intro u hu
  rw [Function.mem_support]
  rcases hu with ha | hb
  · have hsub : Set.Iic (u.2.1 : ℝ) ×ˢ (Set.univ : Set ℝ)
        ⊆ {v : ℝ × ℝ | ¬ ((u.2.1 : ℝ) < v.1 ∧ (u.2.2 : ℝ) < v.2)} := by
      rintro ⟨y1, y2⟩ ⟨hy1, -⟩
      simp only [Set.mem_ofPred_eq, Set.mem_Iic] at hy1 ⊢
      exact fun h => absurd h.1 (not_lt.mpr hy1)
    have hpos : 0 < ((sojournLaw 2).prod (sojournLaw 2))
        (Set.Iic (u.2.1 : ℝ) ×ˢ (Set.univ : Set ℝ)) := by
      rw [Measure.prod_prod, measure_univ, mul_one,
        sojournLaw_Iic (show 2 ≤ 2 by norm_num) (u.2.1 : ℝ) ha.le]
      exact ENNReal.ofReal_pos.mpr (Coalescent.firstMergeCDF_pos (by norm_num) ha)
    exact ne_of_gt (lt_of_lt_of_le hpos (measure_mono hsub))
  · have hsub : (Set.univ : Set ℝ) ×ˢ Set.Iic (u.2.2 : ℝ)
        ⊆ {v : ℝ × ℝ | ¬ ((u.2.1 : ℝ) < v.1 ∧ (u.2.2 : ℝ) < v.2)} := by
      rintro ⟨y1, y2⟩ ⟨-, hy2⟩
      simp only [Set.mem_ofPred_eq, Set.mem_Iic] at hy2 ⊢
      exact fun h => absurd h.2 (not_lt.mpr hy2)
    have hpos : 0 < ((sojournLaw 2).prod (sojournLaw 2))
        ((Set.univ : Set ℝ) ×ˢ Set.Iic (u.2.2 : ℝ)) := by
      rw [Measure.prod_prod, measure_univ, one_mul,
        sojournLaw_Iic (show 2 ≤ 2 by norm_num) (u.2.2 : ℝ) hb.le]
      exact ENNReal.ofReal_pos.mpr (Coalescent.firstMergeCDF_pos (by norm_num) hb)
    exact ne_of_gt (lt_of_lt_of_le hpos (measure_mono hsub))

/-! ## 4. ★C 最小实例：**确定的物种树**（`ρ = dirac`），`Fin 4` 上端到端走完 -/

/-- ★★ **确定物种树下 `deep` 的原像就是两个半直线之积**（`a`、`b` 是常数）。 -/
theorem dirac_preimage_deep (leaf : Fin 4 → ℝ) (a b : ℝ≥0) :
    (toKingmanΘ ∘ Prod.mk (leaf, a, b)) ⁻¹' DeepSet
      = Set.Ioi (a : ℝ) ×ˢ Set.Ioi (b : ℝ) := by
  ext v
  simp only [Function.comp_apply, Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_prod,
    Set.mem_Ioi, toKingmanΘ, DeepSet, kingmanMSCTopoSym, KingmanDeep, decide_eq_true_eq]

/-- ★★★ **确定物种树下的闭式**：`ν(deep) = e^{−a} · e^{−b}`。 -/
theorem kingmanMSCMeasure_dirac_deep (leaf : Fin 4 → ℝ) (a b : ℝ≥0) :
    kingmanMSCMeasure (Measure.dirac (leaf, a, b)) DeepSet
      = ENNReal.ofReal (Real.exp (-(a : ℝ))) * ENNReal.ofReal (Real.exp (-(b : ℝ))) := by
  haveI : IsProbabilityMeasure (sojournLaw 2) := isProbabilityMeasure_sojournLaw (by norm_num)
  have h1 : kingmanMSCMeasure (Measure.dirac (leaf, a, b))
      = Measure.map (toKingmanΘ ∘ Prod.mk (leaf, a, b))
          ((sojournLaw 2).prod (sojournLaw 2)) := by
    rw [kingmanMSCMeasure, Measure.dirac_prod]
    exact Measure.map_map measurable_toKingmanΘ (measurable_const.prodMk measurable_id)
  rw [h1,
    Measure.map_apply (f := toKingmanΘ ∘ Prod.mk (leaf, a, b))
      (measurable_toKingmanΘ.comp (measurable_const.prodMk measurable_id))
      measurableSet_kingmanMSCTopoSym_deep,
    dirac_preimage_deep, Measure.prod_prod,
    sojournLaw_Ioi (show 2 ≤ 2 by norm_num) (a : ℝ) (by positivity),
    sojournLaw_Ioi (show 2 ≤ 2 by norm_num) (b : ℝ) (by positivity)]
  simp only [Coalescent.survival_two]

/-- ★★★ **确定物种树下的闭式（补）**：`ν(¬deep) = 1 − e^{−a} · e^{−b}`
（由 `prob_compl_eq_one_sub`：`ν` 是概率测度）。 -/
theorem kingmanMSCMeasure_dirac_notDeep (leaf : Fin 4 → ℝ) (a b : ℝ≥0) :
    kingmanMSCMeasure (Measure.dirac (leaf, a, b)) DeepSetᶜ
      = 1 - ENNReal.ofReal (Real.exp (-(a : ℝ))) * ENNReal.ofReal (Real.exp (-(b : ℝ))) := by
  haveI : IsProbabilityMeasure (kingmanMSCMeasure (Measure.dirac (leaf, a, b))) := inferInstance
  rw [prob_compl_eq_one_sub measurableSet_kingmanMSCTopoSym_deep, kingmanMSCMeasure_dirac_deep]

/-- ★★★ **`hpos` 在确定物种树下是定理**：`a + b > 0` ⇒ `ν(¬deep) > 0`。

（本定理**真正把 `MSCInstance` 的假设 `hpos` 消掉**：在确定物种树的情形下，
`hpos` 不再是参数，而是 `a + b > 0` 的推论。） -/
theorem kingmanMSCMeasure_dirac_notDeep_pos (leaf : Fin 4 → ℝ) (a b : ℝ≥0)
    (hab : 0 < (a : ℝ) + (b : ℝ)) :
    0 < kingmanMSCMeasure (Measure.dirac (leaf, a, b)) DeepSetᶜ := by
  refine kingmanMSCMeasure_notDeep_pos (Measure.dirac (leaf, a, b)) ?_
  have hset : MeasurableSet {u : (Fin 4 → ℝ) × ℝ≥0 × ℝ≥0 |
      0 < (u.2.1 : ℝ) ∨ 0 < (u.2.2 : ℝ)} :=
    (measurableSet_lt measurable_const (measurable_subtype_coe.comp measurable_snd.fst)).union
      (measurableSet_lt measurable_const (measurable_subtype_coe.comp measurable_snd.snd))
  rw [Measure.dirac_apply' (leaf, a, b) hset]
  have hmem : (leaf, a, b) ∈ {u : (Fin 4 → ℝ) × ℝ≥0 × ℝ≥0 |
      0 < (u.2.1 : ℝ) ∨ 0 < (u.2.2 : ℝ)} := by
    by_cases ha : (0 : ℝ) < (a : ℝ)
    · exact Or.inl ha
    · exact Or.inr (by have h := not_lt.mp ha; linarith)
  rw [Set.indicator_of_mem hmem]
  exact zero_lt_one

/-- ★★ **两段指数之积 = `e^{−(a+b)}`**（半群性；与 `MSCKingman.kingmanDeepProb_eq`
是同一个数）。 -/
theorem exp_neg_mul_exp_neg (a b : ℝ) :
    Real.exp (-a) * Real.exp (-b) = Real.exp (-(a + b)) := by
  rw [← Real.exp_add]
  ring_nf

/-- ★★★ **★C 端到端（`{ab|cd}` 的权重 = `1 − ⅔e^{−t}` 型）**：

`P(一致) = ν(¬deep) · 1 + ν(deep) · ⅓ = (1 − e^{−a}e^{−b}) + ⅓ e^{−a}e^{−b}
         = 1 − ⅔ e^{−(a+b)} = Coalescent.pConcordant (a + b)`。

左边用的是**本文件构造的测度** `kingmanMSCMeasure (dirac …)`，
右边是库内既有的解析闭式 —— 两边**在测度层对上**（不是把 `pConcordant` 展开一遍）。 -/
theorem kingmanMSCMeasure_dirac_concordant (leaf : Fin 4 → ℝ) (a b : ℝ≥0) :
    (kingmanMSCMeasure (Measure.dirac (leaf, a, b)) DeepSetᶜ).toReal * 1
      + (kingmanMSCMeasure (Measure.dirac (leaf, a, b)) DeepSet).toReal * (1 / 3)
      = Coalescent.pConcordant ((a : ℝ) + (b : ℝ)) := by
  haveI : IsProbabilityMeasure (kingmanMSCMeasure (Measure.dirac (leaf, a, b))) := inferInstance
  have hle1 : kingmanMSCMeasure (Measure.dirac (leaf, a, b)) DeepSet ≤ 1 := by
    rw [← measure_univ (μ := kingmanMSCMeasure (Measure.dirac (leaf, a, b)))]
    exact measure_mono (Set.subset_univ _)
  have htr_not : (kingmanMSCMeasure (Measure.dirac (leaf, a, b)) DeepSetᶜ).toReal
      = 1 - (kingmanMSCMeasure (Measure.dirac (leaf, a, b)) DeepSet).toReal := by
    rw [prob_compl_eq_one_sub measurableSet_kingmanMSCTopoSym_deep,
      ENNReal.toReal_sub_of_le hle1 ENNReal.one_ne_top, ENNReal.toReal_one]
  have htr_deep : (kingmanMSCMeasure (Measure.dirac (leaf, a, b)) DeepSet).toReal
      = Real.exp (-(a : ℝ)) * Real.exp (-(b : ℝ)) := by
    rw [kingmanMSCMeasure_dirac_deep, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (Real.exp_pos _).le, ENNReal.toReal_ofReal (Real.exp_pos _).le]
  rw [htr_not, htr_deep, mul_one, ← kingman_concordant_eq_pConcordant (a : ℝ) (b : ℝ),
    kingmanNotDeepProb, kingmanDeepProb, exp_neg_mul_exp_neg]
  ring

/-- ★C **最小实例 `t = 0`**（`a = b = 0`）：此时 `deep` 几乎必然（两个指数等待时间 `> 0` a.s.），
一致概率 `= ⅓ = pConcordant 0`。 -/
theorem kingmanMSCMeasure_dirac_concordant_zero (leaf : Fin 4 → ℝ) :
    (kingmanMSCMeasure (Measure.dirac (leaf, (0 : ℝ≥0), (0 : ℝ≥0))) DeepSetᶜ).toReal * 1
      + (kingmanMSCMeasure (Measure.dirac (leaf, (0 : ℝ≥0), (0 : ℝ≥0))) DeepSet).toReal
          * (1 / 3)
      = 1 / 3 := by
  rw [kingmanMSCMeasure_dirac_concordant, Coalescent.pConcordant_eq]
  simp only [NNReal.coe_zero, add_zero, neg_zero, Real.exp_zero, mul_one]
  norm_num

/-! ## 5. ★★★ 端到端：`MSCInstance` 的假设 `hdeep` / `hpos` **被消掉** -/

/-- ★★★ **JC69 的 CASTER 定理 1 —— `hdeep` / `hpos` 不再是假设**：

与 `Phylo.Stat.MSCInstance.jc69_caster_statisticallyConsistent_kingman` **逐字同形**，
只是把参数 `ν` **实例化**成 ★★★ `kingmanMSCMeasure (Measure.dirac (leaf, a, b))`，
并把 `hdeep` / `hpos` 两个假设**换成**本文件的两条**定理**
（`measurableSet_kingmanMSCTopoSym_deep` / `kingmanMSCMeasure_dirac_notDeep_pos`）。

⇒ 剩下的是 `hf_int` / `hf_pos` / `hint`（幅度可积且正、权重一致有界）与 `hconv`
（大数定律）—— 它们**本来就与 G5″ 无关**（属解析正则性 / 渐近层）。 -/
theorem jc69_caster_statisticallyConsistent_kingman_measure
    (leaf : Fin 4 → ℝ) (a b : ℝ≥0) (hab : 0 < (a : ℝ) + (b : ℝ))
    (hf_int : Integrable Phylo.Stat.MSCInstance.jc69PropADataK.f
      (kingmanMSCMeasure (Measure.dirac (leaf, a, b))))
    (hf_pos : ∀ θ : KingmanΘ, ¬ kingmanMSCTopoSym.deep θ →
      0 < Phylo.Stat.MSCInstance.jc69PropADataK.f θ)
    (hint : ∀ T : Phylo.Stat.CASTERWeights.Topo, Integrable
      (fun θ => ∑ T' : Phylo.Stat.CASTERWeights.Topo,
        kingmanMSCTopoSym.τd θ T' * Phylo.Stat.MSCInstance.jc69PropADataK.A θ T' T)
      (kingmanMSCMeasure (Measure.dirac (leaf, a, b))))
    (emp : ℕ → Phylo.Stat.CASTERTopo.TopoWeight (Fin 4))
    (hconv : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N,
      Phylo.Stat.CASTERTopo.TopoClose (emp n)
        (Phylo.Stat.CASTERTopo.TopoIdeal.ofModel kingmanMSCTopoSym
          (kingmanMSCMeasure (Measure.dirac (leaf, a, b)))
          measurableSet_kingmanMSCTopoSym_deep Phylo.Stat.MSCInstance.jc69PropADataK
          hf_int hf_pos (kingmanMSCMeasure_dirac_notDeep_pos leaf a b hab) hint).W ε)
    {E : ℕ → Phylo.Stat.CASTERTopo.TopoChoice (Fin 4)}
    (hE : ∀ (n : ℕ) (q : Phylo.Stat.CASTERTopo.TopoChoice (Fin 4)),
      Phylo.Stat.CASTERTopo.topoScore (emp n) q ≤ Phylo.Stat.CASTERTopo.topoScore (emp n) (E n)) :
    ∃ N : ℕ, ∀ n ≥ N,
      Phylo.Stat.CASTERTopo.IsTrueT (fun _ _ => Phylo.Stat.CASTERWeights.Topo.ab_cd) (E n) :=
  Phylo.Stat.MSCInstance.jc69_caster_statisticallyConsistent_kingman
    (kingmanMSCMeasure (Measure.dirac (leaf, a, b)))
    measurableSet_kingmanMSCTopoSym_deep
    (kingmanMSCMeasure_dirac_notDeep_pos leaf a b hab)
    hf_int hf_pos hint emp hconv hE

end Phylo.Stat.MSCKingmanMeasure

end
