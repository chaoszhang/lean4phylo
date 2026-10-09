/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.Stat.MSCProof
import Phylo.Stat.KingmanCoalescent
import Phylo.Stat.RootJumpMass

/-!
# `Phylo.Stat.MSCMeasure` —— 把 M1 的 quartet 公式从**实数层**升到**测度层**

`Phylo/Stat/MSCProof.lean` 里的一致概率 `mscConcordant t` 原先写作
`Coalescent.firstMergeCDF 2 t + Coalescent.survival 2 t · rootTopoProb`
—— 这两项都是**实数层的闭式**（`1 − e^{−t}` 与 `e^{−t}`）。
本文件用 W10b（`Phylo/Stat/KingmanCoalescent.lean`）的**测度层**逗留时间律
`sojournLaw 2 = expMeasure 1` 把它们**换成真正的概率**：

* ★★★ `mscConcordant_eq_measure`：`mscConcordant t = P(τ₂ ≤ t)·1 + P(τ₂ > t)·rootTopoProb`，
  其中两个 `P` 都是 `sojournLaw 2` 在**可测集**上的测度；
* ★★★ `mscDiscordant_eq_measure`：`mscDiscordant t = P(τ₂ > t)·rootTopoProb`；
* ★★★ `branch_partition`：`P(τ₂ ≤ t) + P(τ₂ > t) = 1`（**要么在枝内合并、要么不** —— 真·概率划分）；
* ★★★ `topology_probs_sum`：三个拓扑的概率（测度层）之和 `= 1`；
* ★★ `pConcordant_eq_measure`：库内既有的解析闭式 `Coalescent.pConcordant t`
  **就是**这个测度层混合；
* ★★★ **`mscConcordant_eq_measure_jump` / `pConcordant_eq_measure_jump`**：
  再用 `Phylo/Stat/RootJumpMass.lean` 的 ★★★ `rootTopoProb_eq_jumpMass` **把根部的 `1/3` 也换成
  跳链（W10a，(2.2)）在 3 块层上的质量** ⇒ M1 写成了**完全测度层**形式：
  **内枝**用 `expMeasure`（W10b），**根部**用跳链律（W10a），**没有任何实数层的 `1/3` 残留**。

⇒ 于是 M1（4 元集 ILS 公式）不再是「实数层算术」，而是**由 `expMeasure` 与跳链律给出的真概率**。

## 诚实边界（逐条）

| 条目 | 状态 |
|---|---|
| 内部枝的指数项 `1 − e^{−t}` / `e^{−t}` | ✅ **本文件**：换成 `sojournLaw 2 (Iic t)` / `(Ioi t)` 的测度 |
| 根种群的 `1/3`（`rootTopoProb`） | ✅ **本文件**（`*_eq_measure_jump`）：换成 **W10a 跳链在 3 块层上的质量**（`RootJumpMass.rootTopoProb_eq_jumpMass`） |
| 整条跳链的**轨迹律** | ⚠️ 见 `KingmanLaw.lean` 的边界表：需要「一次合并的去向恰有 `C(k+1,2)` 个」这一计数（自造双射，未做） |
| 一般 `n` 的基因树分布 | ❌ 未做（属 W10e 的缺口） |
-/

noncomputable section

open Classical MeasureTheory
open scoped ENNReal NNReal

namespace Phylo.Stat.MSCMeasure

-- `sojournLaw 2` 的概率性要从「是指数测度」的实例取；`haveI` 对 `Prop` 会触发
-- `linter.style.haveILetI`（告警会破坏「`lake env lean` 输出 0 字节」判据）。
-- 库内已有先例（`PhylogramContract.lean`、`SplitsDetermineTree.lean`、本批 `KingmanLaw.lean`）。
set_option linter.style.haveILetI false

/-- 拓扑类（`01|23` 型）在 **3 块划分**上的集合：`{P : |P| = 3 | {0,1} 或 {2,3} 是 `P` 的块}`。
（与 `RootJumpMass` 里用的内联 filter 逐字一致。） -/
abbrev TopoClass3 : Finset (Phylo.Stat.KingmanJumpChain.PartK 4 3) :=
  Finset.univ.filter fun P : Phylo.Stat.KingmanJumpChain.PartK 4 3 =>
    ({0, 1} : Finset (Fin 4)) ∈ P.1.parts ∨ ({2, 3} : Finset (Fin 4)) ∈ P.1.parts

open Phylo.Stat.MSCProof
open Phylo.Stat.KingmanCoalescent (sojournLaw sojournLaw_Ioi sojournLaw_Iic
  isProbabilityMeasure_sojournLaw)

/-- ★★★ **内部枝上的概率划分**：`P(τ₂ ≤ t) + P(τ₂ > t) = 1`
—— 两条谱系**要么在枝内合并、要么不**；两项都是 `sojournLaw 2`（= `expMeasure 1`）在可测集上的测度。 -/
theorem branch_partition (t : ℝ) :
    (sojournLaw 2 (Set.Iic t)).toReal + (sojournLaw 2 (Set.Ioi t)).toReal = 1 := by
  haveI : IsProbabilityMeasure (sojournLaw 2) := isProbabilityMeasure_sojournLaw (by norm_num)
  have hsum : sojournLaw 2 (Set.Iic t) + sojournLaw 2 (Set.Ioi t) = 1 := by
    rw [← measure_union (Set.Iic_disjoint_Ioi le_rfl) measurableSet_Ioi, Set.Iic_union_Ioi]
    exact measure_univ
  have hle : ∀ s : Set ℝ, sojournLaw 2 s ≤ 1 := by
    intro s
    rw [← measure_univ (μ := sojournLaw 2)]
    exact measure_mono (Set.subset_univ s)
  calc (sojournLaw 2 (Set.Iic t)).toReal + (sojournLaw 2 (Set.Ioi t)).toReal
      = (sojournLaw 2 (Set.Iic t) + sojournLaw 2 (Set.Ioi t)).toReal :=
        (ENNReal.toReal_add (ne_top_of_le_ne_top ENNReal.one_ne_top (hle _))
          (ne_top_of_le_ne_top ENNReal.one_ne_top (hle _))).symm
    _ = (1 : ℝ≥0∞).toReal := by rw [hsum]
    _ = 1 := ENNReal.toReal_one

/-- ★★★ **M1 的测度层形式**：一致概率 = `P(在枝内合并)·1 + P(未合并)·rootTopoProb`，
两个 `P` 都是 `sojournLaw 2` 的测度（不再只是闭式 `1 − e^{−t}` / `e^{−t}`）。 -/
theorem mscConcordant_eq_measure {t : ℝ} (ht : 0 ≤ t) :
    mscConcordant t
      = (sojournLaw 2 (Set.Iic t)).toReal * 1
        + (sojournLaw 2 (Set.Ioi t)).toReal * rootTopoProb := by
  rw [sojournLaw_Iic (show 2 ≤ 2 by norm_num) t ht,
    sojournLaw_Ioi (show 2 ≤ 2 by norm_num) t ht,
    ENNReal.toReal_ofReal (Coalescent.firstMergeCDF_nonneg 2 ht),
    ENNReal.toReal_ofReal (Coalescent.survival_pos 2 t).le, mul_one]
  rfl

/-- ★★★ **每个不一致拓扑的概率（测度层）**：`P(未在枝内合并) · rootTopoProb`。 -/
theorem mscDiscordant_eq_measure {t : ℝ} (ht : 0 ≤ t) :
    mscDiscordant t = (sojournLaw 2 (Set.Ioi t)).toReal * rootTopoProb := by
  rw [sojournLaw_Ioi (show 2 ≤ 2 by norm_num) t ht,
    ENNReal.toReal_ofReal (Coalescent.survival_pos 2 t).le]
  rfl

/-- ★★★ **三个拓扑的概率（测度层）之和 = 1**。 -/
theorem topology_probs_sum {t : ℝ} (ht : 0 ≤ t) :
    (sojournLaw 2 (Set.Iic t)).toReal * 1
        + (sojournLaw 2 (Set.Ioi t)).toReal * rootTopoProb
        + 2 * ((sojournLaw 2 (Set.Ioi t)).toReal * rootTopoProb) = 1 := by
  rw [show (sojournLaw 2 (Set.Iic t)).toReal * 1
        + (sojournLaw 2 (Set.Ioi t)).toReal * rootTopoProb = mscConcordant t
      from (mscConcordant_eq_measure ht).symm,
    show (sojournLaw 2 (Set.Ioi t)).toReal * rootTopoProb = mscDiscordant t
      from (mscDiscordant_eq_measure ht).symm]
  exact mscConcordant_add_two t

/-- ★★★ **库内既有的解析闭式 `Coalescent.pConcordant t` 就是上面的测度层混合**
（`= 1 − ⅔e^{−t}` 只是它的闭形式）。 -/
theorem pConcordant_eq_measure {t : ℝ} (ht : 0 ≤ t) :
    Coalescent.pConcordant t
      = (sojournLaw 2 (Set.Iic t)).toReal * 1
        + (sojournLaw 2 (Set.Ioi t)).toReal * rootTopoProb := by
  rw [← mscConcordant_eq_measure ht, mscConcordant_eq]

/-- ★★★ **M1 的完全测度层形式**（本文件的**收口**）：

`p(t) = P(τ₂ ≤ t)·1 + P(τ₂ > t)·(跳链在拓扑类上的质量)` ——
**内枝**用 `sojournLaw 2 = expMeasure 1`（W10b），**根部**用跳链在 3 块层上的质量
（W10a，经 `RootJumpMass.rootTopoProb_eq_jumpMass`）⇒ **没有任何实数层的 `1/3` 残留**。 -/
theorem mscConcordant_eq_measure_jump {t : ℝ} (ht : 0 ≤ t) :
    mscConcordant t
      = (sojournLaw 2 (Set.Iic t)).toReal * 1
        + (sojournLaw 2 (Set.Ioi t)).toReal
          * (∑ P ∈ TopoClass3, Phylo.Stat.KingmanJumpChain.jumpWeight 4 3 P) := by
  rw [mscConcordant_eq_measure ht, ← Phylo.Stat.RootJumpMass.rootTopoProb_eq_jumpMass]

/-- ★★★ 同上，但用库内既有的解析闭式 `Coalescent.pConcordant t` 表述。 -/
theorem pConcordant_eq_measure_jump {t : ℝ} (ht : 0 ≤ t) :
    Coalescent.pConcordant t
      = (sojournLaw 2 (Set.Iic t)).toReal * 1
        + (sojournLaw 2 (Set.Ioi t)).toReal
          * (∑ P ∈ TopoClass3, Phylo.Stat.KingmanJumpChain.jumpWeight 4 3 P) := by
  rw [← mscConcordant_eq_measure_jump ht, mscConcordant_eq]

/-- ★★ 测度层的不一致概率**恒正**（`τ₂ > t` 的概率恒正）。 -/
theorem mscDiscordant_eq_measure_pos {t : ℝ} (ht : 0 ≤ t) :
    0 < (sojournLaw 2 (Set.Ioi t)).toReal := by
  rw [sojournLaw_Ioi (show 2 ≤ 2 by norm_num) t ht,
    ENNReal.toReal_ofReal (Coalescent.survival_pos 2 t).le]
  exact Coalescent.survival_pos 2 t

end Phylo.Stat.MSCMeasure
