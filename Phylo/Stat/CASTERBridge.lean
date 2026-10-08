/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.Stat.CASTERTheorem1
import Phylo.Stat.CASTEREngine

/-!
# `Phylo.Stat.CASTERBridge` —— 从**命题 A（基因树层）**到**命题 B（物种树层）**

文献：Zhang, Nielsen, Mirarab (2025), *Science* **387**(6737) eadk9688，
**Supplementary** `sm.tex` 的 `prop:consistency_genetree` ⇒ `prop:consistency_speciestree`（1308–1440）。

## 这一环做什么

`Phylo.Stat.CASTEREngine` 已经证了「命题 A ⇒ 命题 B」的**抽象**版本，但它是对
`MSCTopoSym`（时间层的拓扑分布）说的；而 `Phylo.Stat.CASTERTheorem1` 需要的
`CASTERIdeal` 是对**期望权重表**说的。本文件把两者接起来：

* **`PropAData`** —— 在「时间 `θ` × 基因树拓扑 `T'`」上给出命题 A 数据
  （`A θ T' r` = 该基因树上拓扑 `r` 的位点权重期望，幅度 `f θ`）；
* **`expWeight`** —— 拓扑 `r` 的**期望权重**：先按 `ν` 抽时间、再按 `τd θ` 抽基因树拓扑；
* ★★★ **`expWeight_strict`** —— 真拓扑 `ab|cd` 的期望权重**严格大于两个错拓扑**
  （这正是 `CASTERIdeal.propB` 的内容，逐 quartet 说）。

## 为什么要两个不同的「符号函数」

引擎的 `sign = (+1,-1,0)` 只给出 `E[w(ab|cd)] > E[w(ac|bd)]` 这一条。
命题 B 要对**两个**错拓扑各给一条，所以还需要 `sgn2 = (+1,0,-1)`
（`E[w(ab|cd)] > E[w(ad|bc)]`）。引擎的 ★★★ `MSCTopoSym.cancel_of` /
`propB_of` 正是为此做的一般化：只要 `∑ T, sgn T = 0` 且 `sgn .ab_cd = 1` 就成立。

⚠️ 对应关系：`delta` 用 `sign`（`ab|cd` 支取 `+1`、`ac|bd` 支取 `-1`、`ad|bc` 支取 `0`），
`delta_ad` 用 `sgn2`（`ab|cd ↦ +1`、`ac|bd ↦ 0`、`ad|bc ↦ -1`）。两者都由
`PropA` 的三条子句直接推出（见各自的证明）。

## 🔻 诚实边界

* 本文件在**单个 quartet**（四叶物种树）上完成桥接，这正是附录的做法；
  多物种的「逐 quartet 求和」由 `Phylo.Stat.CASTERTheorem1` 的得分可加性承担
  （附录原文："can be then extended to species trees with more than four species by
  summing over the species tree restricted to all quartets of species"）。
* 可积性假设 `hint_*` 对应正文定理 1 的**条件 (2)「权重一致有界」**
  （有界 ⟹ 可积），本文件把它显式写出，没有藏起来。 -/

noncomputable section

namespace Phylo.Stat.CASTERBridge

open Phylo.Stat.CASTEREngine
open Phylo.Stat.CASTERWeights
open MeasureTheory

variable {Θ : Type*}

/-! ## 1. 命题 A 数据与两个符号函数 -/

/-- **`sgn2 = (+1, 0, -1)`**：与 `sign` 配对使用，用来拿 `E[w(ab|cd)] > E[w(ad|bc)]`。 -/
def sgn2 : Topo → ℝ
  | .ab_cd => 1
  | .ac_bd => 0
  | .ad_bc => -1

@[simp] theorem sgn2_ab_cd : sgn2 .ab_cd = 1 := rfl
@[simp] theorem sgn2_ac_bd : sgn2 .ac_bd = 0 := rfl
@[simp] theorem sgn2_ad_bc : sgn2 .ad_bc = -1 := rfl

/-- `∑ T, sgn2 T = 0`（抵消引理的前提之一）。 -/
theorem sum_sgn2 : ∑ T : Topo, sgn2 T = 0 := by
  rw [sum_topo]; simp [sgn2]

/-- **命题 A 数据**（在「时间 × 基因树拓扑」上）。

`A θ T' r` = 在时间为 `θ`、基因树拓扑为 `T'` 的基因树上，拓扑 `r` 的位点权重期望；
`f θ` = 幅度。三条子句与 `PropA` 逐字相同（基因树**自己的**拓扑那一支减 `f` 等于另两支）。 -/
structure PropAData (Θ : Type*) where
  /-- 三个拓扑的期望权重（还依赖基因树拓扑）。 -/
  A : Θ → Topo → Topo → ℝ
  /-- 幅度 `f θ`。 -/
  f : Θ → ℝ
  /-- 基因树拓扑为 `ab|cd` 时的子句。 -/
  clause_ab : ∀ θ T', T' = .ab_cd →
    A θ T' .ab_cd - f θ = A θ T' .ac_bd ∧ A θ T' .ab_cd - f θ = A θ T' .ad_bc
  /-- 基因树拓扑为 `ac|bd` 时的子句。 -/
  clause_ac : ∀ θ T', T' = .ac_bd →
    A θ T' .ac_bd - f θ = A θ T' .ab_cd ∧ A θ T' .ac_bd - f θ = A θ T' .ad_bc
  /-- 基因树拓扑为 `ad|bc` 时的子句。 -/
  clause_ad : ∀ θ T', T' = .ad_bc →
    A θ T' .ad_bc - f θ = A θ T' .ab_cd ∧ A θ T' .ad_bc - f θ = A θ T' .ac_bd

namespace PropAData

variable (P : PropAData Θ)

/-- **打包成引擎的 `PropA`**：样本空间取 `Θ × Topo`（时间 × 基因树拓扑）。 -/
def toPropA : PropA (Θ × Topo) where
  A := fun p r => P.A p.1 p.2 r
  f := fun p => P.f p.1
  τ := fun p => p.2
  clause_ab := fun p h => P.clause_ab p.1 p.2 h
  clause_ac := fun p h => P.clause_ac p.1 p.2 h
  clause_ad := fun p h => P.clause_ad p.1 p.2 h

/-- ★★ **`ab|cd` 与 `ac|bd` 的期望权重差 = `sign (基因树拓扑) · f`**
（引擎 ★★★ `PropA.delta` 的重述）。 -/
theorem delta (θ : Θ) (T' : Topo) :
    P.A θ T' .ab_cd - P.A θ T' .ac_bd = sign T' * P.f θ :=
  P.toPropA.delta (θ, T')

/-- ★★ **`ab|cd` 与 `ad|bc` 的期望权重差 = `sgn2 (基因树拓扑) · f`**。

（三条子句在这一支上给出 `+f`：基因树拓扑 `ab|cd` 与 `ad|bc` 各给一条
「自己的减 `f` 等于另一个」，两者相减即得；`ac|bd` 那一支两条都给 `0`。） -/
theorem delta_ad (θ : Θ) (T' : Topo) :
    P.A θ T' .ab_cd - P.A θ T' .ad_bc = sgn2 T' * P.f θ := by
  rcases T' with _ | _ | _
  · obtain ⟨-, h2⟩ := P.clause_ab θ .ab_cd rfl
    simp only [sgn2_ab_cd]; linarith
  · obtain ⟨h1, h2⟩ := P.clause_ac θ .ac_bd rfl
    simp only [sgn2_ac_bd]; linarith
  · obtain ⟨h1, h2⟩ := P.clause_ad θ .ad_bc rfl
    simp only [sgn2_ad_bc]; linarith

end PropAData

/-! ## 2. 期望权重与命题 B -/

variable [MeasurableSpace Θ]

/-- **拓扑 `r` 的期望权重**：先按 `ν` 抽时间、再按 `τd θ` 抽基因树拓扑，然后取权重期望。

即 `r ↦ ∫ θ, ∑_{T'} τd θ T' · A θ T' r`。 -/
noncomputable def expWeight (ν : Measure Θ) (τd : Θ → Topo → ℝ)
    (A : Θ → Topo → Topo → ℝ) (r : Topo) : ℝ :=
  geneExpect ν τd (fun θ T' => A θ T' r)

/-- ★★★ **命题 B（物种树层，逐 quartet）**：真物种树拓扑 `ab|cd` 的期望权重
**严格大于两个错拓扑**。

证明：把 `expWeight` 的差用 ★★ `geneExpect_sub`（迭代期望的线性性）化成
「`delta`/`delta_ad` 的 `sgn`-加权和的期望」，再由引擎 ★★★ `MSCTopoSym.propB_of`
给出严格正。 -/
theorem expWeight_strict (S : MSCTopoSym Θ) (ν : Measure Θ) [IsProbabilityMeasure ν]
    (hdeep : MeasurableSet {θ | S.deep θ}) (P : PropAData Θ)
    (hf_int : Integrable P.f ν) (hf_pos : ∀ θ, ¬ S.deep θ → 0 < P.f θ)
    (hpos : 0 < ν {θ | ¬ S.deep θ})
    (hint_ab : Integrable (fun θ => ∑ T' : Topo, S.τd θ T' * P.A θ T' .ab_cd) ν)
    (hint_ac : Integrable (fun θ => ∑ T' : Topo, S.τd θ T' * P.A θ T' .ac_bd) ν)
    (hint_ad : Integrable (fun θ => ∑ T' : Topo, S.τd θ T' * P.A θ T' .ad_bc) ν) :
    expWeight ν S.τd P.A .ac_bd < expWeight ν S.τd P.A .ab_cd ∧
      expWeight ν S.τd P.A .ad_bc < expWeight ν S.τd P.A .ab_cd := by
  have key : ∀ (sgn : Topo → ℝ), (∑ T : Topo, sgn T) = 0 → sgn .ab_cd = 1 → ∀ r : Topo,
      Integrable (fun θ => ∑ T' : Topo, S.τd θ T' * P.A θ T' r) ν →
      (∀ θ T', P.A θ T' .ab_cd - P.A θ T' r = sgn T' * P.f θ) →
      expWeight ν S.τd P.A r < expWeight ν S.τd P.A .ab_cd := by
    intro sgn hs hb r hint_r hd
    have hsub : expWeight ν S.τd P.A .ab_cd - expWeight ν S.τd P.A r
        = geneExpect ν S.τd (fun θ T' => sgn T' * P.f θ) := by
      rw [expWeight, expWeight, ← geneExpect_sub ν S.τd _ _ hint_ab hint_r]
      unfold geneExpect
      refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
      exact Finset.sum_congr rfl fun T' _ => by
        show S.τd θ T' * (P.A θ T' .ab_cd - P.A θ T' r) = S.τd θ T' * (sgn T' * P.f θ)
        rw [hd θ T']
    have hpositive := S.propB_of ν hdeep sgn hs hb P.f hf_int hf_pos hpos
    linarith
  exact ⟨key sign (by rw [sum_topo]; simp [sign]) rfl .ac_bd hint_ac
          (fun θ T' => P.delta θ T'),
        key sgn2 sum_sgn2 rfl .ad_bc hint_ad (fun θ T' => P.delta_ad θ T')⟩

end Phylo.Stat.CASTERBridge
