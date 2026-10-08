/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Phylo.Stat.CASTERWeights

/-!
# `Phylo.Stat.CASTEREngine` —— CASTER 的**模型无关引擎**：命题 A ⇒ 命题 B

文献：Zhang, Nielsen, Mirarab (2025), *Science* **387**(6737) eadk9688，
**Supplementary** `sm.tex` 的 Proposition `prop:consistency_speciestree`（**1308–1440** 行）。

## 这一批在整条链里的位置

```
命题 A（基因树层）  E[w(真)|G] − f = E[w(错₁)|G] = E[w(错₂)|G]     ← 模型相关，各模型分头证
     │                                                            （JC69 ✅ / LM1 · F84 在建）
     ├── 本文件：命题 A ⇒ **命题 B**（物种树层：真拓扑期望得分严格最大）
     ▼
定理 1（一致性）  + 独立性 + 有界性 + 大数定律
```
本文件**不含任何模型相关的东西**（不认识 JC69/F84/LM），只把「命题 A ⇒ 命题 B」
这一步证成定理。**这正是 CASTER 区别于「平凡归约」的那一步**，也是老师口述里
「被压缩掉、但不是自动的」那个箭头。

## 记号与三条事实

* `sign : Topo → ℝ` 是 `ab|cd ↦ +1`、`ac|bd ↦ -1`、`ad|bc ↦ 0`。
* **`PropA`**（命题 A 的抽象接口）：`A θ T` = 「在基因树 `θ` 上，拓扑 `T` 的位点权重期望」；
  `f θ` = 幅度；`τ θ` = 该基因树的无根拓扑。三条子句说的是
  **「基因树自己的那个拓扑」的期望 − `f` 等于另两个拓扑的期望，且另两个彼此相等**。
  🔎 **这三条子句已在数值上逐条复核**（JC69、三种基因树形状 × 多组枝长）：
  `Δ = E[w(ab|cd)] − E[w(ac|bd)]` 与 `f` 的比恰为 `+1 / −1 / 0`（形状 `ab|cd / ac|bd / ad|bc`）。
  ⚠️ 第三支（`ad|bc`）的符号是 **`0`** 而不是 `−1` —— **这一点是抵消能成立的关键**。
* **`MSCTopoSym`**（MSC 在基因树层的对称性，Kingman 溯祖的标准事实）：
  「有深合并机会」时**三个无根拓扑等概率**；否则拓扑必为 `ab|cd`（点质量）。

## 本文件证什么

* ★★★ `PropA.delta`：`A θ .ab_cd - A θ .ac_bd = sign (τ θ) * f θ` —— 三条子句折成一个符号公式；
* ★★★ `MSCTopoSym.cancel`：`∑ T, τd θ T * sign T = [θ 无深合并]`
  —— **深合并抵消**：三拓扑等概率时 `(+1 - 1 + 0)/3 = 0`，无深合并时点质量给出 `1`。
  **这是命题 B 的心脏，且完全不需要测度论**；
* ★★ `integral_pos_of_indicator`：非负、可积、支集正测度的函数其积分 `> 0`（解析核心）；
* ★★★ `MSCTopoSym.propB`：`0 < geneExpect ν τd (fun θ T => sign T * f θ)`
  —— **命题 B**：真拓扑与任一错拓扑的期望权重差严格为正。

## 📌 为什么 `geneExpect` 是「定义」而不是「公理」

MSC 的基因树分布是「**先抽溯祖时间 `θ`，再按 `τd θ` 抽无根拓扑**」。把这个两步期望
写成迭代积分就是 `geneExpect ν τd g = ∫ θ, (∑ T, τd θ T * g θ T) ∂ν`
（`ν` 是时间层的概率测度），这正是 `Measure.sum`/`withDensity` 构造出的乘积型测度上的积分。
所以 `geneExpect` 是**模型的定义**，`MSCTopoSym` 的三条也只是「深合并时三拓扑等概率、
无深合并时拓扑确定」这一标准 MSC 事实的逐字转写。

⚠️ **诚实边界**：`ν {θ | ¬ deep θ} > 0`（无深合并有正概率）作为**假设**出现在 `propB` 里。
它是 Kingman 溯祖的直接推论（只要内部枝长 > 0，两支系在该枝内合并的概率就 > 0），
但**证明它需要真正的溯祖过程** —— 那与本项目既有的 `Phylo.Stat.MSC`（公理化 MSC）同一层，
见 `Phylo.Stat.MSCProof` 课题。本文件把它**显式列为假设**，而不是藏起来。 -/

noncomputable section

namespace Phylo.Stat.CASTEREngine

open Phylo.Stat.CASTERWeights

open MeasureTheory

/-! ## 1. 符号函数与三元求和 -/

/-- **符号函数**：`ab|cd ↦ +1`、`ac|bd ↦ -1`、`ad|bc ↦ 0`。

它把命题 A 的三条子句折成一条：`Δ = sign(τ)·f`。 -/
def sign : Topo → ℝ
  | .ab_cd => 1
  | .ac_bd => -1
  | .ad_bc => 0

@[simp] theorem sign_ab_cd : sign .ab_cd = 1 := rfl
@[simp] theorem sign_ac_bd : sign .ac_bd = -1 := rfl
@[simp] theorem sign_ad_bc : sign .ad_bc = 0 := rfl

/-- `Topo` 上只有三个元素，故 `∑ T, g T = g ab_cd + g ac_bd + g ad_bc`。 -/
theorem sum_topo (g : Topo → ℝ) :
    ∑ T : Topo, g T = g .ab_cd + g .ac_bd + g .ad_bc := by
  have h : (Finset.univ : Finset Topo) = {.ab_cd, .ac_bd, .ad_bc} := by decide
  rw [h, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  ring

/-! ## 2. 命题 A 的抽象接口 -/

/-- **命题 A（抽象形式）**：基因树层的期望权重模型。

* `A θ T` —— 在基因树 `θ` 上，拓扑 `T` 的位点权重期望；
* `f θ`   —— 幅度（各模型下都等于 `P(L_T)·Q(l_x)`）；
* `τ θ`   —— 该基因树的无根拓扑；

三条子句（附录 `prop:consistency_genetree` 逐字）：
**基因树自己的拓扑的期望 − `f` = 另两个拓扑的期望，且另两个彼此相等。** -/
structure PropA (Ω : Type*) where
  /-- 三个拓扑的期望权重。 -/
  A : Ω → Topo → ℝ
  /-- 幅度 `f`。 -/
  f : Ω → ℝ
  /-- 基因树的无根拓扑。 -/
  τ : Ω → Topo
  /-- 基因树拓扑为 `ab|cd` 时的子句。 -/
  clause_ab : ∀ θ, τ θ = .ab_cd →
    A θ .ab_cd - f θ = A θ .ac_bd ∧ A θ .ab_cd - f θ = A θ .ad_bc
  /-- 基因树拓扑为 `ac|bd` 时的子句。 -/
  clause_ac : ∀ θ, τ θ = .ac_bd →
    A θ .ac_bd - f θ = A θ .ab_cd ∧ A θ .ac_bd - f θ = A θ .ad_bc
  /-- 基因树拓扑为 `ad|bc` 时的子句。 -/
  clause_ad : ∀ θ, τ θ = .ad_bc →
    A θ .ad_bc - f θ = A θ .ab_cd ∧ A θ .ad_bc - f θ = A θ .ac_bd

/-- ★★★ **命题 A 的符号形式**：真物种树拓扑 `ab|cd` 与错拓扑 `ac|bd` 的期望权重差
等于 `sign (τ θ) · f θ`。

即三条子句合起来给出：基因树拓扑为 `ab|cd` 时差 `= +f`、为 `ac|bd` 时 `= -f`、
为 `ad|bc` 时 `= 0`（**第三种情形是三拓扑等概率时抵消的关键**）。 -/
theorem PropA.delta {Ω : Type*} (P : PropA Ω) (θ : Ω) :
    P.A θ .ab_cd - P.A θ .ac_bd = sign (P.τ θ) * P.f θ := by
  rcases h : P.τ θ with _ | _ | _
  · obtain ⟨h1, _⟩ := P.clause_ab θ h
    simp only [sign_ab_cd]; linarith
  · obtain ⟨h1, _⟩ := P.clause_ac θ h
    simp only [sign_ac_bd]; linarith
  · obtain ⟨h1, h2⟩ := P.clause_ad θ h
    simp only [sign_ad_bc]; linarith

/-! ## 3. MSC 在基因树层的拓扑对称性 -/

/-- **MSC 的拓扑对称性**（Kingman 溯祖的标准事实）：

* `deep θ` —— 时间数据 `θ` 是否**给了深合并的机会**；
* `τd θ T` —— 给定 `θ` 时无根拓扑 `T` 的条件概率；
* **无深合并 ⇒ 拓扑必为 `ab|cd`**（点质量）；
* **有深合并 ⇒ 三个无根拓扑各 `1/3`**。

（这两条就是附录 `unbalanced/balanced_genetrees` 图里「同一组合并时刻、不同拓扑」
那几类的对称性。） -/
structure MSCTopoSym (Θ : Type*) where
  /-- 是否给了深合并的机会。 -/
  deep : Θ → Prop
  /-- 给定时间数据时的拓扑条件分布。 -/
  τd : Θ → Topo → ℝ
  /-- 非负。 -/
  τd_nonneg : ∀ θ T, 0 ≤ τd θ T
  /-- 全概率为 1。 -/
  τd_sum : ∀ θ, ∑ T, τd θ T = 1
  /-- 无深合并 ⇒ 拓扑是 `ab|cd`（点质量）。 -/
  not_deep : ∀ θ, ¬ deep θ → τd θ .ab_cd = 1
  /-- 有深合并 ⇒ `ab|cd` 占 `1/3`。 -/
  deep_ab : ∀ θ, deep θ → τd θ .ab_cd = 1 / 3
  /-- 有深合并 ⇒ `ac|bd` 占 `1/3`。 -/
  deep_ac : ∀ θ, deep θ → τd θ .ac_bd = 1 / 3

/-- ★★★ **深合并抵消**：`∑ T, τd θ T * sign T = [θ 无深合并]`（右端是无深合并集的指示函数）。

* 深合并：三个拓扑各 `1/3` ⇒ `(1/3)(+1) + (1/3)(-1) + (1/3)(0) = 0`；
* 无深合并：点质量在 `ab|cd` ⇒ `1·(+1) + 0·(-1) + 0·0 = 1`。

⚠️ 注意 `ad|bc` 的符号是 `0`（不是 `-1`）——**这一条是抵消能成立的关键**：
`+f` 与 `-f` 各占 `1/3`，第三类必须贡献 `0`。所以命题 A 的**第三条子句**不是装饰。 -/
theorem MSCTopoSym.cancel {Θ : Type*} (S : MSCTopoSym Θ) (θ : Θ) :
    ∑ T : Topo, S.τd θ T * sign T
      = {θ' : Θ | ¬ S.deep θ'}.indicator (fun _ => (1 : ℝ)) θ := by
  have hsum : S.τd θ .ab_cd + S.τd θ .ac_bd + S.τd θ .ad_bc = 1 := by
    simpa [sum_topo] using S.τd_sum θ
  rw [sum_topo]
  by_cases h : S.deep θ
  · have hmem : θ ∉ {θ' : Θ | ¬ S.deep θ'} := by simpa using h
    have hab := S.deep_ab θ h
    have hac := S.deep_ac θ h
    have had : S.τd θ .ad_bc = 1 / 3 := by linarith
    rw [hab, hac, had, Set.indicator_of_notMem hmem]
    norm_num
  · have hmem : θ ∈ {θ' : Θ | ¬ S.deep θ'} := by simpa using h
    have hab := S.not_deep θ h
    have h1 := S.τd_nonneg θ .ac_bd
    have h2 := S.τd_nonneg θ .ad_bc
    have hac : S.τd θ .ac_bd = 0 := by linarith
    have had : S.τd θ .ad_bc = 0 := by linarith
    rw [hab, hac, had, Set.indicator_of_mem hmem]
    norm_num

/-! ## 4. 迭代期望与解析核心（与模型、与 MSC 都无关） -/

/-- **基因树层的迭代期望**：先按 `ν` 抽时间数据 `θ`，再按 `τd θ` 抽无根拓扑。

`geneExpect ν τd g = ∫ θ, (∑ T, τd θ T * g θ T) ∂ν` —— 这就是「两步期望」的定义。 -/
noncomputable def geneExpect {Θ : Type*} [MeasurableSpace Θ] (ν : Measure Θ)
    (τd : Θ → Topo → ℝ) (g : Θ → Topo → ℝ) : ℝ :=
  ∫ θ, (∑ T : Topo, τd θ T * g θ T) ∂ν

/-- ★★ **解析核心**：集合 `s` 上处处为正的可积函数，其指示函数的积分 `> 0`（`s` 正测度）。

（`propB` 用它：那里 `s = {θ | θ 无深合并}`，指示函数积分正是「无深合并那一部分的期望」。） -/
theorem integral_pos_of_indicator {Θ : Type*} [MeasurableSpace Θ] (ν : Measure Θ)
    [IsProbabilityMeasure ν] (s : Set Θ) (hs : MeasurableSet s)
    (f : Θ → ℝ) (hf_int : Integrable f ν) (hf_pos : ∀ θ ∈ s, 0 < f θ) (hpos : 0 < ν s) :
    0 < ∫ θ, s.indicator f θ ∂ν := by
  have hint : Integrable (s.indicator f) ν := hf_int.indicator hs
  have hnn : 0 ≤ᵐ[ν] s.indicator f :=
    Filter.Eventually.of_forall fun θ => Set.indicator_nonneg (fun θ hθ => (hf_pos θ hθ).le) θ
  have hsupp : Function.support (s.indicator f) = s := by
    ext θ
    simp only [Function.mem_support]
    by_cases h : θ ∈ s
    · rw [Set.indicator_of_mem h]
      exact iff_of_true (hf_pos θ h).ne' h
    · rw [Set.indicator_of_notMem h]
      exact iff_of_false (fun hz => hz rfl) h
  exact (integral_pos_iff_support_of_nonneg_ae hnn hint).mpr (by rwa [hsupp])

/-! ## 5. ★★★ 命题 B（物种树层） -/

/-- ★★★ **命题 B（物种树层）**：真物种树拓扑 `ab|cd` 与错拓扑 `ac|bd` 的
**期望权重差严格为正**。

证明：由 ★★★ `MSCTopoSym.cancel` 把条件期望化为「无深合并集」上的指示函数，
再由 ★★ `integral_pos_of_indicator`（正函数在正测度集上积分 > 0）。

**这就是老师口述里「被压缩掉的一步」**：`f` 只依赖 `(L_T, l_x)`（时间数据），
所以在「同一组合并时刻、不同拓扑」的每一组里，`+f` 与 `-f` 各占 `1/3` 而相消；
无深合并的那些（拓扑必为 `ab|cd`）留下 `+f > 0`。 -/
theorem MSCTopoSym.propB {Θ : Type*} [MeasurableSpace Θ] (S : MSCTopoSym Θ) (ν : Measure Θ)
    [IsProbabilityMeasure ν] (hdeep : MeasurableSet {θ | S.deep θ})
    (f : Θ → ℝ) (hf_int : Integrable f ν) (hf_pos : ∀ θ, ¬ S.deep θ → 0 < f θ)
    (hpos : 0 < ν {θ | ¬ S.deep θ}) :
    0 < geneExpect ν S.τd (fun θ T => sign T * f θ) := by
  have hs : MeasurableSet {θ : Θ | ¬ S.deep θ} := hdeep.compl
  have hcongr : geneExpect ν S.τd (fun θ T => sign T * f θ)
      = ∫ θ, {θ' : Θ | ¬ S.deep θ'}.indicator f θ ∂ν := by
    unfold geneExpect
    refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
    show (∑ T : Topo, S.τd θ T * (sign T * f θ)) = {θ' : Θ | ¬ S.deep θ'}.indicator f θ
    have hstep : (∑ T : Topo, S.τd θ T * (sign T * f θ))
        = (∑ T : Topo, S.τd θ T * sign T) * f θ := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun T _ => by ring
    rw [hstep, S.cancel θ]
    by_cases h : θ ∈ {θ' : Θ | ¬ S.deep θ'}
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, one_mul]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, zero_mul]
  rw [hcongr]
  exact integral_pos_of_indicator ν _ hs f hf_int (fun θ hθ => hf_pos θ hθ) hpos

end Phylo.Stat.CASTEREngine
