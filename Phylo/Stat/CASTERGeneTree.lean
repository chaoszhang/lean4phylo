/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.Stat.CASTERJC69
import Phylo.Stat.CASTEREngine
import Phylo.Stat.CASTERTopo
import Mathlib.Tactic

/-!
# `Phylo.Stat.CASTERGeneTree` —— 基因树层的 JC69 得分与命题 A 接口

文献：Zhang, Nielsen, Mirarab (2025), *Science* **387**(6737) eadk9688,
"Direct species tree inference from whole-genome alignments"，
**Supplementary** `sm.tex` 的 Proposition `prop:consistency_genetree`（**1308–1440** 行）
与 Fig. 1C 的 JC69 权重表（**348–375** 行）。

## 这一环补的是什么

```
Phylo.Stat.CASTERWeights   JC69 逐模式权重表 wJC / wJCR（+ 同侧、两侧互换三条对称性）
Phylo.CASTERJC69           ★★★ 基准坐标下的得分差闭式：
                             score t .ab_cd - score t .ac_bd = (3/4)·e(t 0)e(t 1)e(t 3)e(t 4)·(1 - e(t 2))
                             ★★ score t .ac_bd = score t .ad_bc
Phylo.Stat.CASTEREngine    抽象引擎：命题 A ⇒ 命题 B（完全不认识 JC69）
        ▲
        └── 本文件：把上面两块**接起来**
```

**基因树**由三样东西决定：形状 `S : Topo`（其无根 split 是 `S` 的那一对配对）、
叶长 `l : Fin 4 → ℝ`（按**物种**编号）、内部枝长 `lx`。它在**基准坐标** `ab|cd` 下的
规范枝长向量是

`canonLen S l lx = ![l (perm S 0), l (perm S 1), lx, l (perm S 2), l (perm S 3)]`，

拓扑 `T` 的期望权重是

`geneScore S l lx T = ∑_σ wJCR T σ · patternProb (canonLen S l lx) (σ ∘ perm S)`
（`wJCR T σ = wJCBase (σ ∘ perm T)`，`perm S` 把基准位置映到物种）。

本文件证：

* ★★ **九条表项** `geneScore_tab`：把「形状 `S` 的基因树」的期望权重搬回基准坐标时，
  `T` 要换成 `tab S T`：

  | 形状 `S` \ 拓扑 `T` | `ab_cd` | `ac_bd` | `ad_bc` |
  |---|---|---|---|
  | `ab_cd` | `ab_cd` | `ac_bd` | `ad_bc` |
  | `ac_bd` | `ac_bd` | `ab_cd` | `ad_bc` |
  | `ad_bc` | `ac_bd` | `ad_bc` | `ab_cd` |

* ★★★ `geneScore_delta`：
  `geneScore S l lx .ab_cd - geneScore S l lx .ac_bd = sign S · f`，
  其中 `f = (3/4)·e(l(perm S 0))·e(l(perm S 1))·e(l(perm S 2))·e(l(perm S 3))·(1 - e lx)`；
* ★★ `geneScore_delta_unpermuted`：把右端的叶长乘积写成 `l 0 · l 1 · l 2 · l 3` 的顺序；
* ★★ 三条「两个错拓扑得分相等」（`geneScore_ac_bd_eq_ad_bc_of_shape_ab_cd` 等）；
* ★★★ `jc69PropA : PropA GTree`：**命题 A 对 JC69 成立** ——
  即 CASTER 证明链里「具体模型 ⇒ 抽象引擎接口」的那一环。

## 证明路线（重指标 + 权重表的基准坐标对称性）

1. 记 `p = perm S`。用 `Equiv.sum_comp` 把 `geneScore` 的求和重指标
   （★ `sum_comp_perm`：`∑_σ F (σ ∘ p) = ∑_τ F τ`）；
2. 于是每条表项只需证 `∀ σ, wJCR T σ = wJCR T' (σ ∘ p)`。因为
   `wJC T σ = wJCBase (σ ∘ perm T)`，这等价于把复合置换 `p ∘ perm T'` 化成 `perm T`，
   **只差 `wJCBase` 的一条不变量**：★ `wJCBase_comp_swap23`
   （基准坐标的**第 2、3 位交换**不变，来自 `CASTERWeights.wJC_swap_cd`）。
   九条表项里只有 4 条需要这条对称性，其余 5 条在基准坐标下逐字相同；
3. 三条主定理由 `CASTERJC69.score_ab_cd_sub_ac_bd` / `score_ac_bd_eq_ad_bc` 加 `sign` 收口。

## 第二段（§10–§11）：接到抽象引擎，端到端可用

* §10：形状无关的幅度 `jc69Amp`、重指标 `prod_e_len_perm`，以及 `PropAData` 三条子句需要的
  「自己的拓扑减 `f` 等于另一个」在三个形状上的版本（`geneScore_ab_cd_self_sub` /
  `geneScore_ac_bd_self_sub` / **`geneScore_ad_bc_self_sub`** —— 最后一条是本批新补的）；
* §11：★★★ `jc69PropAData : PropAData ((Fin 4 → ℝ) × ℝ)`（时间 = （叶长, 内部枝长））
  与 ★★★ 端到端定理 1：`propAData_caster_statisticallyConsistent`（任意模型）与
  `jc69_caster_statisticallyConsistent`（JC69：`∃ N, ∀ n ≥ N, IsTrueT ab_cd (E n)`）。

「大数定律」`hconv`（`TopoClose (emp n) W ε` 最终成立）**作为显式假设**出现，
与 `Phylo.Stat.CASTERTopo.topo_statisticallyConsistent` 一致 —— 不新增公理。

## 诚实边界

* 本文件只做 **JC69**（附录 Fig. 1C）。F84 / LM1 的 `PropAData` 实例不在本批范围
  （见 `Phylo.Stat.CASTERWeights` 的「诚实边界」）；不过 §11 的
  `propAData_caster_statisticallyConsistent` 对**任意** `PropAData` 成立，换模型不用改一行。
* `jc69PropA` 只断言**命题 A**（基因树层）；「命题 A ⇒ 命题 B」在
  `Phylo.Stat.CASTEREngine` / `Phylo.Stat.CASTERBridge` 里，模型无关。
  「`ν{无深合并} > 0`」这一条 MSC 假设在 `MSCTopoSym` 那一层，与本文件无关。
* 端到端定理的**结论止于 quartet 拓扑层**（`X = Fin 4`，只有一个 4-元集）：
  「升级为树同构」由 `Phylo.Stat.QuartetDecides` 承担，多物种的逐 quartet 求和
  由 `Phylo.Stat.CASTERTheorem1` 承担（CASTER 附录原文的做法）。
* 本文件不含 `sorry` / `axiom` / `import Mathlib`。
-/

noncomputable section

namespace Phylo.Stat.CASTERGeneTree

open Phylo.Stat.CASTERWeights
open Phylo.CASTERJC69
open Phylo.JC
open Phylo.Stat.CASTEREngine
open Phylo.Stat.CASTERTopo
open Phylo.Stat.CASTERBridge
open MeasureTheory

/-! ## 1. `wJCBase` 在基准坐标上的对称性

`CASTERWeights` 的三条对称性说的是「权重表在**同侧互换**（`a↔b`、`c↔d`）与
**两侧互换**（`{a,b}↔{c,d}`）下不变」。在基准坐标 `ab|cd` 里：

* `a↔b` 是位置 `0↔1`；
* `c↔d` 是位置 `2↔3`（★ 本文件主要用这一条）；
* 两侧互换是位置 `(0 2)(1 3)`。 -/

/-- ★ **`wJCBase` 对基准坐标的第 2、3 位交换不变**（`c ↔ d` 同侧互换的 `wJCBase` 形式）。 -/
theorem wJCBase_comp_swap23 (b : Fin 4 → Fin 4) :
    wJCBase (b ∘ Equiv.swap 2 3) = wJCBase b :=
  (wJC_swap_cd b).symm

/-- ★ **`wJCBase` 对基准坐标的第 0、1 位交换不变**（`a ↔ b` 同侧互换的 `wJCBase` 形式）。 -/
theorem wJCBase_comp_swap01 (b : Fin 4 → Fin 4) :
    wJCBase (b ∘ Equiv.swap 0 1) = wJCBase b :=
  (wJC_swap_ab b).symm

/-- ★ **`wJCBase` 对两侧互换 `(0 2)(1 3)` 不变**（`{a,b} ↔ {c,d}` 的 `wJCBase` 形式）。 -/
theorem wJCBase_comp_sidesPerm (b : Fin 4 → Fin 4) :
    wJCBase (b ∘ sidesPerm) = wJCBase b :=
  (wJC_swap_sides .ab_cd b).symm

/-! ## 2. `perm` 在 `Fin 4` 上的取值与四条复合恒等式

`perm` 的显式取值（`(perm S) i` = 基准位置 `i` 上的**物种**）：

* `perm .ab_cd = [0,1,2,3]`（恒等）；
* `perm .ac_bd = [0,2,1,3]`（= `swap 1 2`，对合）；
* `perm .ad_bc = [0,3,1,2]`（= `swap 1 2 * swap 1 3`）。

下面四条是第 4 节重指标需要的**置换复合恒等式**，全部由 `fin_cases` + `decide` 穷举
四个位置机械验证（`Fin 4` 上是字面量比较，`decide` 能一路归约到底）。 -/

@[simp] theorem perm_ab_cd_apply (i : Fin 4) : perm .ab_cd i = i := by
  fin_cases i <;> decide

@[simp] theorem perm_ac_bd_apply (i : Fin 4) : perm .ac_bd i = Equiv.swap 1 2 i := by
  fin_cases i <;> decide

@[simp] theorem perm_ad_bc_apply (i : Fin 4) :
    perm .ad_bc i = Equiv.swap 1 2 (Equiv.swap 1 3 i) := by
  fin_cases i <;> decide

/-- `perm .ac_bd` 是对合：`perm .ab_cd = perm .ac_bd ∘ perm .ac_bd`（两边都是恒等）。 -/
theorem perm_ab_cd_eq_ac_bd_comp_self (i : Fin 4) :
    perm .ab_cd i = perm .ac_bd (perm .ac_bd i) := by
  fin_cases i <;> decide

/-- `perm .ac_bd ∘ perm .ad_bc = perm .ad_bc ∘ swap 2 3`（两边都是 `swap 1 3`）。 -/
theorem perm_ad_bc_eq_ac_bd_comp_ad_bc_swap (i : Fin 4) :
    perm .ad_bc i = perm .ac_bd (perm .ad_bc (Equiv.swap 2 3 i)) := by
  fin_cases i <;> decide

/-- `perm .ab_cd = perm .ad_bc ∘ perm .ac_bd ∘ swap 2 3`（两边都是恒等）。 -/
theorem perm_ab_cd_eq_ad_bc_comp_ac_bd_swap (i : Fin 4) :
    perm .ab_cd i = perm .ad_bc (perm .ac_bd (Equiv.swap 2 3 i)) := by
  fin_cases i <;> decide

/-- `perm .ac_bd = perm .ad_bc ∘ perm .ad_bc ∘ swap 2 3`（两边都是 `swap 1 2`）。 -/
theorem perm_ac_bd_eq_ad_bc_comp_self_swap (i : Fin 4) :
    perm .ac_bd i = perm .ad_bc (perm .ad_bc (Equiv.swap 2 3 i)) := by
  fin_cases i <;> decide

/-! ## 3. 规范枝长向量与基因树的期望权重 -/

/-- 形状为 `S` 的基因树在基准 `ab|cd` 坐标下的**规范枝长向量**：

位置 `0,1` 放 `S` 一侧的两条叶边、位置 `3,4` 放另一侧的两条叶边、位置 `2` 放内部枝长。

（与 `Phylo.JC.patternProb` 的约定一致：`t 0, t 1` 挂在内部顶点 `a` 上，
`t 3, t 4` 挂在内部顶点 `b` 上，`t 2` 是 `a—b`。） -/
def canonLen (S : Topo) (l : Fin 4 → ℝ) (lx : ℝ) : Fin 5 → ℝ :=
  ![l (perm S 0), l (perm S 1), lx, l (perm S 2), l (perm S 3)]

@[simp] theorem canonLen_zero (S : Topo) (l : Fin 4 → ℝ) (lx : ℝ) :
    canonLen S l lx 0 = l (perm S 0) := rfl

@[simp] theorem canonLen_one (S : Topo) (l : Fin 4 → ℝ) (lx : ℝ) :
    canonLen S l lx 1 = l (perm S 1) := rfl

@[simp] theorem canonLen_two (S : Topo) (l : Fin 4 → ℝ) (lx : ℝ) :
    canonLen S l lx 2 = lx := rfl

@[simp] theorem canonLen_three (S : Topo) (l : Fin 4 → ℝ) (lx : ℝ) :
    canonLen S l lx 3 = l (perm S 2) := rfl

@[simp] theorem canonLen_four (S : Topo) (l : Fin 4 → ℝ) (lx : ℝ) :
    canonLen S l lx 4 = l (perm S 3) := rfl

/-- 形状 `S`、叶长 `l`（按物种）、内部长 `lx` 的基因树上，拓扑 `T` 的**期望权重**：

`geneScore S l lx T = ∑_σ wJCR T σ · patternProb (canonLen S l lx) (σ ∘ perm S)`。

（`patternProb` 的 256 个位点模式都写在**基准坐标**里，而基因树的叶位置按 `perm S`
排列，故模式的第 `i` 位取 `σ (perm S i)`。） -/
noncomputable def geneScore (S : Topo) (l : Fin 4 → ℝ) (lx : ℝ) (T : Topo) : ℝ :=
  ∑ σ : Fin 4 → Fin 4, wJCR T σ * patternProb (canonLen S l lx) (fun i => σ (perm S i))

/-! ## 4. 重指标与表项的一般引理 -/

/-- ★ **重指标**：置换 `p` 右复合是 `Fin 4 → Fin 4` 上的双射，故
`∑_σ F (σ ∘ p) = ∑_τ F τ`。

（`Equiv.arrowCongr p.symm (Equiv.refl _)` 的 `toFun` 正是 `f ↦ f ∘ p`。） -/
theorem sum_comp_perm (p : Equiv.Perm (Fin 4)) (F : (Fin 4 → Fin 4) → ℝ) :
    (∑ σ : Fin 4 → Fin 4, F (fun i => σ (p i))) = ∑ τ : Fin 4 → Fin 4, F τ :=
  Equiv.sum_comp (Equiv.arrowCongr p.symm (Equiv.refl (Fin 4))) F

/-- ★★ **表项的一般引理**：若逐模式下 `wJCR T σ = wJCR T' (σ ∘ perm S)`，
则形状 `S` 的基因树上拓扑 `T` 的期望权重，就是把规范枝长丢进基准坐标得分 `T'`。

证明：重指标 `σ ↦ σ ∘ perm S`（`sum_comp_perm`）后逐项改写。 -/
theorem geneScore_eq_score_of (S T T' : Topo) (l : Fin 4 → ℝ) (lx : ℝ)
    (h : ∀ σ : Fin 4 → Fin 4, wJCR T σ = wJCR T' (fun i => σ (perm S i))) :
    geneScore S l lx T = score (canonLen S l lx) T' := by
  have h1 : geneScore S l lx T
      = ∑ σ : Fin 4 → Fin 4, wJCR T' (fun i => σ (perm S i))
          * patternProb (canonLen S l lx) (fun i => σ (perm S i)) := by
    simp only [geneScore]
    exact Finset.sum_congr rfl fun σ _ => by rw [h σ]
  rw [h1]
  unfold score
  exact Equiv.sum_comp (Equiv.arrowCongr (perm S).symm (Equiv.refl (Fin 4)))
    (fun τ => wJCR T' τ * patternProb (canonLen S l lx) τ)

/-! ## 5. 逐模式的 `wJCR` 不变性（只有 4 条是实质性的）

对 `S = ab_cd`（`perm S = 1`）与 `T = T'` 等情形，两边的 `wJCBase` 参数在基准坐标下
逐字相同，`rfl` 即可。真正需要第 1 节那条 `2 ↔ 3` 对称性的只有四条，见下面。 -/

/-- 表项 `(S, T) = (ac_bd, ab_cd) ↦ ac_bd`：`wJCR ab_cd σ = wJCR ac_bd (σ ∘ perm ac_bd)`。 -/
theorem wJCR_ab_cd_eq_ac_bd_comp_ac_bd (σ : Fin 4 → Fin 4) :
    wJCR .ab_cd σ = wJCR .ac_bd (fun i => σ (perm .ac_bd i)) := by
  have hfun : (fun i : Fin 4 => σ (perm .ab_cd i))
      = (fun j : Fin 4 => σ (perm .ac_bd (perm .ac_bd j))) := by
    funext i
    simp only [perm_ab_cd_eq_ac_bd_comp_self i]
  simp only [wJCR, wJC, hfun]

/-- 表项 `(S, T) = (ac_bd, ad_bc) ↦ ad_bc`：需要 `perm ac_bd ∘ perm ad_bc = perm ad_bc ∘ swap 2 3`。 -/
theorem wJCR_ad_bc_eq_ad_bc_comp_ac_bd (σ : Fin 4 → Fin 4) :
    wJCR .ad_bc σ = wJCR .ad_bc (fun i => σ (perm .ac_bd i)) := by
  have hfun : (fun i : Fin 4 => σ (perm .ad_bc i))
      = (fun j : Fin 4 => σ (perm .ac_bd (perm .ad_bc j))) ∘ Equiv.swap 2 3 := by
    funext i
    simp only [Function.comp_apply, perm_ad_bc_eq_ac_bd_comp_ad_bc_swap i]
  simp only [wJCR, wJC, hfun, wJCBase_comp_swap23]

/-- 表项 `(S, T) = (ad_bc, ab_cd) ↦ ac_bd`：需要 `perm ad_bc ∘ perm ac_bd = perm ab_cd ∘ swap 2 3`。 -/
theorem wJCR_ab_cd_eq_ac_bd_comp_ad_bc (σ : Fin 4 → Fin 4) :
    wJCR .ab_cd σ = wJCR .ac_bd (fun i => σ (perm .ad_bc i)) := by
  have hfun : (fun i : Fin 4 => σ (perm .ab_cd i))
      = (fun j : Fin 4 => σ (perm .ad_bc (perm .ac_bd j))) ∘ Equiv.swap 2 3 := by
    funext i
    simp only [Function.comp_apply, perm_ab_cd_eq_ad_bc_comp_ac_bd_swap i]
  simp only [wJCR, wJC, hfun, wJCBase_comp_swap23]

/-- 表项 `(S, T) = (ad_bc, ac_bd) ↦ ad_bc`：需要 `perm ad_bc ∘ perm ad_bc = perm ac_bd ∘ swap 2 3`。 -/
theorem wJCR_ac_bd_eq_ad_bc_comp_ad_bc (σ : Fin 4 → Fin 4) :
    wJCR .ac_bd σ = wJCR .ad_bc (fun i => σ (perm .ad_bc i)) := by
  have hfun : (fun i : Fin 4 => σ (perm .ac_bd i))
      = (fun j : Fin 4 => σ (perm .ad_bc (perm .ad_bc j))) ∘ Equiv.swap 2 3 := by
    funext i
    simp only [Function.comp_apply, perm_ac_bd_eq_ad_bc_comp_self_swap i]
  simp only [wJCR, wJC, hfun, wJCBase_comp_swap23]

/-! ## 6. 九条表项 -/

/-- ★★ 表项 `(ab_cd, ab_cd) ↦ ab_cd`。 -/
theorem geneScore_ab_cd_ab_cd (l : Fin 4 → ℝ) (lx : ℝ) :
    geneScore .ab_cd l lx .ab_cd = score (canonLen .ab_cd l lx) .ab_cd :=
  geneScore_eq_score_of .ab_cd .ab_cd .ab_cd l lx fun _ => rfl

/-- ★★ 表项 `(ab_cd, ac_bd) ↦ ac_bd`。 -/
theorem geneScore_ab_cd_ac_bd (l : Fin 4 → ℝ) (lx : ℝ) :
    geneScore .ab_cd l lx .ac_bd = score (canonLen .ab_cd l lx) .ac_bd :=
  geneScore_eq_score_of .ab_cd .ac_bd .ac_bd l lx fun _ => rfl

/-- ★★ 表项 `(ab_cd, ad_bc) ↦ ad_bc`。 -/
theorem geneScore_ab_cd_ad_bc (l : Fin 4 → ℝ) (lx : ℝ) :
    geneScore .ab_cd l lx .ad_bc = score (canonLen .ab_cd l lx) .ad_bc :=
  geneScore_eq_score_of .ab_cd .ad_bc .ad_bc l lx fun _ => rfl

/-- ★★ 表项 `(ac_bd, ab_cd) ↦ ac_bd`。 -/
theorem geneScore_ac_bd_ab_cd (l : Fin 4 → ℝ) (lx : ℝ) :
    geneScore .ac_bd l lx .ab_cd = score (canonLen .ac_bd l lx) .ac_bd :=
  geneScore_eq_score_of .ac_bd .ab_cd .ac_bd l lx wJCR_ab_cd_eq_ac_bd_comp_ac_bd

/-- ★★ 表项 `(ac_bd, ac_bd) ↦ ab_cd`。 -/
theorem geneScore_ac_bd_ac_bd (l : Fin 4 → ℝ) (lx : ℝ) :
    geneScore .ac_bd l lx .ac_bd = score (canonLen .ac_bd l lx) .ab_cd :=
  geneScore_eq_score_of .ac_bd .ac_bd .ab_cd l lx fun _ => rfl

/-- ★★ 表项 `(ac_bd, ad_bc) ↦ ad_bc`。 -/
theorem geneScore_ac_bd_ad_bc (l : Fin 4 → ℝ) (lx : ℝ) :
    geneScore .ac_bd l lx .ad_bc = score (canonLen .ac_bd l lx) .ad_bc :=
  geneScore_eq_score_of .ac_bd .ad_bc .ad_bc l lx wJCR_ad_bc_eq_ad_bc_comp_ac_bd

/-- ★★ 表项 `(ad_bc, ab_cd) ↦ ac_bd`。 -/
theorem geneScore_ad_bc_ab_cd (l : Fin 4 → ℝ) (lx : ℝ) :
    geneScore .ad_bc l lx .ab_cd = score (canonLen .ad_bc l lx) .ac_bd :=
  geneScore_eq_score_of .ad_bc .ab_cd .ac_bd l lx wJCR_ab_cd_eq_ac_bd_comp_ad_bc

/-- ★★ 表项 `(ad_bc, ac_bd) ↦ ad_bc`。 -/
theorem geneScore_ad_bc_ac_bd (l : Fin 4 → ℝ) (lx : ℝ) :
    geneScore .ad_bc l lx .ac_bd = score (canonLen .ad_bc l lx) .ad_bc :=
  geneScore_eq_score_of .ad_bc .ac_bd .ad_bc l lx wJCR_ac_bd_eq_ad_bc_comp_ad_bc

/-- ★★ 表项 `(ad_bc, ad_bc) ↦ ab_cd`。 -/
theorem geneScore_ad_bc_ad_bc (l : Fin 4 → ℝ) (lx : ℝ) :
    geneScore .ad_bc l lx .ad_bc = score (canonLen .ad_bc l lx) .ab_cd :=
  geneScore_eq_score_of .ad_bc .ad_bc .ab_cd l lx fun _ => rfl

/-- **表项映射** `tab S T`：形状 `S` 的基因树上，基准坐标得分要取的拓扑。 -/
def tab : Topo → Topo → Topo
  | .ab_cd, T => T
  | .ac_bd, .ab_cd => .ac_bd
  | .ac_bd, .ac_bd => .ab_cd
  | .ac_bd, .ad_bc => .ad_bc
  | .ad_bc, .ab_cd => .ac_bd
  | .ad_bc, .ac_bd => .ad_bc
  | .ad_bc, .ad_bc => .ab_cd

/-- ★★ **九条表项合成一条**：`geneScore S l lx T = score (canonLen S l lx) (tab S T)`。 -/
theorem geneScore_tab (S T : Topo) (l : Fin 4 → ℝ) (lx : ℝ) :
    geneScore S l lx T = score (canonLen S l lx) (tab S T) := by
  cases S
  · cases T
    · exact geneScore_ab_cd_ab_cd l lx
    · exact geneScore_ab_cd_ac_bd l lx
    · exact geneScore_ab_cd_ad_bc l lx
  · cases T
    · exact geneScore_ac_bd_ab_cd l lx
    · exact geneScore_ac_bd_ac_bd l lx
    · exact geneScore_ac_bd_ad_bc l lx
  · cases T
    · exact geneScore_ad_bc_ab_cd l lx
    · exact geneScore_ad_bc_ac_bd l lx
    · exact geneScore_ad_bc_ad_bc l lx

/-! ## 7. 两个「错」拓扑的期望权重相等

（命题 A 三条子句里的第二个等号就是这三条；它们全部由
`CASTERJC69.score_ac_bd_eq_ad_bc` 给出。） -/

/-- ★★ 形状 `ab|cd` 的基因树上，两个错拓扑的期望权重相等。 -/
theorem geneScore_ac_bd_eq_ad_bc_of_shape_ab_cd (l : Fin 4 → ℝ) (lx : ℝ) :
    geneScore .ab_cd l lx .ac_bd = geneScore .ab_cd l lx .ad_bc := by
  rw [geneScore_ab_cd_ac_bd, geneScore_ab_cd_ad_bc]
  exact score_ac_bd_eq_ad_bc (canonLen .ab_cd l lx)

/-- ★★ 形状 `ac|bd` 的基因树上，两个错拓扑的期望权重相等。 -/
theorem geneScore_ab_cd_eq_ad_bc_of_shape_ac_bd (l : Fin 4 → ℝ) (lx : ℝ) :
    geneScore .ac_bd l lx .ab_cd = geneScore .ac_bd l lx .ad_bc := by
  rw [geneScore_ac_bd_ab_cd, geneScore_ac_bd_ad_bc]
  exact score_ac_bd_eq_ad_bc (canonLen .ac_bd l lx)

/-- ★★ 形状 `ad|bc` 的基因树上，两个错拓扑的期望权重相等。 -/
theorem geneScore_ab_cd_eq_ac_bd_of_shape_ad_bc (l : Fin 4 → ℝ) (lx : ℝ) :
    geneScore .ad_bc l lx .ab_cd = geneScore .ad_bc l lx .ac_bd := by
  rw [geneScore_ad_bc_ab_cd, geneScore_ad_bc_ac_bd]
  exact score_ac_bd_eq_ad_bc (canonLen .ad_bc l lx)

/-! ## 8. ★★★ 命题 A 的具体形式 -/

/-- ★★★ **基因树层的 JC69 主定理**：真拓扑 `ab|cd` 与错拓扑 `ac|bd` 的期望权重差
等于 `sign S · f`，其中 `S` 是基因树自己的形状，`f` 是幅度。

* 形状 `ab|cd`：差 `= +f`；
* 形状 `ac|bd`：差 `= -f`（两个错拓扑互换角色）；
* 形状 `ad|bc`：差 `= 0` —— **这一支的符号是 `0` 而不是 `-1`**，是三拓扑等概率时
  深合并抵消能成立的关键（见 `Phylo.Stat.CASTEREngine.MSCTopoSym.cancel`）。 -/
theorem geneScore_delta (S : Topo) (l : Fin 4 → ℝ) (lx : ℝ) :
    geneScore S l lx .ab_cd - geneScore S l lx .ac_bd
      = sign S * ((3 / 4) * (e (l (perm S 0)) * e (l (perm S 1)) * e (l (perm S 2))
          * e (l (perm S 3))) * (1 - e lx)) := by
  cases S
  · rw [geneScore_ab_cd_ab_cd, geneScore_ab_cd_ac_bd, score_ab_cd_sub_ac_bd]
    simp only [sign_ab_cd, canonLen_zero, canonLen_one, canonLen_two, canonLen_three,
      canonLen_four]
    ring
  · have h := score_ab_cd_sub_ac_bd (canonLen .ac_bd l lx)
    rw [geneScore_ac_bd_ab_cd, geneScore_ac_bd_ac_bd]
    simp only [sign_ac_bd, canonLen_zero, canonLen_one, canonLen_two, canonLen_three,
      canonLen_four] at h ⊢
    linarith
  · rw [geneScore_ad_bc_ab_cd, geneScore_ad_bc_ac_bd, score_ac_bd_eq_ad_bc]
    simp only [sign_ad_bc]
    ring

/-- ★★ **主定理的「不置换」写法**：右端叶长乘积按 `l 0 · l 1 · l 2 · l 3` 的顺序。

（`perm S` 是 `Fin 4` 的置换，故 `∑ᵢ l (perm S i) = ∑ᵢ l i`，
再由 `e` 的可乘性 `e a · e b = e (a+b)` 合并。） -/
theorem geneScore_delta_unpermuted (S : Topo) (l : Fin 4 → ℝ) (lx : ℝ) :
    geneScore S l lx .ab_cd - geneScore S l lx .ac_bd
      = sign S * ((3 / 4) * (e (l 0) * e (l 1) * e (l 2) * e (l 3)) * (1 - e lx)) := by
  have hsum : l (perm S 0) + l (perm S 1) + l (perm S 2) + l (perm S 3)
      = l 0 + l 1 + l 2 + l 3 := by
    rw [← Fin.sum_univ_four (fun i => l (perm S i)), ← Fin.sum_univ_four l]
    exact Equiv.sum_comp (perm S) l
  have hL : e (l (perm S 0)) * e (l (perm S 1)) * e (l (perm S 2)) * e (l (perm S 3))
      = e (l 0 + l 1 + l 2 + l 3) := by
    rw [e_mul, e_mul, e_mul, hsum]
  have hR : e (l 0) * e (l 1) * e (l 2) * e (l 3) = e (l 0 + l 1 + l 2 + l 3) := by
    rw [e_mul, e_mul, e_mul]
  rw [geneScore_delta, hL, hR]

/-- ★★ 主定理的**指数形式**：`(3/4)·e (l 0 + l 1 + l 2 + l 3)·(1 - e lx)`。 -/
theorem geneScore_delta_exp (S : Topo) (l : Fin 4 → ℝ) (lx : ℝ) :
    geneScore S l lx .ab_cd - geneScore S l lx .ac_bd
      = sign S * ((3 / 4) * e (l 0 + l 1 + l 2 + l 3) * (1 - e lx)) := by
  rw [geneScore_delta_unpermuted, ← e_mul, ← e_mul, ← e_mul]

/-! ## 9. ★★★ 命题 A 对 JC69 成立（`PropA` 实例） -/

/-- **JC69 的基因树族**：由形状、叶长（按物种）、内部枝长参数化。 -/
structure GTree where
  /-- 无根基因树拓扑。 -/
  shape : Topo
  /-- 四条叶边长度（按**物种**编号）。 -/
  len : Fin 4 → ℝ
  /-- 内部枝长。 -/
  internal : ℝ

/-- ★★★ **命题 A 对 JC69 成立**：把 `geneScore_delta` 打包成抽象引擎的 `PropA` 接口。

* `A G T = geneScore G.shape G.len G.internal T`（基因树 `G` 上拓扑 `T` 的期望权重）；
* `f G = (3/4)·∏ᵢ e (G.len (perm G.shape i))·(1 - e G.internal)`（幅度）；
* `τ G = G.shape`（基因树自己的无根拓扑）；
* 三条子句：**真拓扑的期望 − `f` = 两个错拓扑的期望，且两个错拓扑彼此相等** ——
  第一条由 `geneScore_delta` 给出，第二条由第 7 节的三条「错拓扑相等」给出。 -/
noncomputable def jc69PropA : PropA GTree where
  A := fun G T => geneScore G.shape G.len G.internal T
  f := fun G => (3 / 4) * (e (G.len (perm G.shape 0)) * e (G.len (perm G.shape 1))
      * e (G.len (perm G.shape 2)) * e (G.len (perm G.shape 3))) * (1 - e G.internal)
  τ := fun G => G.shape
  clause_ab := by
    intro G h
    have hd := geneScore_delta G.shape G.len G.internal
    rw [h] at hd
    rw [sign_ab_cd, one_mul] at hd
    rw [h]
    refine ⟨?_, ?_⟩
    · linarith
    · have h2 := geneScore_ac_bd_eq_ad_bc_of_shape_ab_cd G.len G.internal
      linarith
  clause_ac := by
    intro G h
    have hd := geneScore_delta G.shape G.len G.internal
    rw [h] at hd
    rw [sign_ac_bd] at hd
    rw [h]
    refine ⟨?_, ?_⟩
    · linarith
    · have h2 := geneScore_ab_cd_eq_ad_bc_of_shape_ac_bd G.len G.internal
      linarith
  clause_ad := by
    intro G h
    have hd := geneScore_delta G.shape G.len G.internal
    rw [h] at hd
    rw [sign_ad_bc] at hd
    rw [h]
    have h2 := geneScore_ab_cd_eq_ac_bd_of_shape_ad_bc G.len G.internal
    have h3 : geneScore .ad_bc G.len G.internal .ad_bc
        - geneScore .ad_bc G.len G.internal .ab_cd
        = (3 / 4) * (e (G.len (perm .ad_bc 0)) * e (G.len (perm .ad_bc 1))
            * e (G.len (perm .ad_bc 2)) * e (G.len (perm .ad_bc 3)))
            * (1 - e G.internal) := by
      rw [geneScore_ad_bc_ad_bc, geneScore_ad_bc_ab_cd, score_ab_cd_sub_ac_bd]
      simp only [canonLen_zero, canonLen_one, canonLen_two, canonLen_three, canonLen_four]
    refine ⟨?_, ?_⟩
    · linarith
    · linarith

/-- ★★★ **命题 A ⇒ 符号形式**（`Phylo.Stat.CASTEREngine.PropA.delta` 在 JC69 上的实例）：
`A G .ab_cd - A G .ac_bd = sign (τ G) · f G`，即 `jc69PropA` 确实满足引擎要求的那条符号公式。 -/
theorem jc69PropA_delta (G : GTree) :
    jc69PropA.A G .ab_cd - jc69PropA.A G .ac_bd = sign (jc69PropA.τ G) * jc69PropA.f G :=
  PropA.delta jc69PropA G

/-! ## 10. 形状无关的幅度 `jc69Amp` 与三条「自己的拓扑减 `f`」恒等式

命题 A 的幅度（`CASTERBridge.PropAData.f`）必须与基因树的**形状无关** —— 它只依赖
叶长（按物种）与内部枝长。§8 的 `geneScore_delta` 右端是**置换后**的显式四项乘积
`e (l (perm S 0)) * … * e (l (perm S 3))`，本节用重指标 `prod_e_len_perm` 把它换成
`jc69Amp l lx = (3/4)·∏_i e (l i)·(1 - e lx)`。

同时补上 `PropAData` 三条子句需要的「自己的拓扑减 `f` 等于另一个」在三个形状上的版本：

| 形状 `S` | 恒等式 |
|---|---|
| `ab_cd` | `[ab] − [ac] = amp`（即 §8 `geneScore_delta .ab_cd`） |
| `ac_bd` | `[ac] − [ab] = amp`（§8 `geneScore_delta .ac_bd` 两边乘 `−1`） |
| `ad_bc` | `[ad] − [ab] = amp`（**本批新补**） |

第三条由九条表项 + `score_ab_cd_sub_ac_bd` 在 `canonLen .ad_bc l lx` 上直接给出：
`perm .ad_bc` 把四条叶长按 `0,3,1,2` 排列，`ring` 吸收这个重排。 -/

/-- JC69 的**形状无关**幅度：`(3/4)·∏_i e (l i)·(1 - e lx)`。

（`l` 按物种编号、`lx` 是内部枝长；与基因树形状 `S` 无关 —— 这正是命题 A 里
「幅度 `f` 只依赖时间数据」那一条的具体内容。） -/
def jc69Amp (l : Fin 4 → ℝ) (lx : ℝ) : ℝ := (3 / 4) * (∏ i : Fin 4, e (l i)) * (1 - e lx)

/-- ★ **重指标**：`∏ i, e (l (perm S i)) = ∏ i, e (l i)`（`f` 与形状无关的关键）。 -/
theorem prod_e_len_perm (l : Fin 4 → ℝ) (S : Topo) :
    ∏ i : Fin 4, e (l (perm S i)) = ∏ i : Fin 4, e (l i) :=
  Equiv.prod_comp (perm S) (fun i => e (l i))

/-- ★★ **置换乘积的显式四项形式**（`prod_e_len_perm` 的 `Fin.prod_univ_four` 展开）：

`e (l (perm S 0)) · … · e (l (perm S 3)) = e (l 0) · e (l 1) · e (l 2) · e (l 3)`。

这是 §8 `geneScore_delta` 右端（**置换后**的显式四项乘积）与 `jc69Amp`（物种顺序的
四项乘积）之间的桥。 -/
theorem e_prod_perm_eq (l : Fin 4 → ℝ) (S : Topo) :
    e (l (perm S 0)) * e (l (perm S 1)) * e (l (perm S 2)) * e (l (perm S 3))
      = e (l 0) * e (l 1) * e (l 2) * e (l 3) := by
  rw [← Fin.prod_univ_four (fun i => e (l (perm S i))), prod_e_len_perm l S,
    Fin.prod_univ_four (fun i => e (l i))]

/-- `jc69Amp` 的显式四项展开（与 §8 `geneScore_delta` 右端的形状逐字一致）。 -/
theorem jc69Amp_eq_four (l : Fin 4 → ℝ) (lx : ℝ) :
    jc69Amp l lx
      = (3 / 4) * (e (l 0) * e (l 1) * e (l 2) * e (l 3)) * (1 - e lx) := by
  rw [jc69Amp, Fin.prod_univ_four]

/-- ★★ **形状 `ab|cd` 的树**：自己的拓扑的期望权重减幅度 = `ac|bd` 支的期望权重。 -/
theorem geneScore_ab_cd_self_sub (l : Fin 4 → ℝ) (lx : ℝ) :
    geneScore .ab_cd l lx .ab_cd - geneScore .ab_cd l lx .ac_bd = jc69Amp l lx := by
  rw [geneScore_ab_cd_ab_cd, geneScore_ab_cd_ac_bd, score_ab_cd_sub_ac_bd]
  simp only [canonLen_zero, canonLen_one, canonLen_two, canonLen_three, canonLen_four,
    jc69Amp, Fin.prod_univ_four]
  rw [e_prod_perm_eq l .ab_cd]

/-- ★★ **形状 `ac|bd` 的树**：自己的拓扑的期望权重减幅度 = `ab|cd` 支的期望权重。 -/
theorem geneScore_ac_bd_self_sub (l : Fin 4 → ℝ) (lx : ℝ) :
    geneScore .ac_bd l lx .ac_bd - geneScore .ac_bd l lx .ab_cd = jc69Amp l lx := by
  rw [geneScore_ac_bd_ac_bd, geneScore_ac_bd_ab_cd, score_ab_cd_sub_ac_bd]
  simp only [canonLen_zero, canonLen_one, canonLen_two, canonLen_three, canonLen_four,
    jc69Amp, Fin.prod_univ_four]
  rw [e_prod_perm_eq l .ac_bd]

/-- ★★ **形状 `ad|bc` 的树（本批新补的一条）**：自己的拓扑的期望权重减幅度 = `ab|cd` 支的期望权重。

（`perm .ad_bc` 把四条叶长按 `0,3,1,2` 排列，`e_prod_perm_eq` 吸收这个重排。） -/
theorem geneScore_ad_bc_self_sub (l : Fin 4 → ℝ) (lx : ℝ) :
    geneScore .ad_bc l lx .ad_bc - geneScore .ad_bc l lx .ab_cd = jc69Amp l lx := by
  rw [geneScore_ad_bc_ad_bc, geneScore_ad_bc_ab_cd, score_ab_cd_sub_ac_bd]
  simp only [canonLen_zero, canonLen_one, canonLen_two, canonLen_three, canonLen_four,
    jc69Amp, Fin.prod_univ_four]
  rw [e_prod_perm_eq l .ad_bc]

/-! ## 11. ★★★ 命题 A 数据与端到端定理 1（JC69） -/

/-- ★★★ **JC69 的命题 A 数据**（时间 `θ = (叶长, 内部枝长)`）。

* `A θ T' r = geneScore T' θ.1 θ.2 r`：在形状 `T'`、叶长 `θ.1`、内部长 `θ.2` 的基因树上，
  拓扑 `r` 的期望权重；
* `f θ = jc69Amp θ.1 θ.2`：形状**无关**的幅度；
* 三条子句由 §10 的三条 `geneScore_*_self_sub`（第一个合取）与 §7 的三条
  「两个错拓扑期望权重相等」（第二个合取）给出。

这是把 `Phylo.Stat.CASTERJC69` + 本文件 §1–§10 插进 `Phylo.Stat.CASTERBridge` 的那一步。 -/
noncomputable def jc69PropAData : PropAData ((Fin 4 → ℝ) × ℝ) where
  A := fun θ T' r => geneScore T' θ.1 θ.2 r
  f := fun θ => jc69Amp θ.1 θ.2
  clause_ab := by
    intro θ T' h
    rw [h]
    refine ⟨?_, ?_⟩
    · have h1 := geneScore_ab_cd_self_sub θ.1 θ.2
      linarith
    · have h1 := geneScore_ab_cd_self_sub θ.1 θ.2
      have h2 := geneScore_ac_bd_eq_ad_bc_of_shape_ab_cd θ.1 θ.2
      linarith
  clause_ac := by
    intro θ T' h
    rw [h]
    refine ⟨?_, ?_⟩
    · have h1 := geneScore_ac_bd_self_sub θ.1 θ.2
      linarith
    · have h1 := geneScore_ac_bd_self_sub θ.1 θ.2
      have h2 := geneScore_ab_cd_eq_ad_bc_of_shape_ac_bd θ.1 θ.2
      linarith
  clause_ad := by
    intro θ T' h
    rw [h]
    refine ⟨?_, ?_⟩
    · have h1 := geneScore_ad_bc_self_sub θ.1 θ.2
      linarith
    · have h1 := geneScore_ad_bc_self_sub θ.1 θ.2
      have h2 := geneScore_ab_cd_eq_ac_bd_of_shape_ad_bc θ.1 θ.2
      linarith

/-- ★★★ **任意模型 + MSC 的端到端定理 1**（`X = Fin 4`，单个 quartet）。

把 `PropAData`（各模型的命题 A 数据）经 `CASTERTopo.propB_of_bridge` 与
`CASTERTopo.TopoIdeal.ofModel` 插进无根 quartet 拓扑层的引擎，再交给
`CASTERTopo.topo_statisticallyConsistent`：

* `emp n`：第 `n` 个样本的经验平均权重表；
* `hconv`：**大数定律**（作为显式假设，不新增公理）——`emp n` 最终逐点 `ε`-接近理论表 `W`；
* `E n`：在 `emp n` 上最大化 CASTER 得分的选择；
* 结论：最终 `E n` 把唯一的 quartet 判成真拓扑 `ab|cd`。

（`hNE`（存在非真选择）对 `X = Fin 4` 由 `fun _ _ => .ac_bd` 显式给出，故不必作为假设。） -/
theorem propAData_caster_statisticallyConsistent {Θ : Type*} [MeasurableSpace Θ]
    (S : MSCTopoSym Θ) (ν : Measure Θ) [IsProbabilityMeasure ν]
    (hdeep : MeasurableSet {θ | S.deep θ}) (P : PropAData Θ)
    (hf_int : Integrable P.f ν) (hf_pos : ∀ θ, ¬ S.deep θ → 0 < P.f θ)
    (hpos : 0 < ν {θ | ¬ S.deep θ})
    (hint : ∀ T : Topo, Integrable (fun θ => ∑ T' : Topo, S.τd θ T' * P.A θ T' T) ν)
    (emp : ℕ → TopoWeight (Fin 4))
    (hconv : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N,
      TopoClose (emp n) (TopoIdeal.ofModel S ν hdeep P hf_int hf_pos hpos hint).W ε)
    {E : ℕ → TopoChoice (Fin 4)}
    (hE : ∀ (n : ℕ) (q : TopoChoice (Fin 4)),
      topoScore (emp n) q ≤ topoScore (emp n) (E n)) :
    ∃ N : ℕ, ∀ n ≥ N, IsTrueT (fun _ _ => Topo.ab_cd) (E n) := by
  have hNE : ∃ q : TopoChoice (Fin 4), ¬ IsTrueT (fun _ _ => Topo.ab_cd) q := by
    refine ⟨fun _ _ => Topo.ac_bd, fun hcontra => ?_⟩
    have hcard : (Finset.univ : Finset (Fin 4)).card = 4 := by decide
    have hbad : (Topo.ac_bd : Topo) = Topo.ab_cd := hcontra Finset.univ hcard
    exact absurd hbad (by decide)
  exact topo_statisticallyConsistent
    (TopoIdeal.ofModel S ν hdeep P hf_int hf_pos hpos hint) emp hconv hNE hE

/-- ★★★ **JC69 的 CASTER 定理 1（端到端）**：把 `jc69PropAData` 插进上面的接口。

时间参数取 `(Fin 4 → ℝ) × ℝ`（叶长 × 内部枝长），其余假设逐条显式列出：

* `hdeep` / `hpos`：MSC 侧（「无深合并有正概率」是 Kingman 溯祖的直接推论，此处**显式假设**）；
* `hf_int` / `hf_pos`：幅度可积且（无深合并时）为正；
* `hint`：三个拓扑的期望权重可积（对应正文定理 1 的条件 (2)「权重一致有界」）；
* `hconv`：大数定律（**显式假设**）。 -/
theorem jc69_caster_statisticallyConsistent
    (S : MSCTopoSym ((Fin 4 → ℝ) × ℝ)) (ν : Measure ((Fin 4 → ℝ) × ℝ)) [IsProbabilityMeasure ν]
    (hdeep : MeasurableSet {θ | S.deep θ}) (hpos : 0 < ν {θ | ¬ S.deep θ})
    (hf_int : Integrable jc69PropAData.f ν)
    (hf_pos : ∀ θ, ¬ S.deep θ → 0 < jc69PropAData.f θ)
    (hint : ∀ T : Topo, Integrable (fun θ => ∑ T' : Topo, S.τd θ T' * jc69PropAData.A θ T' T) ν)
    (emp : ℕ → TopoWeight (Fin 4))
    (hconv : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N,
      TopoClose (emp n)
        (TopoIdeal.ofModel S ν hdeep jc69PropAData hf_int hf_pos hpos hint).W ε)
    {E : ℕ → TopoChoice (Fin 4)}
    (hE : ∀ (n : ℕ) (q : TopoChoice (Fin 4)),
      topoScore (emp n) q ≤ topoScore (emp n) (E n)) :
    ∃ N : ℕ, ∀ n ≥ N, IsTrueT (fun _ _ => Topo.ab_cd) (E n) :=
  propAData_caster_statisticallyConsistent S ν hdeep jc69PropAData hf_int hf_pos hpos hint
    emp hconv hE

end Phylo.Stat.CASTERGeneTree
