/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.Stat.CASTERJC69
import Phylo.Stat.CASTEREngine
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

## 诚实边界

* 本文件只做 **JC69**（附录 Fig. 1C）。F84 / LM1 的 `PropA` 实例不在本批范围
  （见 `Phylo.Stat.CASTERWeights` 的「诚实边界」）。
* `jc69PropA` 只断言**命题 A**（基因树层）；「命题 A ⇒ 命题 B」在
  `Phylo.Stat.CASTEREngine` 里，模型无关。「`ν{无深合并} > 0`」这一条 MSC 假设
  在 `MSCTopoSym` 那一层，与本文件无关。
* 本文件不含 `sorry` / `axiom` / `import Mathlib`，`#print axioms` 只出现
  `propext`、`Classical.choice`、`Quot.sound`。
-/

noncomputable section

namespace Phylo.Stat.CASTERGeneTree

open Phylo.Stat.CASTERWeights
open Phylo.CASTERJC69
open Phylo.JC
open Phylo.Stat.CASTEREngine

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

end Phylo.Stat.CASTERGeneTree
