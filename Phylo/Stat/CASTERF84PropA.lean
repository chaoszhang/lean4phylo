/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.Stat.CASTERF84Events
import Phylo.Stat.CASTERF84Scaffold
import Phylo.Stat.CASTERBridge
import Phylo.Stat.CASTERGeneTree

/-!
# `Phylo.Stat.CASTERF84PropA` —— F84 的**命题 A 数据**（agent B，条件形式）

文献：Zhang, Nielsen, Mirarab (2025), *Science* **387**(6737) eadk9688，
附录 `sm.tex` 1601（`λ` 闭式）与 1585（印的常数）。

## 这一环补的是什么

```
Phylo.Stat.CASTERF84Events   Ew（对角分组）/ EwA（{a,c}/{b,d}）/ EwB（{a,d}/{b,c}）
Phylo.Stat.CASTERBridge      PropAData（命题 A 数据）与抽象引擎
Phylo.Stat.CASTERGeneTree    jc69PropAData + 端到端定理 1 的写法
        ▲
        └── 本文件：把 F84 的**九格权重表**打包成 `PropAData`
```

## 两种形式（条件 / 无条件）

三条核恒等式

```
(D)  Ew  pi kap lam t1 t2 lx t3 t4 = C
(XA) EwA pi kap lam t1 t2 lx t3 t4 = 0
(XB) EwB pi kap lam t1 t2 lx t3 t4 = 0
C := 2·π_A·π_C·π_G·π_T·π_R·π_Y·(1 − sm lam lx)·rm(λ,κ,t1)·rm(λ,κ,t2)·rm(λ,κ,t3)·rm(λ,κ,t4)
```

已由 ★★★ `Phylo.Stat.CASTERF84Scaffold.Ew_diag` / `EwA_zero` / `EwB_zero` **无条件证完**
（零 `sorry` / 零 `axiom`）。本文件据此给两种打包：

* **条件形式** `f84PropAData_of` / `f84_caster_statisticallyConsistent_of`：把三条恒等式收成
  显式假设 `hD / hA / hB`，因此**不依赖**脚手架那一支即可落地（保留，供分层复核与复用）；
* **无条件形式** `f84PropAData` / `f84_caster_statisticallyConsistent`（见 §5）：
  `π, κ` 退为**参数**，样本空间取「叶长 × 内部枝长」`(Fin 4 → ℝ) × ℝ`，
  三条恒等式由脚手架直接供给 ⇒ **F84 的 CASTER 定理 1 端到端无条件成立**。

**九格权重表**（`T'` = 基因树形状、`τ` = 被评拓扑；`l` 是按 `a,b,c,d` 的**自然**叶长）：

| `T'` \ `τ` | `ab_cd` | `ac_bd` | `ad_bc` |
|---|---|---|---|
| `ab_cd` | `Ew  l0 l1 lx l2 l3` | `EwA l0 l1 lx l2 l3` | `EwB l0 l1 lx l2 l3` |
| `ac_bd` | `EwA l0 l2 lx l1 l3` | `Ew  l0 l2 lx l1 l3` | `EwB l0 l2 lx l1 l3` |
| `ad_bc` | `EwA l0 l3 lx l1 l2` | `EwB l0 l3 lx l1 l2` | `Ew  l0 l3 lx l1 l2` |

对角格是「基因树的姐妹叶恰好是 `τ` 的两侧」（同一内部结点对），故用 `Ew`；
非对角格的两个侧都**横跨** `p,q`，故用 `EwA`/`EwB`。

由 (D)/(XA)/(XB) 立即得到 `E[w(τ) | 基因树 T'] = C·[τ = T']` —— **两个错拓扑的期望权重恰为 0**。

本文件含 ★★★ `f84Weight_eq`、★★★ `f84PropAData_of`、★★★ `f84_caster_statisticallyConsistent_of`、
★★★ `f84Weight_eq_uncond`、★★★ `f84PropAData`、★★★ `f84_caster_statisticallyConsistent`；
不含 `sorry` / `axiom` / `import Mathlib`。
-/

noncomputable section

set_option maxHeartbeats 1600000

namespace Phylo.Stat.CASTERF84PropA

open Phylo.CASTERF84
open Phylo.Stat.CASTERF84Events
open Phylo.Stat.CASTERWeights
open Phylo.Stat.CASTEREngine
open Phylo.Stat.CASTERTopo
open Phylo.Stat.CASTERBridge
open Phylo.Stat.CASTERGeneTree
open MeasureTheory

/-! ## 1. 模型参数与印的常数 -/

/-- **附录 1601 的率因子闭式**（F84）：
`λ = π_Rπ_Y / ((1 − Σπ_i²)π_Rπ_Y + 2κ(π_Aπ_Gπ_Y + π_Cπ_Tπ_R))`。 -/
def lamF84 (pi : Fin 4 → ℝ) (kap : ℝ) : ℝ :=
  piR pi * piY pi
    / ((1 - (pi 0 ^ 2 + pi 1 ^ 2 + pi 2 ^ 2 + pi 3 ^ 2)) * piR pi * piY pi
        + 2 * kap * (pi 0 * pi 1 * piY pi + pi 2 * pi 3 * piR pi))

/-- **幅度中与形状无关的因子**：`2·π_Aπ_Cπ_Gπ_T·π_Rπ_Y·(1 − sm lam lx)`。 -/
def f84Amp (pi : Fin 4 → ℝ) (lam lx : ℝ) : ℝ :=
  2 * pi 0 * pi 2 * pi 1 * pi 3 * piR pi * piY pi * (1 - sm lam lx)

/-- ★★ **附录 1585 印的常数** `C`（÷4 口径）：
`2·π_Aπ_Cπ_Gπ_T·π_Rπ_Y·(1 − sm lam lx)·∏ᵢ rm(λ,κ,lᵢ)`。 -/
def f84Const (pi : Fin 4 → ℝ) (kap lam lx : ℝ) (l : Fin 4 → ℝ) : ℝ :=
  f84Amp pi lam lx
    * (rm lam kap (l 0) * rm lam kap (l 1) * rm lam kap (l 2) * rm lam kap (l 3))

/-! ## 2. 九格权重表 -/

/-- ★★ **F84 的九格权重表** `f84Weight pi kap lam l lx T' τ`：
基因树形状 `T'`（叶长 `l`、内部枝长 `lx`）上，被评拓扑 `τ` 的期望权重。

对角格用 `Ew`（同结点分组），非对角格用 `EwA`/`EwB`（跨结点分组）。 -/
def f84Weight (pi : Fin 4 → ℝ) (kap lam : ℝ) (l : Fin 4 → ℝ) (lx : ℝ) :
    Topo → Topo → ℝ
  | .ab_cd, .ab_cd => Ew pi kap lam (l 0) (l 1) lx (l 2) (l 3)
  | .ab_cd, .ac_bd => EwA pi kap lam (l 0) (l 1) lx (l 2) (l 3)
  | .ab_cd, .ad_bc => EwB pi kap lam (l 0) (l 1) lx (l 2) (l 3)
  | .ac_bd, .ab_cd => EwA pi kap lam (l 0) (l 2) lx (l 1) (l 3)
  | .ac_bd, .ac_bd => Ew pi kap lam (l 0) (l 2) lx (l 1) (l 3)
  | .ac_bd, .ad_bc => EwB pi kap lam (l 0) (l 2) lx (l 1) (l 3)
  | .ad_bc, .ab_cd => EwA pi kap lam (l 0) (l 3) lx (l 1) (l 2)
  | .ad_bc, .ac_bd => EwB pi kap lam (l 0) (l 3) lx (l 1) (l 2)
  | .ad_bc, .ad_bc => Ew pi kap lam (l 0) (l 3) lx (l 1) (l 2)

/-- ★★★ **条件形式的九格定理**：在 (D)/(XA)/(XB) 三条恒等式下，
`f84Weight` 恰是「对角 = 常数、非对角 = 0」。

（三条假设按**任意四个长度**给出，以便对角格的叶长重排（`Ew l0 l2 lx l1 l3` 等）
直接代入；`f84Const` 的四项 `rm` 乘积由 `ring` 重排。） -/
theorem f84Weight_eq (pi : Fin 4 → ℝ) (kap lam : ℝ) (l : Fin 4 → ℝ) (lx : ℝ)
    (hD : ∀ a b c d : ℝ, Ew pi kap lam a b lx c d
      = f84Amp pi lam lx * (rm lam kap a * rm lam kap b * rm lam kap c * rm lam kap d))
    (hA : ∀ a b c d : ℝ, EwA pi kap lam a b lx c d = 0)
    (hB : ∀ a b c d : ℝ, EwB pi kap lam a b lx c d = 0) :
    ∀ T' τ : Topo, f84Weight pi kap lam l lx T' τ
      = if T' = τ then f84Const pi kap lam lx l else 0 := by
  intro T' τ
  by_cases h : T' = τ
  · subst h
    rw [ite_eq_left rfl]
    cases T' <;> simp only [f84Weight] <;> rw [f84Const, hD] <;> ring
  · rw [ite_eq_right h]
    cases T' <;> cases τ <;> simp only [f84Weight]
    · exact absurd rfl h
    · exact hA _ _ _ _
    · exact hB _ _ _ _
    · exact hA _ _ _ _
    · exact absurd rfl h
    · exact hB _ _ _ _
    · exact hA _ _ _ _
    · exact hB _ _ _ _
    · exact absurd rfl h

/-- ★★ **对角格**：`f84Weight` 在 `T' = τ` 时给印的常数。 -/
theorem f84Weight_self (pi : Fin 4 → ℝ) (kap lam : ℝ) (l : Fin 4 → ℝ) (lx : ℝ)
    (hD : ∀ a b c d : ℝ, Ew pi kap lam a b lx c d
      = f84Amp pi lam lx * (rm lam kap a * rm lam kap b * rm lam kap c * rm lam kap d))
    (hA : ∀ a b c d : ℝ, EwA pi kap lam a b lx c d = 0)
    (hB : ∀ a b c d : ℝ, EwB pi kap lam a b lx c d = 0) (T : Topo) :
    f84Weight pi kap lam l lx T T = f84Const pi kap lam lx l := by
  rw [f84Weight_eq pi kap lam l lx hD hA hB T T, ite_eq_left rfl]

/-- ★★ **非对角格**：`f84Weight` 在 `T' ≠ τ` 时给 `0`。 -/
theorem f84Weight_ne (pi : Fin 4 → ℝ) (kap lam : ℝ) (l : Fin 4 → ℝ) (lx : ℝ)
    (hD : ∀ a b c d : ℝ, Ew pi kap lam a b lx c d
      = f84Amp pi lam lx * (rm lam kap a * rm lam kap b * rm lam kap c * rm lam kap d))
    (hA : ∀ a b c d : ℝ, EwA pi kap lam a b lx c d = 0)
    (hB : ∀ a b c d : ℝ, EwB pi kap lam a b lx c d = 0)
    (T' τ : Topo) (h : T' ≠ τ) :
    f84Weight pi kap lam l lx T' τ = 0 := by
  rw [f84Weight_eq pi kap lam l lx hD hA hB T' τ, ite_eq_right h]

/-! ## 3. 命题 A 数据 -/

/-- 时间 / 参数层：`θ = ((叶长, 内部枝长), (π, κ))`。
（`π` 与 `κ` 进入样本空间，因为三条恒等式的假设是关于具体 `π,κ` 说的。） -/
abbrev F84Theta : Type := ((Fin 4 → ℝ) × ℝ) × ((Fin 4 → ℝ) × ℝ)

/-- `θ` 处的期望权重表（= `f84Weight` 用 `θ` 里的模型参数与枝长实例化）。 -/
noncomputable def f84A (θ : F84Theta) (T' τ : Topo) : ℝ :=
  f84Weight θ.2.1 θ.2.2 (lamF84 θ.2.1 θ.2.2) θ.1.1 θ.1.2 T' τ

/-- `θ` 处的幅度（= `f84Const` 用 `θ` 里的参数实例化）。 -/
noncomputable def f84F (θ : F84Theta) : ℝ :=
  f84Const θ.2.1 θ.2.2 (lamF84 θ.2.1 θ.2.2) θ.1.2 θ.1.1

/-- ★★★ **F84 的命题 A 数据**（条件形式：三条核恒等式作为假设）。

* `A θ T' τ = f84Weight …`：形状 `T'` 的基因树上拓扑 `τ` 的期望权重；
* `f θ = f84Const …`：**与形状无关**的幅度；
* 三条子句：由 ★★★ `f84Weight_eq` 立即给出（对角格 = 幅度、非对角格 = `0`）。 -/
noncomputable def f84PropAData_of
    (hD : ∀ (θ : F84Theta) (a b c d : ℝ),
      Ew θ.2.1 θ.2.2 (lamF84 θ.2.1 θ.2.2) a b θ.1.2 c d
        = f84Amp θ.2.1 (lamF84 θ.2.1 θ.2.2) θ.1.2
          * (rm (lamF84 θ.2.1 θ.2.2) θ.2.2 a * rm (lamF84 θ.2.1 θ.2.2) θ.2.2 b
            * rm (lamF84 θ.2.1 θ.2.2) θ.2.2 c * rm (lamF84 θ.2.1 θ.2.2) θ.2.2 d))
    (hA : ∀ (θ : F84Theta) (a b c d : ℝ),
      EwA θ.2.1 θ.2.2 (lamF84 θ.2.1 θ.2.2) a b θ.1.2 c d = 0)
    (hB : ∀ (θ : F84Theta) (a b c d : ℝ),
      EwB θ.2.1 θ.2.2 (lamF84 θ.2.1 θ.2.2) a b θ.1.2 c d = 0) :
    PropAData F84Theta where
  A := f84A
  f := f84F
  clause_ab := by
    intro θ T' hT
    subst hT
    simp only [f84A, f84F]
    have hs := f84Weight_self θ.2.1 θ.2.2 (lamF84 θ.2.1 θ.2.2) θ.1.1 θ.1.2
      (hD θ) (hA θ) (hB θ) .ab_cd
    have h1 := f84Weight_ne θ.2.1 θ.2.2 (lamF84 θ.2.1 θ.2.2) θ.1.1 θ.1.2
      (hD θ) (hA θ) (hB θ) .ab_cd .ac_bd (by decide)
    have h2 := f84Weight_ne θ.2.1 θ.2.2 (lamF84 θ.2.1 θ.2.2) θ.1.1 θ.1.2
      (hD θ) (hA θ) (hB θ) .ab_cd .ad_bc (by decide)
    rw [hs, h1, h2]
    exact ⟨sub_self _, sub_self _⟩
  clause_ac := by
    intro θ T' hT
    subst hT
    simp only [f84A, f84F]
    have hs := f84Weight_self θ.2.1 θ.2.2 (lamF84 θ.2.1 θ.2.2) θ.1.1 θ.1.2
      (hD θ) (hA θ) (hB θ) .ac_bd
    have h1 := f84Weight_ne θ.2.1 θ.2.2 (lamF84 θ.2.1 θ.2.2) θ.1.1 θ.1.2
      (hD θ) (hA θ) (hB θ) .ac_bd .ab_cd (by decide)
    have h2 := f84Weight_ne θ.2.1 θ.2.2 (lamF84 θ.2.1 θ.2.2) θ.1.1 θ.1.2
      (hD θ) (hA θ) (hB θ) .ac_bd .ad_bc (by decide)
    rw [hs, h1, h2]
    exact ⟨sub_self _, sub_self _⟩
  clause_ad := by
    intro θ T' hT
    subst hT
    simp only [f84A, f84F]
    have hs := f84Weight_self θ.2.1 θ.2.2 (lamF84 θ.2.1 θ.2.2) θ.1.1 θ.1.2
      (hD θ) (hA θ) (hB θ) .ad_bc
    have h1 := f84Weight_ne θ.2.1 θ.2.2 (lamF84 θ.2.1 θ.2.2) θ.1.1 θ.1.2
      (hD θ) (hA θ) (hB θ) .ad_bc .ab_cd (by decide)
    have h2 := f84Weight_ne θ.2.1 θ.2.2 (lamF84 θ.2.1 θ.2.2) θ.1.1 θ.1.2
      (hD θ) (hA θ) (hB θ) .ad_bc .ac_bd (by decide)
    rw [hs, h1, h2]
    exact ⟨sub_self _, sub_self _⟩

/-! ## 4. 端到端定理 1（F84） -/

/-- ★★★ **F84 的 CASTER 定理 1（端到端，条件形式）**：把 `f84PropAData_of` 插进引擎。

时间层取 `F84Theta = ((叶长, 内部枝长), (π, κ))`，其余假设逐条显式列出
（与 `Phylo.Stat.CASTERGeneTree.jc69_caster_statisticallyConsistent` 逐字同形）：

* `hD / hA / hB`：三条核恒等式（由 `Phylo.Stat.CASTERF84Scaffold` 供给）；
* `hdeep` / `hpos`：MSC 侧（「无深合并有正概率」，显式假设）；
* `hf_int` / `hf_pos`：幅度可积且（无深合并时）为正；
* `hint`：三个拓扑的期望权重可积（对应正文定理 1 的条件 (2)「权重一致有界」）；
* `hconv`：大数定律（显式假设）。

结论：最终 `E n` 把唯一的 quartet 判成真拓扑 `ab|cd`。 -/
theorem f84_caster_statisticallyConsistent_of
    (hD : ∀ (θ : F84Theta) (a b c d : ℝ),
      Ew θ.2.1 θ.2.2 (lamF84 θ.2.1 θ.2.2) a b θ.1.2 c d
        = f84Amp θ.2.1 (lamF84 θ.2.1 θ.2.2) θ.1.2
          * (rm (lamF84 θ.2.1 θ.2.2) θ.2.2 a * rm (lamF84 θ.2.1 θ.2.2) θ.2.2 b
            * rm (lamF84 θ.2.1 θ.2.2) θ.2.2 c * rm (lamF84 θ.2.1 θ.2.2) θ.2.2 d))
    (hA : ∀ (θ : F84Theta) (a b c d : ℝ),
      EwA θ.2.1 θ.2.2 (lamF84 θ.2.1 θ.2.2) a b θ.1.2 c d = 0)
    (hB : ∀ (θ : F84Theta) (a b c d : ℝ),
      EwB θ.2.1 θ.2.2 (lamF84 θ.2.1 θ.2.2) a b θ.1.2 c d = 0)
    (S : MSCTopoSym F84Theta) (ν : Measure F84Theta) [IsProbabilityMeasure ν]
    (hdeep : MeasurableSet {θ | S.deep θ}) (hpos : 0 < ν {θ | ¬ S.deep θ})
    (hf_int : Integrable (f84PropAData_of hD hA hB).f ν)
    (hf_pos : ∀ θ, ¬ S.deep θ → 0 < (f84PropAData_of hD hA hB).f θ)
    (hint : ∀ T : Topo, Integrable
      (fun θ => ∑ T' : Topo, S.τd θ T' * (f84PropAData_of hD hA hB).A θ T' T) ν)
    (emp : ℕ → TopoWeight (Fin 4))
    (hconv : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N,
      TopoClose (emp n)
        (TopoIdeal.ofModel S ν hdeep (f84PropAData_of hD hA hB) hf_int hf_pos hpos hint).W ε)
    {E : ℕ → TopoChoice (Fin 4)}
    (hE : ∀ (n : ℕ) (q : TopoChoice (Fin 4)),
      topoScore (emp n) q ≤ topoScore (emp n) (E n)) :
    ∃ N : ℕ, ∀ n ≥ N, IsTrueT (fun _ _ => Topo.ab_cd) (E n) :=
  propAData_caster_statisticallyConsistent S ν hdeep (f84PropAData_of hD hA hB)
    hf_int hf_pos hpos hint emp hconv hE

/-! ## 5. 无条件形式（由 `Phylo.Stat.CASTERF84Scaffold` 供给）

`π, κ` 从样本空间退为**参数**，样本空间只剩「叶长 × 内部枝长」`(Fin 4 → ℝ) × ℝ`；
三条核恒等式 (D)/(XA)/(XB) 由 ★★★ `Ew_diag` / `EwA_zero` / `EwB_zero` 无条件给出，
于是本节的 `f84PropAData` 与 `f84_caster_statisticallyConsistent` **不含任何核恒等式假设**。 -/

open Phylo.Stat.CASTERF84Scaffold (Ew_diag EwA_zero EwB_zero)

/-- ★★ **无条件版 (D)**：把 ★★★ `Ew_diag` 重排成 `f84Amp · ∏rm` 的形状（即 `hD` 的形状）。 -/
theorem f84Ew_eq (pi : Fin 4 → ℝ) (kap : ℝ) (hR : piR pi ≠ 0) (hY : piY pi ≠ 0) (lx : ℝ) :
    ∀ a b c d : ℝ, Ew pi kap (lamF84 pi kap) a b lx c d
      = f84Amp pi (lamF84 pi kap) lx
        * (rm (lamF84 pi kap) kap a * rm (lamF84 pi kap) kap b
          * rm (lamF84 pi kap) kap c * rm (lamF84 pi kap) kap d) := by
  intro a b c d
  rw [Ew_diag pi hR hY kap (lamF84 pi kap) a b lx c d]
  simp only [f84Amp]

/-- ★★ **无条件版 (XA)**：跨结点分组 `ac|bd` 的期望权重恒为 `0`。 -/
theorem f84EwA_eq (pi : Fin 4 → ℝ) (kap : ℝ) (hR : piR pi ≠ 0) (hY : piY pi ≠ 0) (lx : ℝ) :
    ∀ a b c d : ℝ, EwA pi kap (lamF84 pi kap) a b lx c d = 0 :=
  fun a b c d => EwA_zero pi hR hY kap (lamF84 pi kap) a b lx c d

/-- ★★ **无条件版 (XB)**：跨结点分组 `ad|bc` 的期望权重恒为 `0`。 -/
theorem f84EwB_eq (pi : Fin 4 → ℝ) (kap : ℝ) (hR : piR pi ≠ 0) (hY : piY pi ≠ 0) (lx : ℝ) :
    ∀ a b c d : ℝ, EwB pi kap (lamF84 pi kap) a b lx c d = 0 :=
  fun a b c d => EwB_zero pi hR hY kap (lamF84 pi kap) a b lx c d

/-- ★★★ **F84 九格定理（无条件）**：`π, κ` 固定为参数时，`f84Weight` 恰是
「对角 = 印的常数、非对角 = `0`」。 -/
theorem f84Weight_eq_uncond (pi : Fin 4 → ℝ) (kap : ℝ) (hR : piR pi ≠ 0) (hY : piY pi ≠ 0)
    (l : Fin 4 → ℝ) (lx : ℝ) :
    ∀ T' τ : Topo, f84Weight pi kap (lamF84 pi kap) l lx T' τ
      = if T' = τ then f84Const pi kap (lamF84 pi kap) lx l else 0 :=
  f84Weight_eq pi kap (lamF84 pi kap) l lx
    (f84Ew_eq pi kap hR hY lx) (f84EwA_eq pi kap hR hY lx) (f84EwB_eq pi kap hR hY lx)

/-- ★★ **对角格（无条件）**：`f84Weight` 在 `T' = τ` 时给印的常数。 -/
theorem f84Weight_self_uncond (pi : Fin 4 → ℝ) (kap : ℝ) (hR : piR pi ≠ 0) (hY : piY pi ≠ 0)
    (l : Fin 4 → ℝ) (lx : ℝ) (T : Topo) :
    f84Weight pi kap (lamF84 pi kap) l lx T T = f84Const pi kap (lamF84 pi kap) lx l := by
  rw [f84Weight_eq_uncond pi kap hR hY l lx T T, ite_eq_left rfl]

/-- ★★ **非对角格（无条件）**：`f84Weight` 在 `T' ≠ τ` 时给 `0`。 -/
theorem f84Weight_ne_uncond (pi : Fin 4 → ℝ) (kap : ℝ) (hR : piR pi ≠ 0) (hY : piY pi ≠ 0)
    (l : Fin 4 → ℝ) (lx : ℝ) (T' τ : Topo) (h : T' ≠ τ) :
    f84Weight pi kap (lamF84 pi kap) l lx T' τ = 0 := by
  rw [f84Weight_eq_uncond pi kap hR hY l lx T' τ, ite_eq_right h]

/-- 无条件形式的期望权重表（`π, κ` 是参数，`θ` 只含枝长）。 -/
noncomputable def f84A_uncond (pi : Fin 4 → ℝ) (kap : ℝ) (θ : (Fin 4 → ℝ) × ℝ)
    (T' τ : Topo) : ℝ :=
  f84Weight pi kap (lamF84 pi kap) θ.1 θ.2 T' τ

/-- 无条件形式的幅度。 -/
noncomputable def f84F_uncond (pi : Fin 4 → ℝ) (kap : ℝ) (θ : (Fin 4 → ℝ) × ℝ) : ℝ :=
  f84Const pi kap (lamF84 pi kap) θ.2 θ.1

/-- ★★★ **F84 的命题 A 数据（无条件）**：样本空间 = 「叶长 × 内部枝长」`(Fin 4 → ℝ) × ℝ`，
`π, κ` 退回为参数（故 `hR : π_R ≠ 0`、`hY : π_Y ≠ 0` 是对**参数**的非退化假设，
而不是对样本点的逐点要求）。三条子句由 ★★★ `f84Weight_eq_uncond` 立即给出。 -/
noncomputable def f84PropAData (pi : Fin 4 → ℝ) (kap : ℝ)
    (hR : piR pi ≠ 0) (hY : piY pi ≠ 0) : PropAData ((Fin 4 → ℝ) × ℝ) where
  A := f84A_uncond pi kap
  f := f84F_uncond pi kap
  clause_ab := by
    intro θ T' hT
    subst hT
    simp only [f84A_uncond, f84F_uncond]
    have hs := f84Weight_self_uncond pi kap hR hY θ.1 θ.2 .ab_cd
    have h1 := f84Weight_ne_uncond pi kap hR hY θ.1 θ.2 .ab_cd .ac_bd (by decide)
    have h2 := f84Weight_ne_uncond pi kap hR hY θ.1 θ.2 .ab_cd .ad_bc (by decide)
    rw [hs, h1, h2]
    exact ⟨sub_self _, sub_self _⟩
  clause_ac := by
    intro θ T' hT
    subst hT
    simp only [f84A_uncond, f84F_uncond]
    have hs := f84Weight_self_uncond pi kap hR hY θ.1 θ.2 .ac_bd
    have h1 := f84Weight_ne_uncond pi kap hR hY θ.1 θ.2 .ac_bd .ab_cd (by decide)
    have h2 := f84Weight_ne_uncond pi kap hR hY θ.1 θ.2 .ac_bd .ad_bc (by decide)
    rw [hs, h1, h2]
    exact ⟨sub_self _, sub_self _⟩
  clause_ad := by
    intro θ T' hT
    subst hT
    simp only [f84A_uncond, f84F_uncond]
    have hs := f84Weight_self_uncond pi kap hR hY θ.1 θ.2 .ad_bc
    have h1 := f84Weight_ne_uncond pi kap hR hY θ.1 θ.2 .ad_bc .ab_cd (by decide)
    have h2 := f84Weight_ne_uncond pi kap hR hY θ.1 θ.2 .ad_bc .ac_bd (by decide)
    rw [hs, h1, h2]
    exact ⟨sub_self _, sub_self _⟩

/-- ★★★ **F84 的 CASTER 定理 1（端到端，无条件）**：三条核恒等式**不再作为假设**，
由 `Phylo.Stat.CASTERF84Scaffold` 的 ★★★ `Ew_diag` / `EwA_zero` / `EwB_zero` 直接供给；
其余假设与 `f84_caster_statisticallyConsistent_of` 逐条同形
（`hdeep`/`hpos` MSC 侧、`hf_int`/`hf_pos` 幅度、`hint` 正文条件 (2)、`hconv` 大数定律）。 -/
theorem f84_caster_statisticallyConsistent
    (pi : Fin 4 → ℝ) (kap : ℝ) (hR : piR pi ≠ 0) (hY : piY pi ≠ 0)
    (S : MSCTopoSym ((Fin 4 → ℝ) × ℝ)) (ν : Measure ((Fin 4 → ℝ) × ℝ)) [IsProbabilityMeasure ν]
    (hdeep : MeasurableSet {θ | S.deep θ}) (hpos : 0 < ν {θ | ¬ S.deep θ})
    (hf_int : Integrable (f84PropAData pi kap hR hY).f ν)
    (hf_pos : ∀ θ, ¬ S.deep θ → 0 < (f84PropAData pi kap hR hY).f θ)
    (hint : ∀ T : Topo, Integrable
      (fun θ => ∑ T' : Topo, S.τd θ T' * (f84PropAData pi kap hR hY).A θ T' T) ν)
    (emp : ℕ → TopoWeight (Fin 4))
    (hconv : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N,
      TopoClose (emp n)
        (TopoIdeal.ofModel S ν hdeep (f84PropAData pi kap hR hY) hf_int hf_pos hpos hint).W ε)
    {E : ℕ → TopoChoice (Fin 4)}
    (hE : ∀ (n : ℕ) (q : TopoChoice (Fin 4)),
      topoScore (emp n) q ≤ topoScore (emp n) (E n)) :
    ∃ N : ℕ, ∀ n ≥ N, IsTrueT (fun _ _ => Topo.ab_cd) (E n) :=
  propAData_caster_statisticallyConsistent S ν hdeep (f84PropAData pi kap hR hY)
    hf_int hf_pos hpos hint emp hconv hE

end Phylo.Stat.CASTERF84PropA
