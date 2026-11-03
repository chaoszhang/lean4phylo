/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.Stat.MassMajorizes
import Phylo.SplitWeak

/-!
# `Phylo.Stat.AnchorGap` —— **S5：Δ 等价桥**（`μ = mass_A − mass_B`）

## 这一层做什么

`references/FOUR_POINT_2026-11-03.md` §1.1 的 `μ`（带符号的四点内枝长）与 §3 的 `mass`
（锚间距）在**单棵树**上是**同一个量的两种写法**：

```text
μ(xy|zw) := (d(x,z) + d(y,w) − d(x,y) − d(z,w)) / 2
mass(q)  := Σ_{s ∈ F 在 {x,y,z,w} 上诱导出 q} w s
⇒ μ(xy|zw) = mass(xy|zw) − mass(xz|yw)
```

于是「**argmax mass**」与「**Δ 的符号**」是同一件事 —— 这就是派单 §5 的 S5。

## 走的是 split 度量路线（不是 105 拓扑 ＋ 偏导）

`d = Σ w_s · SplitMetric_s`。两侧都是 `w` 的**线性泛函** ⇒ 只需对**单个 split** 验证；
而单个 split 的行为完全由 4 个点的隶属模式决定 ⇒ **16 个模式**（派单说 64 是 6 点版，
这里只需要 4 点 ⇒ 16）。逐模式 `by_cases` ＋ `simp`/`norm_num` 即可，
**不需要** 105 拓扑、分段线性、偏导、连续性。

## 诚实边界

* 本文件只做**四点层**的桥（`μ = mass_A − mass_B` ⇒ 符号一致）。文档 A3 的 `n` 点通式
  `Δ = C(n−1,2)·μ` **未做**（要靠 `D(a,b)` 双和记账，与 `BunyanIndexBridge` 的 A2/A3 同一量级）。
* 单 split 的 16 模式用 `by_cases` 展开，**不是** `decide`（`x ∈ s.sideA` 不是可计算命题）。
* 「至多一个非零」（相容性）那条在 `MassMajorizes.mass_majorizes` 里已证；本文件的
  `mu_pos_iff` 只把「符号」翻译过去，不重复用它。
-/

noncomputable section

open Finset

namespace Phylo.Stat.AnchorGap

open Split

universe u

variable {X : Type u} [Fintype X] [DecidableEq X]

/-! ## 1. `s` 把 `{x,y,z,u}` 分成 `xy|zu` -/

/-- `s` 在四点集上诱导出配对 `xy|zu`（2|2，**无向**）。

`abbrev` 而不是 `def`：否则 `if Sep s x y z u then …` 在**陈述层**拿不到 `Decidable` 实例
（`def` 是半可约的，实例搜索不展开它）。 -/
abbrev Sep (s : Split X) (x y z u : X) : Prop :=
  (x ∈ s.sideA ∧ y ∈ s.sideA ∧ z ∈ s.sideB ∧ u ∈ s.sideB) ∨
  (x ∈ s.sideB ∧ y ∈ s.sideB ∧ z ∈ s.sideA ∧ u ∈ s.sideA)

/-- 四点上的**锚间距**（`mass` 的 split 级写法，与 `MassMajorizes.mass` 同一口径）。 -/
def mass4 (F : Finset (Split X)) (wt : Split X → ℝ) (x y z u : X) : ℝ := by
  classical
  exact ∑ s ∈ F, wt s * (if Sep s x y z u then 1 else 0)

/-- `sumMetric` 的写法：`d(x,y) = Σ_s w_s · SplitMetric_s(x,y)`。 -/
def dmet (F : Finset (Split X)) (wt : Split X → ℝ) (x y : X) : ℝ :=
  ∑ s ∈ F, wt s * SplitMetric s x y

/-! ## 2. 单 split 的恒等式（16 个隶属模式） -/

/-- ★★ **单 split 的核心恒等式**：把 `SplitMetric s` 代入 `μ` 与 `mass`，两边恰好相等。

证明：对四点的四个隶属位 `by_cases` 展开，`SplitMetric` 与 `Sep` 都退化成 `0/1`，逐情形 `norm_num`。 -/
theorem split_identity (s : Split X) (x y z u : X) :
    (SplitMetric s x z + SplitMetric s y u - SplitMetric s x y - SplitMetric s z u) / 2
      = (if Sep s x y z u then 1 else 0) - (if Sep s x z y u then 1 else 0) := by
  classical
  by_cases hx : x ∈ s.sideA <;> by_cases hy : y ∈ s.sideA <;>
    by_cases hz : z ∈ s.sideA <;> by_cases hu : u ∈ s.sideA <;>
    simp [SplitMetric, Sep, Split.sideB_eq_sdiff, hx, hy, hz, hu] <;> norm_num

/-! ## 3. 求和层：`μ = mass_A − mass_B` -/

/-- ★★★★ **S5 的主命题**：`μ(xy|zu) = mass(xy|zu) − mass(xz|yu)`。

两侧都是 `wt` 的线性泛函，故由 §2 的单 split 恒等式逐项相加得到。 -/
theorem mu_eq_mass_sub (F : Finset (Split X)) (wt : Split X → ℝ) (x y z u : X) :
    (dmet F wt x z + dmet F wt y u - dmet F wt x y - dmet F wt z u) / 2
      = mass4 F wt x y z u - mass4 F wt x z y u := by
  classical
  have hterm : ∀ s ∈ F,
      wt s * ((SplitMetric s x z + SplitMetric s y u - SplitMetric s x y
        - SplitMetric s z u) / 2)
        = wt s * (if Sep s x y z u then 1 else 0)
          - wt s * (if Sep s x z y u then 1 else 0) := by
    intro s _
    rw [split_identity s x y z u]
    ring
  have hsum : (dmet F wt x z + dmet F wt y u - dmet F wt x y - dmet F wt z u) / 2
      = ∑ s ∈ F, wt s * ((SplitMetric s x z + SplitMetric s y u - SplitMetric s x y
          - SplitMetric s z u) / 2) := by
    simp only [dmet]
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
      Finset.sum_div]
    exact Finset.sum_congr rfl fun s _ => by ring
  rw [hsum, Finset.sum_congr rfl hterm, Finset.sum_sub_distrib]
  simp only [mass4]

/-- ★★ **等价桥的符号形态**：`μ(xy|zu) > 0 ⟺ mass(xy|zu) > mass(xz|yu)`。

「argmax mass」与「Δ 的符号」因此是同一件事（`Δ` 与 `μ` 只差一个**正常数**：
`Δ = C(n−1,2)·μ`，文档 §3.3；四点层 `n = 4` 时系数 `3/2` 也是正的 ⇒ 符号相同）。 -/
theorem mu_pos_iff (F : Finset (Split X)) (wt : Split X → ℝ) (x y z u : X) :
    0 < (dmet F wt x z + dmet F wt y u - dmet F wt x y - dmet F wt z u) / 2
      ↔ mass4 F wt x y z u > mass4 F wt x z y u := by
  rw [mu_eq_mass_sub F wt x y z u]
  constructor <;> intro h <;> linarith

end Phylo.Stat.AnchorGap
