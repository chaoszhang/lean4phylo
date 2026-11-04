/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.Stat.CASTERtL1

/-!
# `Phylo.Stat.CASTERD` —— CASTER 的 `D` 与归一化 `D̃`（W44 · L3）

文献：`references/CASTER_NJ_2026-11-04.md` §4。

```lean
D tval a b      := (Σ_{c ≠ a,b} Σ_{d ≠ a,b,c} tval a b c d) / 2      -- 无序 2-子集，除 2 去重
Dtilde tval W a b := D tval a b / (W a * W b)
```

## L3 的内容（文档定理 4）

在 A1–A3 下 `E[t(ab|cd)] = α·W_a W_b W_c W_d·f(I)·ε`，故把 `W_a W_b` 提出求和后除回去：

```text
D̃_ab 的分子 = (W_a W_b) · Σ_{c<d} W_c W_d · (α f ε)   ⇒   D̃_ab = α Σ_{c<d} W_c W_d f ε
```

本文件把这条写成**纯代数**（无概率论）：只要有 `0 < W a`、`0 < W b`，
把逐项分解 `α W_a W_b W_c W_d f = (W_a W_b)·(α W_c W_d f)` 提出来即可。

★ 口径：这里**不引入任何额外归一化**（文档 §4.2 明确说不要 `R = Σ W_cW_d` 之类）。
-/

noncomputable section

namespace Phylo.Stat.CASTERD

open Finset

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- `S ∖ {a, b}`。 -/
def rest (a b : X) : Finset X := Finset.univ \ {a, b}

/-- **`D_ab`**：`t(ab|cd)` 在 `c<d ⊆ S∖{a,b}` 上的和（用有序对求和再除 2 实现「无序」）。 -/
def D (tval : X → X → X → X → ℝ) (a b : X) : ℝ :=
  (∑ c ∈ rest a b, ∑ d ∈ rest a b \ {c}, tval a b c d) / 2

/-- **归一化 `D̃_ab = D_ab / (W_a W_b)`**。 -/
def Dtilde (tval : X → X → X → X → ℝ) (W : X → ℝ) (a b : X) : ℝ :=
  D tval a b / (W a * W b)

/-- ★★ **L3（文档定理 4，代数核）**：若逐项 `E t(ab|cd) = α·W_a W_b W_c W_d·f c d`
（`f` 吸收了 `ε` 与内部枝长的函数），则

```text
(Σ_{c<d} α W_a W_b W_c W_d f) / (W_a W_b) = α · Σ_{c<d} W_c W_d f .
```

即「`D̃` 把两端的叶权 `W_a W_b` 约掉」。 -/
theorem Dtilde_eq (W : X → ℝ) (ha : W a ≠ 0) (hb : W b ≠ 0)
    (α : ℝ) (f : X → X → ℝ) :
    (∑ c ∈ rest a b, ∑ d ∈ rest a b \ {c}, α * W a * W b * W c * W d * f c d) / (W a * W b)
      = α * ∑ c ∈ rest a b, ∑ d ∈ rest a b \ {c}, W c * W d * f c d := by
  have hfac : ∀ c d : X, α * W a * W b * W c * W d * f c d
      = (W a * W b) * (α * W c * W d * f c d) := by
    intro c d; ring
  simp only [hfac, Finset.mul_sum]
  field_simp
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  ring

end Phylo.Stat.CASTERD
