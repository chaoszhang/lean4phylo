/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.Stat.CASTERWeights

/-!
# `Phylo.Stat.CASTERt` —— CASTER 四点统计量 `t`：三值性 · 对称 · 三条判据（W44/W45 · L1）

文献：`references/CASTER_NJ_2026-11-04.md` §2（定义 1/2、定理 1/2、推论 1）。
配方见 `W45_L1_recipe.md`（协调侧实跑）。

## 口径（★D 两处，都是 W45 实测推翻我先前判断的）

1. **`w` 用文档 Definition 1 的对称表，不用库内 `wJCBase`**。
   两张表**不是同一个函数**：文档对「恰 3 种字母」**一律**给 `−1/2`，而 `wJCBase` 只对两种朝向给；
   且 `wJC T σ` 还依赖拓扑。把 `wJCBase` 代进文档的 `t` 公式，**三值性是假命题**
   （W45 实测：256 个模式里 **96** 个不满足）。
   ⇒ 本文件用 `wSym`（文档表，放大 2 倍的整数版）。
2. **枚举姿势**：用 `∀ σ : Fin 4 → Fin 4, … := by decide` ＋ `set_option maxRecDepth 100000`，
   **不要** `fin_cases` 后 `simp`、也**不要**自造 `vec4_*` 投影引理
   （`σ` 在 `decide` 里是具体元素，`σ 0` 是 `rfl` 级归约）。
3. **值域放 `ℤ`**（放大 2/4 倍）：`ℚ`/`ℝ` 上 `decide` 会在 `Rat.num` 上停住（库内文件头有记）。

## 交付

| # | 定理 | 内容 |
|---|---|---|
| L1.1 | `t4_trichotomy` | `t ∈ {1, −1/2, 0}` ⟺ `4t ∈ {4, −2, 0}` |
| L1.1′ | `counts` | 12 / 24 / 220（文档 §2.3 数值表的定理版） |
| L1.2 | `t4_symm` | 两侧对调不变（文档定理 2） |
| L1.3 | `t4_eq_four_iff` / `t4_eq_neg_two_iff` / `t4_eq_zero_iff` | 推论 1 三条 |
-/

set_option maxRecDepth 100000

namespace Phylo.Stat.CASTERt

open Phylo.Stat.CASTERWeights

/-- 交换位置 `1,2`（`σ₁₂`）。 -/
def sw12 : Equiv.Perm (Fin 4) := Equiv.swap 1 2

/-- 交换位置 `1,3`（`σ₁₃`，文档 §2.2 的 `(s0,s3,s2,s1)`）。 -/
def sw13 : Equiv.Perm (Fin 4) := Equiv.swap 1 3

/-- **文档 Definition 1 的 CASTER 权重**，放大 2 倍的整数版：
2|2 匹配（`s0=s1 ∧ s2=s3 ∧ s0≠s2`）⇒ `2`；恰 3 种字母 ⇒ `-1`；其余 ⇒ `0`。
（对应原值 `+1`、`−1/2`、`0`。） -/
def wSym (b : Fin 4 → Fin 4) : ℤ :=
  if b 0 = b 1 ∧ b 2 = b 3 ∧ b 0 ≠ b 2 then 2
  else if (Finset.univ.image b).card = 3 then -1
  else 0

/-- **`4·t`**：由 `t = w − ½(w₁₂ + w₁₃)` 与 `W = 2w` 得 `4t = 2·W − W₁₂ − W₁₃`。 -/
def t4 (σ : Fin 4 → Fin 4) : ℤ :=
  2 * wSym σ - wSym (fun i => σ (sw12 i)) - wSym (fun i => σ (sw13 i))

/-! ## L1.1 三值性（文档定理 1） -/

/-- ★★ **L1.1**：`t` 只取 `1`、`−1/2`、`0`（等价地 `4t ∈ {4, −2, 0}`）。 -/
theorem t4_trichotomy : ∀ σ : Fin 4 → Fin 4, t4 σ = 4 ∨ t4 σ = -2 ∨ t4 σ = 0 := by
  decide

/-- ★★ **L1.1′**（文档 §2.3 的数值表，升成定理）：`t = 1` 有 **12** 个模式、
`t = −1/2` 有 **24** 个、`t = 0` 有 **220** 个，合计 256。 -/
theorem counts :
    ((Finset.univ : Finset (Fin 4 → Fin 4)).filter (fun σ => t4 σ = 4)).card = 12
    ∧ ((Finset.univ : Finset (Fin 4 → Fin 4)).filter (fun σ => t4 σ = -2)).card = 24
    ∧ ((Finset.univ : Finset (Fin 4 → Fin 4)).filter (fun σ => t4 σ = 0)).card = 220 := by
  decide

/-! ## L1.2 两侧对称（文档定理 2） -/

/-- ★★ **L1.2**：把两侧对调（`(0 2)(1 3)`）不改变 `t`。 -/
theorem t4_symm : ∀ σ : Fin 4 → Fin 4,
    t4 (fun i => σ (Phylo.Stat.CASTERWeights.sidesPerm i)) = t4 σ := by
  decide

/-! ## L1.3 三条判据（文档推论 1） -/

/-- ★★ **L1.3a**：`t = 1` ⟺ 位点支持 `01|23`。 -/
theorem t4_eq_four_iff : ∀ σ : Fin 4 → Fin 4,
    (t4 σ = 4 ↔ (σ 0 = σ 1 ∧ σ 2 = σ 3 ∧ σ 0 ≠ σ 2)) := by
  decide

/-- ★★ **L1.3b**：`t = −1/2` ⟺ 位点支持 `02|13` 或 `03|12`。

（文档 §2.4 该行写成「1-1、3-1 或 4-1 型」是**笔误**：那三类给 `t = 0`；派单 §3.4 已指出。） -/
theorem t4_eq_neg_two_iff : ∀ σ : Fin 4 → Fin 4,
    (t4 σ = -2 ↔
      (σ 0 = σ 2 ∧ σ 1 = σ 3 ∧ σ 0 ≠ σ 1) ∨ (σ 0 = σ 3 ∧ σ 1 = σ 2 ∧ σ 0 ≠ σ 1)) := by
  decide

/-- ★★ **L1.3c**：`t = 0` ⟺ 位点**无信息**（不属于另外两类 `2|2`）。 -/
theorem t4_eq_zero_iff : ∀ σ : Fin 4 → Fin 4,
    (t4 σ = 0 ↔
      ¬ (σ 0 = σ 1 ∧ σ 2 = σ 3 ∧ σ 0 ≠ σ 2) ∧
        ¬ ((σ 0 = σ 2 ∧ σ 1 = σ 3 ∧ σ 0 ≠ σ 1) ∨
            (σ 0 = σ 3 ∧ σ 1 = σ 2 ∧ σ 0 ≠ σ 1))) := by
  decide

end Phylo.Stat.CASTERt
