/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.Stat.CASTERFourPoint4

/-!
# `Phylo.Stat.CASTERFourPointN` —— `n ≥ 5` 的四点不等式（W44/W46 · L4.2）

文献：`references/CASTER_NJ_2026-11-04.md` §5.3（定理 6）· 派单：`W44_TO_DSH_prompt.txt` §3.2。

## 我选路线 A，但 `g(P) ≥ 0` 的依据比「分情形穷尽」强

派单的路线 A 把 `Δ` 写成 `Δ = Σ_P W_c W_d · g(P)` 并断言 `g(P) ≥ 0`（协调侧数值）；
路线 B 是文档原稿的双计数表，文档自己写了「完整双计数我尚未逐格写完」且第 2、3 行带 `?`。
**选 A**（B 要先把表重算完，且 A 的 `g` 有下表的闭合形式）。

本文件不走「有限枚举」，而是用**一条**结构事实把全部 11 类一次压掉：

> `{x,y}`、`{z,w}` **严格是樱桃** ⇒ 任何同时含 `x,y` 的四点按 `xy|·` 分裂。

于是 `ε(xy|pq) = 1`（所有 `p,q ∉ {x,y}`）、`ε(zw|pq) = 1`（所有 `p,q ∉ {z,w}`）
——`Δ` 的**两个正项逐项取到最大值 `+1`**，两个负项只要 `ε ≤ 1` 就压得住：

| `P ∩ Q` | `g(P)` | `≥ 0` 的依据 |
|---|---|---|
| `∅` | `c·(2 − ε(xz|P) − ε(yw|P))` | 两个 `ε ≤ 1` |
| 恰 1 个 | `c·(1 − ε(·|P))` | `ε ≤ 1` |
| `{x,y}`、`{z,w}` | `c` | 另一樱桃 ⇒ `ε = 1` |
| `{x,z}`、`{y,w}` | `c/2` | **恰一性**：`xy|zw` 已占 `+1` ⇒ 另两项 `−1/2` |
| `{x,w}`、`{y,z}` | `0` | 四项都不激活 |

严格性：`g({x,y}) = g({z,w}) = c ⇒ Δ ≥ α c (W_x W_y + W_z W_w) > 0`。

## 分情形穷尽清单（派单 §3.2 ③）

`P = {p,q}`（无序）相对 `Q = {x,y,z,w}` 的位置只有
`P ∩ Q ∈ {∅, {x}, {y}, {z}, {w}, {x,y}, {x,z}, {x,w}, {y,z}, {y,w}, {z,w}}` —— **11 类**，
上表 5 行**恰好**是这 11 类（`∅` / 恰 1 个的 4 种 / 含 2 个的 6 种）。
代码里用 `cases_four`（`a = x ∨ a = y ∨ a = z ∨ a = w ∨ a ∉ Q`）对 `p`、`q` 各五分支，
共 `5 × 5 = 25` 个位置、扣掉 5 个 `p = q`，**20 个非平凡分支**；`P ∩ Q` 含 2 个的两处
例外（`{x,z}`、`{y,w}`）单列，用「恰一性」（`casterEps_ne_of_lt`）算成 `c/2`。

## 实测（W46，`.w46/gcheck.py`，精确有理数）

`n = 6` 的**全部 105 棵**带标号二叉无根树 × 全部 `(x,y,z,w)` 有序四元组 × 全部 `P`
（**189000** 次检查）：`g(P) ≥ 0` **无例外**，值域 `{0, ½, 1, 3/2, 3}`，
`g({x,y}) = g({z,w}) = 1` 恒成立。分 `|P ∩ Q|`：`0 → {0, 3/2, 3}`、`1 → {0, 3/2}`、
`2 → {0, ½, 1}`，与上表逐行吻合。

## 诚实边界

* `ε` 由**树距离的严格四点判据**定义（`casterEps`）；`{x,y}`/`{z,w}` 的**严格樱桃性**
  作为显式假设 `hcx`/`hcz` 传入。它由「实现树二叉 ＋ 边权全正」供给
  （`Cladogram.dist_add_le_of_isCherry`（`Phylo/CherryQuartet.lean:131`）是**非严格**版，
  严格版还需二叉性：度 ≥ 4 的顶点让 quartet 退化）。**本文件不证「二叉 ⇒ 严格」这一条**。
* **不用** A3 的单一指数形式；`α` 是 A3 的常数，`c` 是 A4 的常数（`f ≡ c`）。
* `n = 4` 的特例在 `Phylo/Stat/CASTERFourPoint4.lean`（`casterDelta4` / `fourPoint_n4_eq`）；
  本文件的 `casterDeltaN` 在 `n ≥ 5` 时多出的项全部 `≥ 0`，是它的推广。
-/

noncomputable section

namespace Phylo.Stat.CASTERFourPoint

open Finset

variable {X : Type*} [Fintype X] [DecidableEq X]

/-! ## 1. 四点符号 `ε`（文档 A3 的 `ε_{ab|cd}`） -/

/-- **CASTER 的四点符号**：`ab|cd` 是四点三和中的**严格最小** ⇒ `+1`，否则 `−½`。 -/
noncomputable def casterEps (dl : X → X → ℝ) (a b c d : X) : ℝ :=
  if dl a b + dl c d < dl a c + dl b d ∧ dl a b + dl c d < dl a d + dl b c then 1
  else -(1 / 2)

theorem casterEps_of_lt (dl : X → X → ℝ) (a b c d : X)
    (h1 : dl a b + dl c d < dl a c + dl b d) (h2 : dl a b + dl c d < dl a d + dl b c) :
    casterEps dl a b c d = 1 := by
  unfold casterEps
  rw [if_pos ⟨h1, h2⟩]

theorem casterEps_le_one (dl : X → X → ℝ) (a b c d : X) : casterEps dl a b c d ≤ 1 := by
  unfold casterEps
  split_ifs <;> norm_num

theorem casterEps_ge_neg_half (dl : X → X → ℝ) (a b c d : X) :
    -(1 / 2) ≤ casterEps dl a b c d := by
  unfold casterEps
  split_ifs <;> norm_num

/-- **恰一性**：若 `ab|cd` 严格最小，则 `ac|bd` 取 `−½`。 -/
theorem casterEps_ne_of_lt (dl : X → X → ℝ) (a b c d : X)
    (h : dl a b + dl c d < dl a c + dl b d) : casterEps dl a c b d = -(1 / 2) := by
  unfold casterEps
  rw [if_neg]
  intro hc
  linarith [hc.1]

theorem casterEps_swap12 (dl : X → X → ℝ) (hsym : ∀ a b, dl a b = dl b a) (a b c d : X) :
    casterEps dl a b c d = casterEps dl b a c d := by
  unfold casterEps
  have key : (dl b a + dl c d < dl b c + dl a d ∧ dl b a + dl c d < dl b d + dl a c)
      ↔ (dl a b + dl c d < dl a c + dl b d ∧ dl a b + dl c d < dl a d + dl b c) := by
    rw [hsym b a]
    constructor <;> intro h <;> exact ⟨by linarith [h.2], by linarith [h.1]⟩
  by_cases h : (dl a b + dl c d < dl a c + dl b d ∧ dl a b + dl c d < dl a d + dl b c)
  · rw [if_pos h, if_pos (key.mpr h)]
  · rw [if_neg h, if_neg (fun h' => h (key.mp h'))]

theorem casterEps_swap34 (dl : X → X → ℝ) (hsym : ∀ a b, dl a b = dl b a) (a b c d : X) :
    casterEps dl a b c d = casterEps dl a b d c := by
  unfold casterEps
  have key : (dl a b + dl d c < dl a d + dl b c ∧ dl a b + dl d c < dl a c + dl b d)
      ↔ (dl a b + dl c d < dl a c + dl b d ∧ dl a b + dl c d < dl a d + dl b c) := by
    rw [hsym c d]
    exact and_comm
  by_cases h : (dl a b + dl c d < dl a c + dl b d ∧ dl a b + dl c d < dl a d + dl b c)
  · rw [if_pos h, if_pos (key.mpr h)]
  · rw [if_neg h, if_neg (fun h' => h (key.mp h'))]

theorem casterEps_swapSides (dl : X → X → ℝ) (hsym : ∀ a b, dl a b = dl b a) (a b c d : X) :
    casterEps dl a b c d = casterEps dl c d a b := by
  unfold casterEps
  have key : (dl c d + dl a b < dl c a + dl d b ∧ dl c d + dl a b < dl c b + dl d a)
      ↔ (dl a b + dl c d < dl a c + dl b d ∧ dl a b + dl c d < dl a d + dl b c) := by
    rw [hsym c a, hsym d b, hsym c b, hsym d a]
    constructor <;> intro h <;> exact ⟨by linarith [h.1], by linarith [h.2]⟩
  by_cases h : (dl a b + dl c d < dl a c + dl b d ∧ dl a b + dl c d < dl a d + dl b c)
  · rw [if_pos h, if_pos (key.mpr h)]
  · rw [if_neg h, if_neg (fun h' => h (key.mp h'))]

/-- 一个元素相对四个特殊点的**五分类**（`casterG` 的分情形穷尽用）。 -/
theorem cases_four (a x y z w : X) :
    a = x ∨ a = y ∨ a = z ∨ a = w ∨ (a ≠ x ∧ a ≠ y ∧ a ≠ z ∧ a ≠ w) := by
  by_cases h1 : a = x
  · exact Or.inl h1
  · by_cases h2 : a = y
    · exact Or.inr (Or.inl h2)
    · by_cases h3 : a = z
      · exact Or.inr (Or.inr (Or.inl h3))
      · by_cases h4 : a = w
        · exact Or.inr (Or.inr (Or.inr (Or.inl h4)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨h1, h2, h3, h4⟩)))

/-! ## 2. 逐项系数 `g(P)` 与 `Δ` -/

/-- **`g(P)` 的 `c` 倍**（有序对 `(p,q)`）：`c·[xy|·]ε + c·[zw|·]ε − c·[xz|·]ε − c·[yw|·]ε`；
方括号 = 「`p,q` 都不在该侧」的指示，缺项记 `0`（文档 §3.2 路线 A 的 `g(P)`）。 -/
noncomputable def casterG (dl : X → X → ℝ) (c : ℝ) (x y z w p q : X) : ℝ :=
  (if p ≠ x ∧ p ≠ y ∧ q ≠ x ∧ q ≠ y ∧ p ≠ q then c * casterEps dl x y p q else 0)
    + (if p ≠ z ∧ p ≠ w ∧ q ≠ z ∧ q ≠ w ∧ p ≠ q then c * casterEps dl z w p q else 0)
    - (if p ≠ x ∧ p ≠ z ∧ q ≠ x ∧ q ≠ z ∧ p ≠ q then c * casterEps dl x z p q else 0)
    - (if p ≠ y ∧ p ≠ w ∧ q ≠ y ∧ q ≠ w ∧ p ≠ q then c * casterEps dl y w p q else 0)

/-- ★★★ **路线 A 的核心：`g(P) ≥ 0` 逐点成立**（`p = q` 时 `g = 0`）。

依据见文件头：`{x,y}`、`{z,w}` 严格是樱桃 ⇒ 两个正项的 `ε` 恒为 `1`，
负项用 `ε ≤ 1`；唯一的例外 `{x,z}`、`{y,w}` 由**恰一性**算成 `c/2`。 -/
theorem casterG_nonneg (dl : X → X → ℝ) (hsym : ∀ a b, dl a b = dl b a)
    {x y z w : X} (hxy : x ≠ y) (hxz : x ≠ z) (hxw : x ≠ w)
    (hyz : y ≠ z) (hyw : y ≠ w) (hzw : z ≠ w)
    (hcx : ∀ p q : X, p ≠ q → p ≠ x → p ≠ y → q ≠ x → q ≠ y →
      dl x y + dl p q < dl x p + dl y q ∧ dl x y + dl p q < dl x q + dl y p)
    (hcz : ∀ p q : X, p ≠ q → p ≠ z → p ≠ w → q ≠ z → q ≠ w →
      dl z w + dl p q < dl z p + dl w q ∧ dl z w + dl p q < dl z q + dl w p)
    (c : ℝ) (hc : 0 ≤ c) (p q : X) :
    0 ≤ casterG dl c x y z w p q := by
  have hxy' : y ≠ x := hxy.symm
  have hxz' : z ≠ x := hxz.symm
  have hxw' : w ≠ x := hxw.symm
  have hyz' : z ≠ y := hyz.symm
  have hyw' : w ≠ y := hyw.symm
  have hzw' : w ≠ z := hzw.symm
  have exy : ∀ p q : X, p ≠ q → p ≠ x → p ≠ y → q ≠ x → q ≠ y →
      casterEps dl x y p q = 1 :=
    fun p q h1 h2 h3 h4 h5 =>
      casterEps_of_lt dl x y p q (hcx p q h1 h2 h3 h4 h5).1 (hcx p q h1 h2 h3 h4 h5).2
  have ezw : ∀ p q : X, p ≠ q → p ≠ z → p ≠ w → q ≠ z → q ≠ w →
      casterEps dl z w p q = 1 :=
    fun p q h1 h2 h3 h4 h5 =>
      casterEps_of_lt dl z w p q (hcz p q h1 h2 h3 h4 h5).1 (hcz p q h1 h2 h3 h4 h5).2
  have exz_yw : casterEps dl x z y w = -(1 / 2) :=
    casterEps_ne_of_lt dl x y z w (hcx z w hzw hxz.symm hyz.symm hxw.symm hyw.symm).1
  have exz_wy : casterEps dl x z w y = -(1 / 2) := by
    rw [casterEps_swap34 dl hsym x z w y]; exact exz_yw
  have eyw_xz : casterEps dl y w x z = -(1 / 2) := by
    rw [← casterEps_swapSides dl hsym x z y w]; exact exz_yw
  have eyw_zx : casterEps dl y w z x = -(1 / 2) := by
    rw [← casterEps_swapSides dl hsym z x y w, casterEps_swap12 dl hsym z x y w]; exact exz_yw
  by_cases hpq : p = q
  · rw [hpq] at ⊢
    simp [casterG]
  · -- `p ≠ q`：按 `p`、`q` 各落在 `x/y/z/w/其余` 做分情形
    rcases cases_four p x y z w with hpc | hpc | hpc | hpc | ⟨hpx, hpy, hpz, hpw⟩
    · -- p = x
      rw [hpc] at hpq ⊢
      rcases cases_four q x y z w with hqc | hqc | hqc | hqc | ⟨hqx, hqy, hqz, hqw⟩
      · rw [hqc] at hpq; exact absurd rfl hpq
      · -- p = x, q = y
        rw [hqc] at hpq ⊢
        have i1 : ¬ (x ≠ x ∧ x ≠ y ∧ y ≠ x ∧ y ≠ y ∧ x ≠ y) := by simp
        have i2 : x ≠ z ∧ x ≠ w ∧ y ≠ z ∧ y ≠ w ∧ x ≠ y := by simp [*]
        have i3 : ¬ (x ≠ x ∧ x ≠ z ∧ y ≠ x ∧ y ≠ z ∧ x ≠ y) := by simp
        have i4 : ¬ (x ≠ y ∧ x ≠ w ∧ y ≠ y ∧ y ≠ w ∧ x ≠ y) := by simp
        have e2 : casterEps dl z w x y = 1 := ezw x y (by simp [*]) (by simp [*]) (by simp [*]) (by simp [*]) (by simp [*])
        simp only [casterG, if_neg i1, if_pos i2, if_neg i3, if_neg i4]
        rw [e2]
        nlinarith
      · -- p = x, q = z
        rw [hqc] at hpq ⊢
        have i1 : ¬ (x ≠ x ∧ x ≠ y ∧ z ≠ x ∧ z ≠ y ∧ x ≠ z) := by simp
        have i2 : ¬ (x ≠ z ∧ x ≠ w ∧ z ≠ z ∧ z ≠ w ∧ x ≠ z) := by simp
        have i3 : ¬ (x ≠ x ∧ x ≠ z ∧ z ≠ x ∧ z ≠ z ∧ x ≠ z) := by simp
        have i4 : x ≠ y ∧ x ≠ w ∧ z ≠ y ∧ z ≠ w ∧ x ≠ z := by simp [*]
        have ebad : casterEps dl y w x z = -(1 / 2) := eyw_xz
        simp only [casterG, if_neg i1, if_neg i2, if_neg i3, if_pos i4]
        rw [ebad]
        nlinarith
      · -- p = x, q = w
        rw [hqc] at hpq ⊢
        have i1 : ¬ (x ≠ x ∧ x ≠ y ∧ w ≠ x ∧ w ≠ y ∧ x ≠ w) := by simp
        have i2 : ¬ (x ≠ z ∧ x ≠ w ∧ w ≠ z ∧ w ≠ w ∧ x ≠ w) := by simp
        have i3 : ¬ (x ≠ x ∧ x ≠ z ∧ w ≠ x ∧ w ≠ z ∧ x ≠ w) := by simp
        have i4 : ¬ (x ≠ y ∧ x ≠ w ∧ w ≠ y ∧ w ≠ w ∧ x ≠ w) := by simp
        simp only [casterG, if_neg i1, if_neg i2, if_neg i3, if_neg i4]
        nlinarith
      · -- p = x, q = q
        have i1 : ¬ (x ≠ x ∧ x ≠ y ∧ q ≠ x ∧ q ≠ y ∧ x ≠ q) := by simp
        have i2 : x ≠ z ∧ x ≠ w ∧ q ≠ z ∧ q ≠ w ∧ x ≠ q := by simp [*]
        have i3 : ¬ (x ≠ x ∧ x ≠ z ∧ q ≠ x ∧ q ≠ z ∧ x ≠ q) := by simp
        have i4 : x ≠ y ∧ x ≠ w ∧ q ≠ y ∧ q ≠ w ∧ x ≠ q := by simp [*]
        have e2 : casterEps dl z w x q = 1 := ezw x q (by simp [*]) (by simp [*]) (by simp [*]) (by simp [*]) (by simp [*])
        simp only [casterG, if_neg i1, if_pos i2, if_neg i3, if_pos i4]
        rw [e2]
        nlinarith [mul_le_mul_of_nonneg_left (casterEps_le_one dl y w x q) hc]
    · -- p = y
      rw [hpc] at hpq ⊢
      rcases cases_four q x y z w with hqc | hqc | hqc | hqc | ⟨hqx, hqy, hqz, hqw⟩
      · -- p = y, q = x
        rw [hqc] at hpq ⊢
        have i1 : ¬ (y ≠ x ∧ y ≠ y ∧ x ≠ x ∧ x ≠ y ∧ y ≠ x) := by simp
        have i2 : y ≠ z ∧ y ≠ w ∧ x ≠ z ∧ x ≠ w ∧ y ≠ x := by simp [*]
        have i3 : ¬ (y ≠ x ∧ y ≠ z ∧ x ≠ x ∧ x ≠ z ∧ y ≠ x) := by simp
        have i4 : ¬ (y ≠ y ∧ y ≠ w ∧ x ≠ y ∧ x ≠ w ∧ y ≠ x) := by simp
        have e2 : casterEps dl z w y x = 1 := ezw y x (by simp [*]) (by simp [*]) (by simp [*]) (by simp [*]) (by simp [*])
        simp only [casterG, if_neg i1, if_pos i2, if_neg i3, if_neg i4]
        rw [e2]
        nlinarith
      · rw [hqc] at hpq; exact absurd rfl hpq
      · -- p = y, q = z
        rw [hqc] at hpq ⊢
        have i1 : ¬ (y ≠ x ∧ y ≠ y ∧ z ≠ x ∧ z ≠ y ∧ y ≠ z) := by simp
        have i2 : ¬ (y ≠ z ∧ y ≠ w ∧ z ≠ z ∧ z ≠ w ∧ y ≠ z) := by simp
        have i3 : ¬ (y ≠ x ∧ y ≠ z ∧ z ≠ x ∧ z ≠ z ∧ y ≠ z) := by simp
        have i4 : ¬ (y ≠ y ∧ y ≠ w ∧ z ≠ y ∧ z ≠ w ∧ y ≠ z) := by simp
        simp only [casterG, if_neg i1, if_neg i2, if_neg i3, if_neg i4]
        nlinarith
      · -- p = y, q = w
        rw [hqc] at hpq ⊢
        have i1 : ¬ (y ≠ x ∧ y ≠ y ∧ w ≠ x ∧ w ≠ y ∧ y ≠ w) := by simp
        have i2 : ¬ (y ≠ z ∧ y ≠ w ∧ w ≠ z ∧ w ≠ w ∧ y ≠ w) := by simp
        have i3 : y ≠ x ∧ y ≠ z ∧ w ≠ x ∧ w ≠ z ∧ y ≠ w := by simp [*]
        have i4 : ¬ (y ≠ y ∧ y ≠ w ∧ w ≠ y ∧ w ≠ w ∧ y ≠ w) := by simp
        have ebad : casterEps dl x z y w = -(1 / 2) := exz_yw
        simp only [casterG, if_neg i1, if_neg i2, if_pos i3, if_neg i4]
        rw [ebad]
        nlinarith
      · -- p = y, q = q
        have i1 : ¬ (y ≠ x ∧ y ≠ y ∧ q ≠ x ∧ q ≠ y ∧ y ≠ q) := by simp
        have i2 : y ≠ z ∧ y ≠ w ∧ q ≠ z ∧ q ≠ w ∧ y ≠ q := by simp [*]
        have i3 : y ≠ x ∧ y ≠ z ∧ q ≠ x ∧ q ≠ z ∧ y ≠ q := by simp [*]
        have i4 : ¬ (y ≠ y ∧ y ≠ w ∧ q ≠ y ∧ q ≠ w ∧ y ≠ q) := by simp
        have e2 : casterEps dl z w y q = 1 := ezw y q (by simp [*]) (by simp [*]) (by simp [*]) (by simp [*]) (by simp [*])
        simp only [casterG, if_neg i1, if_pos i2, if_pos i3, if_neg i4]
        rw [e2]
        nlinarith [mul_le_mul_of_nonneg_left (casterEps_le_one dl x z y q) hc]
    · -- p = z
      rw [hpc] at hpq ⊢
      rcases cases_four q x y z w with hqc | hqc | hqc | hqc | ⟨hqx, hqy, hqz, hqw⟩
      · -- p = z, q = x
        rw [hqc] at hpq ⊢
        have i1 : ¬ (z ≠ x ∧ z ≠ y ∧ x ≠ x ∧ x ≠ y ∧ z ≠ x) := by simp
        have i2 : ¬ (z ≠ z ∧ z ≠ w ∧ x ≠ z ∧ x ≠ w ∧ z ≠ x) := by simp
        have i3 : ¬ (z ≠ x ∧ z ≠ z ∧ x ≠ x ∧ x ≠ z ∧ z ≠ x) := by simp
        have i4 : z ≠ y ∧ z ≠ w ∧ x ≠ y ∧ x ≠ w ∧ z ≠ x := by simp [*]
        have ebad : casterEps dl y w z x = -(1 / 2) := eyw_zx
        simp only [casterG, if_neg i1, if_neg i2, if_neg i3, if_pos i4]
        rw [ebad]
        nlinarith
      · -- p = z, q = y
        rw [hqc] at hpq ⊢
        have i1 : ¬ (z ≠ x ∧ z ≠ y ∧ y ≠ x ∧ y ≠ y ∧ z ≠ y) := by simp
        have i2 : ¬ (z ≠ z ∧ z ≠ w ∧ y ≠ z ∧ y ≠ w ∧ z ≠ y) := by simp
        have i3 : ¬ (z ≠ x ∧ z ≠ z ∧ y ≠ x ∧ y ≠ z ∧ z ≠ y) := by simp
        have i4 : ¬ (z ≠ y ∧ z ≠ w ∧ y ≠ y ∧ y ≠ w ∧ z ≠ y) := by simp
        simp only [casterG, if_neg i1, if_neg i2, if_neg i3, if_neg i4]
        nlinarith
      · rw [hqc] at hpq; exact absurd rfl hpq
      · -- p = z, q = w
        rw [hqc] at hpq ⊢
        have i1 : z ≠ x ∧ z ≠ y ∧ w ≠ x ∧ w ≠ y ∧ z ≠ w := by simp [*]
        have i2 : ¬ (z ≠ z ∧ z ≠ w ∧ w ≠ z ∧ w ≠ w ∧ z ≠ w) := by simp
        have i3 : ¬ (z ≠ x ∧ z ≠ z ∧ w ≠ x ∧ w ≠ z ∧ z ≠ w) := by simp
        have i4 : ¬ (z ≠ y ∧ z ≠ w ∧ w ≠ y ∧ w ≠ w ∧ z ≠ w) := by simp
        have e1 : casterEps dl x y z w = 1 := exy z w (by simp [*]) (by simp [*]) (by simp [*]) (by simp [*]) (by simp [*])
        simp only [casterG, if_pos i1, if_neg i2, if_neg i3, if_neg i4]
        rw [e1]
        nlinarith
      · -- p = z, q = q
        have i1 : z ≠ x ∧ z ≠ y ∧ q ≠ x ∧ q ≠ y ∧ z ≠ q := by simp [*]
        have i2 : ¬ (z ≠ z ∧ z ≠ w ∧ q ≠ z ∧ q ≠ w ∧ z ≠ q) := by simp
        have i3 : ¬ (z ≠ x ∧ z ≠ z ∧ q ≠ x ∧ q ≠ z ∧ z ≠ q) := by simp
        have i4 : z ≠ y ∧ z ≠ w ∧ q ≠ y ∧ q ≠ w ∧ z ≠ q := by simp [*]
        have e1 : casterEps dl x y z q = 1 := exy z q (by simp [*]) (by simp [*]) (by simp [*]) (by simp [*]) (by simp [*])
        simp only [casterG, if_pos i1, if_neg i2, if_neg i3, if_pos i4]
        rw [e1]
        nlinarith [mul_le_mul_of_nonneg_left (casterEps_le_one dl y w z q) hc]
    · -- p = w
      rw [hpc] at hpq ⊢
      rcases cases_four q x y z w with hqc | hqc | hqc | hqc | ⟨hqx, hqy, hqz, hqw⟩
      · -- p = w, q = x
        rw [hqc] at hpq ⊢
        have i1 : ¬ (w ≠ x ∧ w ≠ y ∧ x ≠ x ∧ x ≠ y ∧ w ≠ x) := by simp
        have i2 : ¬ (w ≠ z ∧ w ≠ w ∧ x ≠ z ∧ x ≠ w ∧ w ≠ x) := by simp
        have i3 : ¬ (w ≠ x ∧ w ≠ z ∧ x ≠ x ∧ x ≠ z ∧ w ≠ x) := by simp
        have i4 : ¬ (w ≠ y ∧ w ≠ w ∧ x ≠ y ∧ x ≠ w ∧ w ≠ x) := by simp
        simp only [casterG, if_neg i1, if_neg i2, if_neg i3, if_neg i4]
        nlinarith
      · -- p = w, q = y
        rw [hqc] at hpq ⊢
        have i1 : ¬ (w ≠ x ∧ w ≠ y ∧ y ≠ x ∧ y ≠ y ∧ w ≠ y) := by simp
        have i2 : ¬ (w ≠ z ∧ w ≠ w ∧ y ≠ z ∧ y ≠ w ∧ w ≠ y) := by simp
        have i3 : w ≠ x ∧ w ≠ z ∧ y ≠ x ∧ y ≠ z ∧ w ≠ y := by simp [*]
        have i4 : ¬ (w ≠ y ∧ w ≠ w ∧ y ≠ y ∧ y ≠ w ∧ w ≠ y) := by simp
        have ebad : casterEps dl x z w y = -(1 / 2) := exz_wy
        simp only [casterG, if_neg i1, if_neg i2, if_pos i3, if_neg i4]
        rw [ebad]
        nlinarith
      · -- p = w, q = z
        rw [hqc] at hpq ⊢
        have i1 : w ≠ x ∧ w ≠ y ∧ z ≠ x ∧ z ≠ y ∧ w ≠ z := by simp [*]
        have i2 : ¬ (w ≠ z ∧ w ≠ w ∧ z ≠ z ∧ z ≠ w ∧ w ≠ z) := by simp
        have i3 : ¬ (w ≠ x ∧ w ≠ z ∧ z ≠ x ∧ z ≠ z ∧ w ≠ z) := by simp
        have i4 : ¬ (w ≠ y ∧ w ≠ w ∧ z ≠ y ∧ z ≠ w ∧ w ≠ z) := by simp
        have e1 : casterEps dl x y w z = 1 := exy w z (by simp [*]) (by simp [*]) (by simp [*]) (by simp [*]) (by simp [*])
        simp only [casterG, if_pos i1, if_neg i2, if_neg i3, if_neg i4]
        rw [e1]
        nlinarith
      · rw [hqc] at hpq; exact absurd rfl hpq
      · -- p = w, q = q
        have i1 : w ≠ x ∧ w ≠ y ∧ q ≠ x ∧ q ≠ y ∧ w ≠ q := by simp [*]
        have i2 : ¬ (w ≠ z ∧ w ≠ w ∧ q ≠ z ∧ q ≠ w ∧ w ≠ q) := by simp
        have i3 : w ≠ x ∧ w ≠ z ∧ q ≠ x ∧ q ≠ z ∧ w ≠ q := by simp [*]
        have i4 : ¬ (w ≠ y ∧ w ≠ w ∧ q ≠ y ∧ q ≠ w ∧ w ≠ q) := by simp
        have e1 : casterEps dl x y w q = 1 := exy w q (by simp [*]) (by simp [*]) (by simp [*]) (by simp [*]) (by simp [*])
        simp only [casterG, if_pos i1, if_neg i2, if_pos i3, if_neg i4]
        rw [e1]
        nlinarith [mul_le_mul_of_nonneg_left (casterEps_le_one dl x z w q) hc]
    · -- p ∉ Q
      rcases cases_four q x y z w with hqc | hqc | hqc | hqc | ⟨hqx, hqy, hqz, hqw⟩
      · -- p = p, q = x
        rw [hqc] at hpq ⊢
        have i1 : ¬ (p ≠ x ∧ p ≠ y ∧ x ≠ x ∧ x ≠ y ∧ p ≠ x) := by simp
        have i2 : p ≠ z ∧ p ≠ w ∧ x ≠ z ∧ x ≠ w ∧ p ≠ x := by simp [*]
        have i3 : ¬ (p ≠ x ∧ p ≠ z ∧ x ≠ x ∧ x ≠ z ∧ p ≠ x) := by simp
        have i4 : p ≠ y ∧ p ≠ w ∧ x ≠ y ∧ x ≠ w ∧ p ≠ x := by simp [*]
        have e2 : casterEps dl z w p x = 1 := ezw p x (by simp [*]) (by simp [*]) (by simp [*]) (by simp [*]) (by simp [*])
        simp only [casterG, if_neg i1, if_pos i2, if_neg i3, if_pos i4]
        rw [e2]
        nlinarith [mul_le_mul_of_nonneg_left (casterEps_le_one dl y w p x) hc]
      · -- p = p, q = y
        rw [hqc] at hpq ⊢
        have i1 : ¬ (p ≠ x ∧ p ≠ y ∧ y ≠ x ∧ y ≠ y ∧ p ≠ y) := by simp
        have i2 : p ≠ z ∧ p ≠ w ∧ y ≠ z ∧ y ≠ w ∧ p ≠ y := by simp [*]
        have i3 : p ≠ x ∧ p ≠ z ∧ y ≠ x ∧ y ≠ z ∧ p ≠ y := by simp [*]
        have i4 : ¬ (p ≠ y ∧ p ≠ w ∧ y ≠ y ∧ y ≠ w ∧ p ≠ y) := by simp
        have e2 : casterEps dl z w p y = 1 := ezw p y (by simp [*]) (by simp [*]) (by simp [*]) (by simp [*]) (by simp [*])
        simp only [casterG, if_neg i1, if_pos i2, if_pos i3, if_neg i4]
        rw [e2]
        nlinarith [mul_le_mul_of_nonneg_left (casterEps_le_one dl x z p y) hc]
      · -- p = p, q = z
        rw [hqc] at hpq ⊢
        have i1 : p ≠ x ∧ p ≠ y ∧ z ≠ x ∧ z ≠ y ∧ p ≠ z := by simp [*]
        have i2 : ¬ (p ≠ z ∧ p ≠ w ∧ z ≠ z ∧ z ≠ w ∧ p ≠ z) := by simp
        have i3 : ¬ (p ≠ x ∧ p ≠ z ∧ z ≠ x ∧ z ≠ z ∧ p ≠ z) := by simp
        have i4 : p ≠ y ∧ p ≠ w ∧ z ≠ y ∧ z ≠ w ∧ p ≠ z := by simp [*]
        have e1 : casterEps dl x y p z = 1 := exy p z (by simp [*]) (by simp [*]) (by simp [*]) (by simp [*]) (by simp [*])
        simp only [casterG, if_pos i1, if_neg i2, if_neg i3, if_pos i4]
        rw [e1]
        nlinarith [mul_le_mul_of_nonneg_left (casterEps_le_one dl y w p z) hc]
      · -- p = p, q = w
        rw [hqc] at hpq ⊢
        have i1 : p ≠ x ∧ p ≠ y ∧ w ≠ x ∧ w ≠ y ∧ p ≠ w := by simp [*]
        have i2 : ¬ (p ≠ z ∧ p ≠ w ∧ w ≠ z ∧ w ≠ w ∧ p ≠ w) := by simp
        have i3 : p ≠ x ∧ p ≠ z ∧ w ≠ x ∧ w ≠ z ∧ p ≠ w := by simp [*]
        have i4 : ¬ (p ≠ y ∧ p ≠ w ∧ w ≠ y ∧ w ≠ w ∧ p ≠ w) := by simp
        have e1 : casterEps dl x y p w = 1 := exy p w (by simp [*]) (by simp [*]) (by simp [*]) (by simp [*]) (by simp [*])
        simp only [casterG, if_pos i1, if_neg i2, if_pos i3, if_neg i4]
        rw [e1]
        nlinarith [mul_le_mul_of_nonneg_left (casterEps_le_one dl x z p w) hc]
      · -- p = p, q = q
        have i1 : p ≠ x ∧ p ≠ y ∧ q ≠ x ∧ q ≠ y ∧ p ≠ q := by simp [*]
        have i2 : p ≠ z ∧ p ≠ w ∧ q ≠ z ∧ q ≠ w ∧ p ≠ q := by simp [*]
        have i3 : p ≠ x ∧ p ≠ z ∧ q ≠ x ∧ q ≠ z ∧ p ≠ q := by simp [*]
        have i4 : p ≠ y ∧ p ≠ w ∧ q ≠ y ∧ q ≠ w ∧ p ≠ q := by simp [*]
        have e1 : casterEps dl x y p q = 1 := exy p q (by simp [*]) (by simp [*]) (by simp [*]) (by simp [*]) (by simp [*])
        have e2 : casterEps dl z w p q = 1 := ezw p q (by simp [*]) (by simp [*]) (by simp [*]) (by simp [*]) (by simp [*])
        simp only [casterG, if_pos i1, if_pos i2, if_pos i3, if_pos i4]
        rw [e1, e2]
        nlinarith [mul_le_mul_of_nonneg_left (casterEps_le_one dl x z p q) hc, mul_le_mul_of_nonneg_left (casterEps_le_one dl y w p q) hc]

/-- ★★ **`g({x,y}) = c`**（另一个樱桃 `{z,w}` 给出 `ε = 1`）。 -/
theorem casterG_xy (dl : X → X → ℝ) {x y z w : X} (hxy : x ≠ y) (hxz : x ≠ z)
    (hxw : x ≠ w) (hyz : y ≠ z) (hyw : y ≠ w)
    (hcz : ∀ p q : X, p ≠ q → p ≠ z → p ≠ w → q ≠ z → q ≠ w →
      dl z w + dl p q < dl z p + dl w q ∧ dl z w + dl p q < dl z q + dl w p)
    (c : ℝ) : casterG dl c x y z w x y = c := by
  have i1 : ¬ (x ≠ x ∧ x ≠ y ∧ y ≠ x ∧ y ≠ y ∧ x ≠ y) := by simp
  have i2 : x ≠ z ∧ x ≠ w ∧ y ≠ z ∧ y ≠ w ∧ x ≠ y := ⟨hxz, hxw, hyz, hyw, hxy⟩
  have i3 : ¬ (x ≠ x ∧ x ≠ z ∧ y ≠ x ∧ y ≠ z ∧ x ≠ y) := by simp
  have i4 : ¬ (x ≠ y ∧ x ≠ w ∧ y ≠ y ∧ y ≠ w ∧ x ≠ y) := by simp
  have e2 : casterEps dl z w x y = 1 :=
    casterEps_of_lt dl z w x y (hcz x y hxy hxz hxw hyz hyw).1 (hcz x y hxy hxz hxw hyz hyw).2
  simp only [casterG, if_neg i1, if_pos i2, if_neg i3, if_neg i4, e2]
  ring

/-- ★★ **`g({z,w}) = c`**（对称件）。 -/
theorem casterG_zw (dl : X → X → ℝ) {x y z w : X} (hzw : z ≠ w) (hxz : x ≠ z)
    (hxw : x ≠ w) (hyz : y ≠ z) (hyw : y ≠ w)
    (hcx : ∀ p q : X, p ≠ q → p ≠ x → p ≠ y → q ≠ x → q ≠ y →
      dl x y + dl p q < dl x p + dl y q ∧ dl x y + dl p q < dl x q + dl y p)
    (c : ℝ) : casterG dl c x y z w z w = c := by
  have i1 : z ≠ x ∧ z ≠ y ∧ w ≠ x ∧ w ≠ y ∧ z ≠ w :=
    ⟨hxz.symm, hyz.symm, hxw.symm, hyw.symm, hzw⟩
  have i2 : ¬ (z ≠ z ∧ z ≠ w ∧ w ≠ z ∧ w ≠ w ∧ z ≠ w) := by simp
  have i3 : ¬ (z ≠ x ∧ z ≠ z ∧ w ≠ x ∧ w ≠ z ∧ z ≠ w) := by simp
  have i4 : ¬ (z ≠ y ∧ z ≠ w ∧ w ≠ y ∧ w ≠ w ∧ z ≠ w) := by simp
  have e1 : casterEps dl x y z w = 1 :=
    casterEps_of_lt dl x y z w (hcx z w hzw hxz.symm hyz.symm hxw.symm hyw.symm).1
      (hcx z w hzw hxz.symm hyz.symm hxw.symm hyw.symm).2
  simp only [casterG, if_pos i1, if_neg i2, if_neg i3, if_neg i4, e1]
  ring

/-- **`Δ` 的逐项形式**（`= D̃_xy + D̃_zw − D̃_xz − D̃_yw`，见 `casterDeltaN_eq_Dtilde`）。 -/
noncomputable def casterDeltaN (α c : ℝ) (W : X → ℝ) (dl : X → X → ℝ)
    (x y z w : X) : ℝ :=
  (α / 2) * ∑ p, ∑ q, W p * W q * casterG dl c x y z w p q

/-- ★★★ **L4.2（文档定理 6，一般 `n`）**：`{x,y}`、`{z,w}` 是两条严格樱桃时 `Δ > 0`。
定量地 `Δ ≥ α c (W_x W_y + W_z W_w) > 0`。 -/
theorem casterDeltaN_pos (α c : ℝ) (hα : 0 < α) (hc : 0 < c)
    (W : X → ℝ) (hW : ∀ u, 0 < W u)
    (dl : X → X → ℝ) (hsym : ∀ a b, dl a b = dl b a)
    (x y z w : X) (hxy : x ≠ y) (hxz : x ≠ z) (hxw : x ≠ w)
    (hyz : y ≠ z) (hyw : y ≠ w) (hzw : z ≠ w)
    (hcx : ∀ p q : X, p ≠ q → p ≠ x → p ≠ y → q ≠ x → q ≠ y →
      dl x y + dl p q < dl x p + dl y q ∧ dl x y + dl p q < dl x q + dl y p)
    (hcz : ∀ p q : X, p ≠ q → p ≠ z → p ≠ w → q ≠ z → q ≠ w →
      dl z w + dl p q < dl z p + dl w q ∧ dl z w + dl p q < dl z q + dl w p) :
    0 < casterDeltaN α c W dl x y z w := by
  have hG : ∀ p q : X, 0 ≤ casterG dl c x y z w p q := fun p q =>
    casterG_nonneg dl hsym hxy hxz hxw hyz hyw hzw hcx hcz c hc.le p q
  have hrow : ∀ p : X, 0 ≤ ∑ q, W p * W q * casterG dl c x y z w p q := by
    intro p
    refine Finset.sum_nonneg fun q _ => ?_
    exact mul_nonneg (mul_nonneg (hW p).le (hW q).le) (hG p q)
  have hsub : (∑ p ∈ ({x, z} : Finset X), ∑ q, W p * W q * casterG dl c x y z w p q)
      ≤ ∑ p, ∑ q, W p * W q * casterG dl c x y z w p q :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun p _ _ => hrow p
  have hsplit : (∑ p ∈ ({x, z} : Finset X), ∑ q, W p * W q * casterG dl c x y z w p q)
      = (∑ q, W x * W q * casterG dl c x y z w x q)
        + (∑ q, W z * W q * casterG dl c x y z w z q) := by
    rw [Finset.sum_insert (by simp [hxz]), Finset.sum_singleton]
  have hx : W x * W y * c ≤ ∑ q, W x * W q * casterG dl c x y z w x q := by
    have h := Finset.single_le_sum (s := (Finset.univ : Finset X))
      (f := fun q => W x * W q * casterG dl c x y z w x q)
      (fun q _ => mul_nonneg (mul_nonneg (hW x).le (hW q).le) (hG x q)) (Finset.mem_univ y)
    rwa [casterG_xy dl hxy hxz hxw hyz hyw hcz c] at h
  have hz : W z * W w * c ≤ ∑ q, W z * W q * casterG dl c x y z w z q := by
    have h := Finset.single_le_sum (s := (Finset.univ : Finset X))
      (f := fun q => W z * W q * casterG dl c x y z w z q)
      (fun q _ => mul_nonneg (mul_nonneg (hW z).le (hW q).le) (hG z q)) (Finset.mem_univ w)
    rwa [casterG_zw dl hzw hxz hxw hyz hyw hcx c] at h
  have hsum : W x * W y * c + W z * W w * c
      ≤ ∑ p, ∑ q, W p * W q * casterG dl c x y z w p q := by
    linarith [hsub, hsplit, hx, hz]
  have h1 : 0 < W x * W y * c := mul_pos (mul_pos (hW x) (hW y)) hc
  have h2 : 0 < W z * W w * c := mul_pos (mul_pos (hW z) (hW w)) hc
  have hpos : 0 < ∑ p, ∑ q, W p * W q * casterG dl c x y z w p q := by linarith
  unfold casterDeltaN
  have hα2 : 0 < α / 2 := by linarith
  exact mul_pos hα2 hpos

/-! ## 3. 与 `D̃` 的接口（L3 的代数核） -/

/-- 文档 A3 的逐项期望 `α·W_a W_b W_c W_d·f(I)ε`（A4 取 `f ≡ c`）。 -/
noncomputable def casterTval (α c : ℝ) (W : X → ℝ) (dl : X → X → ℝ) :
    X → X → X → X → ℝ :=
  fun p q r s => α * W p * W q * W r * W s * (c * casterEps dl p q r s)

/-- `Ssum`：`Σ_{p,q ∉ {a,b}, p≠q} W_p W_q (c·ε_{ab|pq})`。
有序对求和（每个无序 2-子集算两次），故 `D̃` 那边带 `/2`。 -/
noncomputable def Ssum (W : X → ℝ) (dl : X → X → ℝ) (c : ℝ) (a b : X) : ℝ :=
  ∑ p, ∑ q, if p ≠ a ∧ p ≠ b ∧ q ≠ a ∧ q ≠ b ∧ p ≠ q then
    W p * W q * (c * casterEps dl a b p q) else 0

theorem rest_mem_iff (a b p : X) :
    p ∈ Phylo.Stat.CASTERD.rest a b ↔ p ≠ a ∧ p ≠ b := by
  simp [Phylo.Stat.CASTERD.rest]

theorem rest_erase_mem_iff (a b p q : X) :
    q ∈ Phylo.Stat.CASTERD.rest a b \ {p} ↔ q ≠ a ∧ q ≠ b ∧ q ≠ p := by
  simp [Phylo.Stat.CASTERD.rest, and_assoc]

theorem cond_iff (a b p q : X) :
    (p ≠ a ∧ p ≠ b ∧ q ≠ a ∧ q ≠ b ∧ p ≠ q)
      ↔ (p ∈ Phylo.Stat.CASTERD.rest a b ∧
          q ∈ Phylo.Stat.CASTERD.rest a b \ {p}) := by
  rw [rest_mem_iff, rest_erase_mem_iff]
  tauto

/-- `∑ x, (if x ∈ s then g x else 0) = ∑ x ∈ s, g x`。 -/
theorem sum_ite_mem' (g : X → ℝ) (s : Finset X) :
    (∑ x, (if x ∈ s then g x else 0)) = ∑ x ∈ s, g x := by
  rw [← Finset.sum_filter]
  congr 1
  ext x
  simp

/-- `if`-形式与 `Finset`-限定求和形式的换写。 -/
theorem sum_ite_mem_rest (f : X → X → ℝ) (s : Finset X) (t : X → Finset X) :
    (∑ p, ∑ q, (if p ∈ s ∧ q ∈ t p then f p q else 0)) = ∑ p ∈ s, ∑ q ∈ t p, f p q := by
  have step : ∀ p, (∑ q, (if p ∈ s ∧ q ∈ t p then f p q else 0))
      = if p ∈ s then ∑ q ∈ t p, f p q else 0 := by
    intro p
    by_cases hp : p ∈ s
    · rw [if_pos hp]
      have hcq : ∀ q, (if p ∈ s ∧ q ∈ t p then f p q else 0)
          = (if q ∈ t p then f p q else 0) := by
        intro q
        by_cases hq : q ∈ t p
        · rw [if_pos ⟨hp, hq⟩, if_pos hq]
        · rw [if_neg (fun h => hq h.2), if_neg hq]
      simp only [hcq]
      exact sum_ite_mem' (fun q => f p q) (t p)
    · rw [if_neg hp]
      have hcq : ∀ q, (if p ∈ s ∧ q ∈ t p then f p q else 0) = (0 : ℝ) := by
        intro q; rw [if_neg (fun h => hp h.1)]
      simp only [hcq, Finset.sum_const_zero]
  simp only [step]
  exact sum_ite_mem' (fun p => ∑ q ∈ t p, f p q) s

theorem Ssum_eq_rest (W : X → ℝ) (dl : X → X → ℝ) (c : ℝ) (a b : X) :
    Ssum W dl c a b
      = ∑ p ∈ Phylo.Stat.CASTERD.rest a b,
          ∑ q ∈ Phylo.Stat.CASTERD.rest a b \ {p},
            W p * W q * (c * casterEps dl a b p q) := by
  have hconv : Ssum W dl c a b
      = ∑ p, ∑ q, (if p ∈ Phylo.Stat.CASTERD.rest a b ∧
          q ∈ Phylo.Stat.CASTERD.rest a b \ {p} then
          W p * W q * (c * casterEps dl a b p q) else 0) := by
    unfold Ssum
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    by_cases h : (p ≠ a ∧ p ≠ b ∧ q ≠ a ∧ q ≠ b ∧ p ≠ q)
    · rw [if_pos h, if_pos ((cond_iff a b p q).mp h)]
    · rw [if_neg h, if_neg (fun h' => h ((cond_iff a b p q).mpr h'))]
  rw [hconv]
  exact sum_ite_mem_rest _ _ _

/-- ★★ **L3 的代数核（`ε` 版）**：`D̃_ab = (α/2)·Σ_{p,q} W_p W_q (c·ε_{ab|pq})`。
与 `Phylo.Stat.CASTERD.Dtilde_eq` 同一套代数（把 `W_a W_b` 提出来约掉）。 -/
theorem Dtilde_eq_casterEps (W : X → ℝ) (dl : X → X → ℝ) (c α : ℝ) (a b : X)
    (ha : W a ≠ 0) (hb : W b ≠ 0) :
    Phylo.Stat.CASTERD.Dtilde (casterTval α c W dl) W a b
      = (α / 2) * Ssum W dl c a b := by
  rw [Ssum_eq_rest]
  have hab : W a * W b ≠ 0 := mul_ne_zero ha hb
  have hfac : ∀ p q : X, α * W a * W b * W p * W q * (c * casterEps dl a b p q)
      = (W a * W b) * (α * W p * W q * (c * casterEps dl a b p q)) := by
    intro p q; ring
  unfold Phylo.Stat.CASTERD.Dtilde Phylo.Stat.CASTERD.D casterTval
  simp only [hfac, Finset.mul_sum]
  field_simp
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  ring

/-- ★★ **`Δ` 的四项分解**：`Σ_{Šxy} + Σ_{Šzw} − Σ_{Šxz} − Σ_{Šyw} = Σ_p Σ_q W_pW_q g(p,q)`。 -/
theorem Ssum_combine (W : X → ℝ) (dl : X → X → ℝ) (c : ℝ) (x y z w : X) :
    Ssum W dl c x y + Ssum W dl c z w - Ssum W dl c x z - Ssum W dl c y w
      = ∑ p, ∑ q, W p * W q * casterG dl c x y z w p q := by
  unfold Ssum casterG
  simp only [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  refine Finset.sum_congr rfl fun q _ => ?_
  split_ifs <;> ring

/-- ★★★ **L4.2 的第二种写法（= 文档定理 6 的 `Δ`）**：
`casterDeltaN` 就是 `D̃_xy + D̃_zw − D̃_xz − D̃_yw`。 -/
theorem casterDeltaN_eq_Dtilde (α c : ℝ) (W : X → ℝ) (dl : X → X → ℝ)
    (x y z w : X) (hWx : W x ≠ 0) (hWy : W y ≠ 0) (hWz : W z ≠ 0) (hWw : W w ≠ 0) :
    casterDeltaN α c W dl x y z w
      = Phylo.Stat.CASTERD.Dtilde (casterTval α c W dl) W x y
        + Phylo.Stat.CASTERD.Dtilde (casterTval α c W dl) W z w
        - Phylo.Stat.CASTERD.Dtilde (casterTval α c W dl) W x z
        - Phylo.Stat.CASTERD.Dtilde (casterTval α c W dl) W y w := by
  unfold casterDeltaN
  rw [Dtilde_eq_casterEps W dl c α x y hWx hWy,
      Dtilde_eq_casterEps W dl c α z w hWz hWw,
      Dtilde_eq_casterEps W dl c α x z hWx hWz,
      Dtilde_eq_casterEps W dl c α y w hWy hWw,
      ← Ssum_combine]
  ring

/-- ★★★ **L4.2（文档定理 6，最终形式）**：
`Δ := D̃_xy + D̃_zw − D̃_xz − D̃_yw > 0`（`n` 任意，`{x,y}`/`{z,w}` 严格是樱桃）。 -/
theorem fourPoint_n_pos (α c : ℝ) (hα : 0 < α) (hc : 0 < c)
    (W : X → ℝ) (hW : ∀ u, 0 < W u)
    (dl : X → X → ℝ) (hsym : ∀ a b, dl a b = dl b a)
    (x y z w : X) (hxy : x ≠ y) (hxz : x ≠ z) (hxw : x ≠ w)
    (hyz : y ≠ z) (hyw : y ≠ w) (hzw : z ≠ w)
    (hcx : ∀ p q : X, p ≠ q → p ≠ x → p ≠ y → q ≠ x → q ≠ y →
      dl x y + dl p q < dl x p + dl y q ∧ dl x y + dl p q < dl x q + dl y p)
    (hcz : ∀ p q : X, p ≠ q → p ≠ z → p ≠ w → q ≠ z → q ≠ w →
      dl z w + dl p q < dl z p + dl w q ∧ dl z w + dl p q < dl z q + dl w p) :
    0 < Phylo.Stat.CASTERD.Dtilde (casterTval α c W dl) W x y
        + Phylo.Stat.CASTERD.Dtilde (casterTval α c W dl) W z w
        - Phylo.Stat.CASTERD.Dtilde (casterTval α c W dl) W x z
        - Phylo.Stat.CASTERD.Dtilde (casterTval α c W dl) W y w := by
  rw [← casterDeltaN_eq_Dtilde α c W dl x y z w (ne_of_gt (hW x)) (ne_of_gt (hW y))
    (ne_of_gt (hW z)) (ne_of_gt (hW w))]
  exact casterDeltaN_pos α c hα hc W hW dl hsym x y z w hxy hxz hxw hyz hyw hzw hcx hcz

end Phylo.Stat.CASTERFourPoint
