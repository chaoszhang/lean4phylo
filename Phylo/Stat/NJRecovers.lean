/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.Stat.NJShrink
import Phylo.SplitsDetermineTreeBase

/-!
# `Phylo.Stat.NJRecovers` —— L5a 装配层（进行中）

`nj_recovers_topology_additive` 走**拓扑唯一性**路线：

> 两个「正权 ＋ 二叉」的实现树，若实现**同一个** `δ`，则同构。

归纳（对 `|Y|` 递降）：
1. `|Y| ≤ 2`：★★ `Cladogram.iso_of_card_le_two`（库内已有）；
2. `|Y| ≥ 3`：取 `Q` 在有限对上的最小对 `(a,b)`（★★ `exists_njStep`）；
   由 ★★★ `NJShrink.isCherry_of_njStep`，**两棵**树都把 `{a,b}` 当樱桃；
   各自收缩（★★★ `shrinkPhylogram`）后实现**同一个** `mergeStep δ a b`
   （★★★ `shrinkPhylogram_dist`）⇒ 归纳假设给收缩树同构 `φ`；
3. **iso 提升**：把 `φ` 沿 `leaf b ↦ leaf b`、`w ↦ w'` 扩回 `T ≅ T'`。

## 已证

* ★★ `exists_njStep`：`2 ≤ |Y|` ⇒ 存在 `Q`-最小对。
* ★★ `liftFun` ＋ `dropFun`：提升／下降映射（`leaf b ↦ leaf b`、`w ↦ w'`、其余走 `φ`／`φ.symm`），
  及 `liftFun_leaf_b` / `liftFun_w` / `liftFun_pack` / `liftFun_dropFun` / `dropFun_liftFun`。
-/

noncomputable section

universe u v

namespace Phylo.Stat.NJRecovers

open Phylo
open Phylo.Stat.NJShrink
open Phylo.Stat.CASTERNJStep

variable {X : Type u} [Fintype X] [DecidableEq X]

/-! ## 1. `Q`-最小对的存在性 -/

/-- ★★ **`njStep` 的存在性**：`2 ≤ |X|` 时 `Q_δ` 在有限对集上取到最小值。

（`Q` 的定义域是**有向**对；用 `Finset.filter` 取出 `i ≠ j` 的对，
再由 `Finset.exists_min_image` 取最小者。） -/
theorem exists_njStep (δ : NJ.Dissimilarity X) (hcard : 2 ≤ Fintype.card X) :
    ∃ a b : X, njStep δ a b := by
  classical
  have hpair : ((Finset.univ : Finset (X × X)).filter (fun p => p.1 ≠ p.2)).Nonempty := by
    have h1 : 1 < (Finset.univ : Finset X).card := by
      rw [Finset.card_univ]
      omega
    obtain ⟨a, -, b, -, hab⟩ := Finset.one_lt_card.mp h1
    exact ⟨(a, b), by simp [hab]⟩
  obtain ⟨p, hp, hmin⟩ :=
    Finset.exists_min_image ((Finset.univ : Finset (X × X)).filter (fun p => p.1 ≠ p.2))
      (fun p : X × X => δ.Q p.1 p.2) hpair
  have hpq : p.1 ≠ p.2 := (Finset.mem_filter.mp hp).2
  exact ⟨p.1, p.2, hpq, fun i j hij => hmin (i, j) (by simp [hij])⟩

/-! ## 2. iso 提升的顶点映射

设两棵树 `T`、`T'`（同一标签集 `X`）各以 `{a,b}` 为樱桃，中点分别是 `w`、`w'`；
`φ` 是**收缩树之间**的顶点等价（`ShrinkV T b w ≃ ShrinkV T' b w'`）。

* `liftFun φ`：`T.leaf b ↦ T'.leaf b`、`w ↦ w'`、其余 `v ↦ (φ ⟨v,·⟩).1`；
* `dropFun φ`：反向（`T'.leaf b ↦ T.leaf b`、`w' ↦ w`、其余 `v' ↦ (φ.symm ⟨v',·⟩).1`）。 -/

variable {T T' : Phylogram.{u, v} X}

/-- ★★ **提升映射**。 -/
def liftFun {b : X} {w : T.V} {w' : T'.V} (φ : ShrinkV T b w ≃ ShrinkV T' b w') :
    T.V → T'.V :=
  fun v =>
    if hv : v = T.leaf b then T'.leaf b
    else if hv' : v = w then w'
    else (φ ⟨v, hv, hv'⟩).1

/-- ★★ **下降映射**（`liftFun` 的逆候选）。 -/
def dropFun {b : X} {w : T.V} {w' : T'.V} (φ : ShrinkV T b w ≃ ShrinkV T' b w') :
    T'.V → T.V :=
  fun v' =>
    if hv : v' = T'.leaf b then T.leaf b
    else if hv' : v' = w' then w
    else (φ.symm ⟨v', hv, hv'⟩).1

/-- ★★ **`T.leaf b` 的像**。 -/
theorem liftFun_leaf_b {b : X} {w : T.V} {w' : T'.V}
    (φ : ShrinkV T b w ≃ ShrinkV T' b w') :
    liftFun φ (T.leaf b) = T'.leaf b := by
  unfold liftFun
  rw [dif_pos rfl]

/-- ★★ **`w` 的像**。 -/
theorem liftFun_w {b : X} {w : T.V} {w' : T'.V}
    (φ : ShrinkV T b w ≃ ShrinkV T' b w') (hwb : w ≠ T.leaf b) :
    liftFun φ w = w' := by
  unfold liftFun
  rw [dif_neg hwb, dif_pos rfl]

/-- ★★ **其余点的像**。 -/
theorem liftFun_pack {b : X} {w : T.V} {w' : T'.V}
    (φ : ShrinkV T b w ≃ ShrinkV T' b w') {v : T.V} (hb : v ≠ T.leaf b) (hw : v ≠ w) :
    liftFun φ v = (φ ⟨v, hb, hw⟩).1 := by
  unfold liftFun
  rw [dif_neg hb, dif_neg hw]

/-- ★★ **`T'.leaf b` 的原像**。 -/
theorem dropFun_leaf_b {b : X} {w : T.V} {w' : T'.V}
    (φ : ShrinkV T b w ≃ ShrinkV T' b w') :
    dropFun φ (T'.leaf b) = T.leaf b := by
  unfold dropFun
  rw [dif_pos rfl]

/-- ★★ **`w'` 的原像**。 -/
theorem dropFun_w {b : X} {w : T.V} {w' : T'.V}
    (φ : ShrinkV T b w ≃ ShrinkV T' b w') (hw'b : w' ≠ T'.leaf b) :
    dropFun φ w' = w := by
  unfold dropFun
  rw [dif_neg hw'b, dif_pos rfl]

/-- ★★ **其余点的原像**。 -/
theorem dropFun_pack {b : X} {w : T.V} {w' : T'.V}
    (φ : ShrinkV T b w ≃ ShrinkV T' b w') {v' : T'.V} (hb : v' ≠ T'.leaf b)
    (hw : v' ≠ w') : dropFun φ v' = (φ.symm ⟨v', hb, hw⟩).1 := by
  unfold dropFun
  rw [dif_neg hb, dif_neg hw]

/-- ★★ **`dropFun` 是 `liftFun` 的左逆**（在两个中点都不与 `leaf b` 重合时）。 -/
theorem liftFun_dropFun {b : X} {w : T.V} {w' : T'.V}
    (φ : ShrinkV T b w ≃ ShrinkV T' b w')
    (hwb : w ≠ T.leaf b) (hw'b : w' ≠ T'.leaf b) (v : T.V) :
    dropFun φ (liftFun φ v) = v := by
  by_cases hb : v = T.leaf b
  · subst hb
    rw [liftFun_leaf_b, dropFun_leaf_b]
  · by_cases hw : v = w
    · subst hw
      rw [liftFun_w φ hwb, dropFun_w φ hw'b]
    · rw [liftFun_pack φ hb hw]
      have hx1 : (φ ⟨v, hb, hw⟩).1 ≠ T'.leaf b := (φ ⟨v, hb, hw⟩).2.1
      have hx2 : (φ ⟨v, hb, hw⟩).1 ≠ w' := (φ ⟨v, hb, hw⟩).2.2
      rw [dropFun_pack φ hx1 hx2]
      have hsub : (⟨(φ ⟨v, hb, hw⟩).1, hx1, hx2⟩ : ShrinkV T' b w') = φ ⟨v, hb, hw⟩ :=
        Subtype.ext rfl
      rw [hsub]
      exact congrArg Subtype.val (Equiv.symm_apply_apply φ ⟨v, hb, hw⟩)

/-- ★★ **`liftFun` 是 `dropFun` 的左逆**（对称件）。 -/
theorem dropFun_liftFun {b : X} {w : T.V} {w' : T'.V}
    (φ : ShrinkV T b w ≃ ShrinkV T' b w')
    (hwb : w ≠ T.leaf b) (hw'b : w' ≠ T'.leaf b) (v : T'.V) :
    liftFun φ (dropFun φ v) = v := by
  by_cases hb : v = T'.leaf b
  · subst hb
    rw [dropFun_leaf_b, liftFun_leaf_b]
  · by_cases hw : v = w'
    · subst hw
      rw [dropFun_w φ hw'b, liftFun_w φ hwb]
    · rw [dropFun_pack φ hb hw]
      have hy1 : (φ.symm ⟨v, hb, hw⟩).1 ≠ T.leaf b := (φ.symm ⟨v, hb, hw⟩).2.1
      have hy2 : (φ.symm ⟨v, hb, hw⟩).1 ≠ w := (φ.symm ⟨v, hb, hw⟩).2.2
      rw [liftFun_pack φ hy1 hy2]
      have hsub : (⟨(φ.symm ⟨v, hb, hw⟩).1, hy1, hy2⟩ : ShrinkV T b w) = φ.symm ⟨v, hb, hw⟩ :=
        Subtype.ext rfl
      rw [hsub]
      exact congrArg Subtype.val (Equiv.apply_symm_apply φ ⟨v, hb, hw⟩)

/-- ★★ **提升后的顶点等价**。 -/
def liftEquiv {b : X} {w : T.V} {w' : T'.V}
    (φ : ShrinkV T b w ≃ ShrinkV T' b w')
    (hwb : w ≠ T.leaf b) (hw'b : w' ≠ T'.leaf b) : T.V ≃ T'.V where
  toFun := liftFun φ
  invFun := dropFun φ
  left_inv := liftFun_dropFun φ hwb hw'b
  right_inv := dropFun_liftFun φ hwb hw'b

end Phylo.Stat.NJRecovers
