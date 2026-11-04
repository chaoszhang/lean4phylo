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

open NJ NJ.Dissimilarity

/-! ## 4. `ψ` 的注入性、特殊点、以及 `leaf b`／`w` 的邻接

先把后面反复用到的三件小事做掉：
* ★★ `liftFun_inj`（由 ★★★ `liftFun_dropFun`）；
* ★★ `liftFun_eq_leafb_iff` / `liftFun_eq_w_iff`（唯一性）；
* ★★★ `liftFun_special_iff`：`{leaf a, leaf b, z}` 与 `{leaf a, leaf b, z'}` 在 `ψ` 下**对应**
  （`w` 的三个邻居，两侧一致）。 -/

variable {a b : X} {w z : T.V} {w' z' : T'.V}

/-- ★★ **`ψ` 注入**。 -/
theorem liftFun_inj (φ : ShrinkV T b w ≃ ShrinkV T' b w')
    (hwb : w ≠ T.leaf b) (hw'b : w' ≠ T'.leaf b) :
    Function.Injective (liftFun φ) := by
  intro u v huv
  have hu := liftFun_dropFun φ hwb hw'b u
  have hv := liftFun_dropFun φ hwb hw'b v
  rw [← hu, huv, hv]

/-- ★★ `ψ v = T'.leaf b ↔ v = T.leaf b`。 -/
theorem liftFun_eq_leafb_iff (φ : ShrinkV T b w ≃ ShrinkV T' b w')
    (hwb : w ≠ T.leaf b) (hw'b : w' ≠ T'.leaf b) (v : T.V) :
    liftFun φ v = T'.leaf b ↔ v = T.leaf b := by
  constructor
  · intro h
    exact liftFun_inj φ hwb hw'b (h.trans (liftFun_leaf_b φ).symm)
  · intro h
    rw [h]
    exact liftFun_leaf_b φ

/-- ★★ `ψ v = w' ↔ v = w`。 -/
theorem liftFun_eq_w_iff (φ : ShrinkV T b w ≃ ShrinkV T' b w')
    (hwb : w ≠ T.leaf b) (hw'b : w' ≠ T'.leaf b) (v : T.V) :
    liftFun φ v = w' ↔ v = w := by
  constructor
  · intro h
    exact liftFun_inj φ hwb hw'b (h.trans (liftFun_w φ hwb).symm)
  · intro h
    rw [h]
    exact liftFun_w φ hwb

/-- ★★ **`ψ` 把 `T.leaf a` 送到 `T'.leaf a`**（`φ` 保标号的推论）。 -/
theorem liftFun_leaf_a (φ : ShrinkV T b w ≃ ShrinkV T' b w')
    (ha : T.leaf a ≠ T.leaf b ∧ T.leaf a ≠ w)
    (ha' : T'.leaf a ≠ T'.leaf b ∧ T'.leaf a ≠ w')
    (hφa : φ ⟨T.leaf a, ha⟩ = ⟨T'.leaf a, ha'⟩) :
    liftFun φ (T.leaf a) = T'.leaf a := by
  rw [liftFun_pack φ ha.1 ha.2, hφa]

/-- ★★ **`ψ` 把 `z` 送到 `z'`**。 -/
theorem liftFun_z (φ : ShrinkV T b w ≃ ShrinkV T' b w')
    (hz : z ≠ T.leaf b ∧ z ≠ w) (hz' : z' ≠ T'.leaf b ∧ z' ≠ w')
    (hφz : φ ⟨z, hz⟩ = ⟨z', hz'⟩) :
    liftFun φ z = z' := by
  rw [liftFun_pack φ hz.1 hz.2, hφz]

/-- ★★★ **`w` 的三个邻居在 `ψ` 下对应**：`v ∈ {leaf a, leaf b, z} ↔ ψ v ∈ {leaf a, leaf b, z'}`。 -/
theorem liftFun_special_iff (φ : ShrinkV T b w ≃ ShrinkV T' b w')
    (hwb : w ≠ T.leaf b) (hw'b : w' ≠ T'.leaf b)
    (ha : T.leaf a ≠ T.leaf b ∧ T.leaf a ≠ w)
    (ha' : T'.leaf a ≠ T'.leaf b ∧ T'.leaf a ≠ w')
    (hφa : φ ⟨T.leaf a, ha⟩ = ⟨T'.leaf a, ha'⟩)
    (hz : z ≠ T.leaf b ∧ z ≠ w) (hz' : z' ≠ T'.leaf b ∧ z' ≠ w')
    (hφz : φ ⟨z, hz⟩ = ⟨z', hz'⟩) (v : T.V) :
    (v = T.leaf a ∨ v = T.leaf b ∨ v = z) ↔
      (liftFun φ v = T'.leaf a ∨ liftFun φ v = T'.leaf b ∨ liftFun φ v = z') := by
  constructor
  · rintro (rfl | rfl | rfl)
    · exact Or.inl (liftFun_leaf_a φ ha ha' hφa)
    · exact Or.inr (Or.inl (liftFun_leaf_b φ))
    · exact Or.inr (Or.inr (liftFun_z φ hz hz' hφz))
  · rintro (h | h | h)
    · exact Or.inl (liftFun_inj φ hwb hw'b (h.trans (liftFun_leaf_a φ ha ha' hφa).symm))
    · exact Or.inr (Or.inl ((liftFun_eq_leafb_iff φ hwb hw'b v).mp h))
    · exact Or.inr (Or.inr (liftFun_inj φ hwb hw'b (h.trans (liftFun_z φ hz hz' hφz).symm)))



/-! ## 5. `ψ` 与三个特殊点的**对应判定** -/

/-- ★★ `⟨u,·⟩ = ⟨T.leaf a, ·⟩` 在 `φ` 下的像：`u = T.leaf a ↔ (φ ⟨u,·⟩).1 = T'.leaf a`。 -/
theorem pack_eq_leaf_a_iff {T T' : Phylogram.{u, v} X} {a b : X} {w : T.V} {w' : T'.V}
    (φ : ShrinkV T b w ≃ ShrinkV T' b w')
    (ha : T.leaf a ≠ T.leaf b ∧ T.leaf a ≠ w)
    (ha' : T'.leaf a ≠ T'.leaf b ∧ T'.leaf a ≠ w')
    (hφa : φ ⟨T.leaf a, ha⟩ = ⟨T'.leaf a, ha'⟩)
    {u : T.V} (hu : u ≠ T.leaf b ∧ u ≠ w) :
    (u = T.leaf a) ↔ ((φ ⟨u, hu⟩).1 = T'.leaf a) := by
  constructor
  · intro h
    subst u
    rw [show (⟨T.leaf a, ha⟩ : ShrinkV T b w) = ⟨T.leaf a, ha.1, ha.2⟩ from Subtype.ext rfl, hφa]
  · intro h
    have h2 : φ ⟨u, hu⟩ = ⟨T'.leaf a, ha'⟩ := by
      rw [show (⟨T'.leaf a, ha'⟩ : ShrinkV T' b w')
        = ⟨(φ ⟨u, hu⟩).1, (φ ⟨u, hu⟩).2⟩ from Subtype.ext h.symm]
    have h3 : (⟨u, hu⟩ : ShrinkV T b w) = ⟨T.leaf a, ha⟩ :=
      Equiv.injective φ (by rw [h2, hφa])
    exact congrArg Subtype.val h3

/-- ★★ `z` 的同款判定：`u = z ↔ (φ ⟨u,·⟩).1 = z'`。 -/
theorem pack_eq_z_iff {T T' : Phylogram.{u, v} X} {a b : X} {w z : T.V} {w' z' : T'.V}
    (φ : ShrinkV T b w ≃ ShrinkV T' b w')
    (hz : z ≠ T.leaf b ∧ z ≠ w) (hz' : z' ≠ T'.leaf b ∧ z' ≠ w')
    (hφz : φ ⟨z, hz⟩ = ⟨z', hz'⟩)
    {u : T.V} (hu : u ≠ T.leaf b ∧ u ≠ w) :
    (u = z) ↔ ((φ ⟨u, hu⟩).1 = z') := by
  constructor
  · intro h
    subst u
    rw [show (⟨z, hz⟩ : ShrinkV T b w) = ⟨z, hz.1, hz.2⟩ from Subtype.ext rfl, hφz]
  · intro h
    have h2 : φ ⟨u, hu⟩ = ⟨z', hz'⟩ := by
      rw [show (⟨z', hz'⟩ : ShrinkV T' b w') = ⟨(φ ⟨u, hu⟩).1, (φ ⟨u, hu⟩).2⟩ from Subtype.ext h.symm]
    have h3 : (⟨u, hu⟩ : ShrinkV T b w) = ⟨z, hz⟩ := Equiv.injective φ (by rw [h2, hφz])
    exact congrArg Subtype.val h3

/-! ## 6. `ψ` **保邻接**（三支）

`T` 的边分三类：与 `leaf b` 相连（唯一：`w`）、与 `w` 相连（`{leaf a, leaf b, z}`）、
其余（都在 `ShrinkV` 里，即收缩图的**旧边**）。三支分别由
★★ `leaf_b_adj_eq_midpoint`、★★ `adj_midpoint_cases` ＋ ★★★ `liftFun_special_iff`、
以及「`shrinkGraph` = 诱导子图 ＋ 一条新边」的分解给出。 -/

/-- ★★ **`leaf b` 那一支**：两侧的唯一邻居都是中点。 -/
theorem lift_adj_leaf_b {T T' : Phylogram.{u, v} X} {a b : X} {w : T.V} {w' : T'.V}
    (hbw : T.graph.Adj (T.leaf b) w) (hbw' : T'.graph.Adj (T'.leaf b) w')
    (φ : ShrinkV T b w ≃ ShrinkV T' b w')
    (hwb : w ≠ T.leaf b) (hw'b : w' ≠ T'.leaf b) (v : T.V) :
    T.graph.Adj (T.leaf b) v ↔ T'.graph.Adj (T'.leaf b) (liftFun φ v) := by
  have h1 : ∀ y : T.V, T.graph.Adj (T.leaf b) y ↔ y = w := by
    intro y
    exact ⟨leaf_b_adj_eq_midpoint T hbw y, by intro h; rw [h]; exact hbw⟩
  have h2 : ∀ y : T'.V, T'.graph.Adj (T'.leaf b) y ↔ y = w' := by
    intro y
    exact ⟨leaf_b_adj_eq_midpoint T' hbw' y, by intro h; rw [h]; exact hbw'⟩
  rw [h1 v, h2 (liftFun φ v), liftFun_eq_w_iff φ hwb hw'b v]

/-- ★★ **`w` 那一支**：两侧的邻居集都是 `{leaf a, leaf b, z}`／`{leaf a, leaf b, z'}`。 -/
theorem lift_adj_w {T T' : Phylogram.{u, v} X} {a b : X} {w z : T.V} {w' z' : T'.V}
    (hbin : T.toCladogram.IsBinary) (hbin' : T'.toCladogram.IsBinary) (hab : a ≠ b)
    (haw : T.graph.Adj (T.leaf a) w) (hbw : T.graph.Adj (T.leaf b) w)
    (hwz : T.graph.Adj w z) (hza : z ≠ T.leaf a) (hzb : z ≠ T.leaf b)
    (haw' : T'.graph.Adj (T'.leaf a) w') (hbw' : T'.graph.Adj (T'.leaf b) w')
    (hwz' : T'.graph.Adj w' z') (hza' : z' ≠ T'.leaf a) (hzb' : z' ≠ T'.leaf b)
    (φ : ShrinkV T b w ≃ ShrinkV T' b w')
    (hwb : w ≠ T.leaf b) (hw'b : w' ≠ T'.leaf b)
    (ha : T.leaf a ≠ T.leaf b ∧ T.leaf a ≠ w)
    (ha' : T'.leaf a ≠ T'.leaf b ∧ T'.leaf a ≠ w')
    (hφa : φ ⟨T.leaf a, ha⟩ = ⟨T'.leaf a, ha'⟩)
    (hz : z ≠ T.leaf b ∧ z ≠ w) (hz' : z' ≠ T'.leaf b ∧ z' ≠ w')
    (hφz : φ ⟨z, hz⟩ = ⟨z', hz'⟩) (v : T.V) :
    T.graph.Adj w v ↔ T'.graph.Adj w' (liftFun φ v) := by
  have hcases := adj_midpoint_cases T hbin hab haw hbw hwz hza hzb
  have hcases' := adj_midpoint_cases T' hbin' hab haw' hbw' hwz' hza' hzb'
  have h1 : T.graph.Adj w v ↔ (v = T.leaf a ∨ v = T.leaf b ∨ v = z) := by
    refine ⟨hcases v, ?_⟩
    rintro (h | h | h)
    · rw [h]; exact haw.symm
    · rw [h]; exact hbw.symm
    · rw [h]; exact hwz
  have h2 : T'.graph.Adj w' (liftFun φ v) ↔
      (liftFun φ v = T'.leaf a ∨ liftFun φ v = T'.leaf b ∨ liftFun φ v = z') := by
    refine ⟨hcases' (liftFun φ v), ?_⟩
    rintro (h | h | h)
    · rw [h]; exact haw'.symm
    · rw [h]; exact hbw'.symm
    · rw [h]; exact hwz'
  rw [h1, h2, liftFun_special_iff φ hwb hw'b ha ha' hφa hz hz' hφz v]

/-- ★★ **`ShrinkV` 内部那一支**：收缩图 = 诱导子图 ＋ 一条新边 `leaf a — z`，
而这条新边在 `T`／`T'` 里都**不是**边（★ `not_adj_leaf_a_z`），故两侧都去掉它即可。 -/
theorem lift_adj_shrink {T T' : Phylogram.{u, v} X} {a b : X} {w z : T.V} {w' z' : T'.V}
    (haw : T.graph.Adj (T.leaf a) w) (haw' : T'.graph.Adj (T'.leaf a) w')
    (hzw : z ≠ w) (hza : z ≠ T.leaf a) (hza' : z' ≠ T'.leaf a)
    (φ : ShrinkV T b w ≃ ShrinkV T' b w')
    (ha : T.leaf a ≠ T.leaf b ∧ T.leaf a ≠ w)
    (ha' : T'.leaf a ≠ T'.leaf b ∧ T'.leaf a ≠ w')
    (hφa : φ ⟨T.leaf a, ha⟩ = ⟨T'.leaf a, ha'⟩)
    (hz : z ≠ T.leaf b ∧ z ≠ w) (hz' : z' ≠ T'.leaf b ∧ z' ≠ w')
    (hφz : φ ⟨z, hz⟩ = ⟨z', hz'⟩)
    (hφadj : ∀ p q : ShrinkV T b w,
      (shrinkGraph T a b w z hza).Adj p q ↔ (shrinkGraph T' a b w' z' hza').Adj (φ p) (φ q))
    {u v : T.V} (hu : u ≠ T.leaf b ∧ u ≠ w) (hv : v ≠ T.leaf b ∧ v ≠ w) :
    T.graph.Adj u v ↔ T'.graph.Adj (liftFun φ u) (liftFun φ v) := by
  have keyT : T.graph.Adj u v ↔ (shrinkGraph T a b w z hza).Adj ⟨u, hu⟩ ⟨v, hv⟩ ∧
      ¬((u = T.leaf a ∧ v = z) ∨ (u = z ∧ v = T.leaf a)) := by
    constructor
    · intro h
      refine ⟨Or.inl h, ?_⟩
      rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact not_adj_leaf_a_z T haw hzw (h1 ▸ h2 ▸ h)
      · exact not_adj_leaf_a_z T haw hzw ((h1 ▸ h2 ▸ h).symm)
    · rintro ⟨h, hn⟩
      rcases h with h | h | h
      · exact h
      · exact absurd (Or.inl h) hn
      · exact absurd (Or.inr h) hn
  have keyT' : T'.graph.Adj (liftFun φ u) (liftFun φ v) ↔
      (shrinkGraph T' a b w' z' hza').Adj (φ ⟨u, hu⟩) (φ ⟨v, hv⟩) ∧
      ¬(((φ ⟨u, hu⟩).1 = T'.leaf a ∧ (φ ⟨v, hv⟩).1 = z') ∨
        ((φ ⟨u, hu⟩).1 = z' ∧ (φ ⟨v, hv⟩).1 = T'.leaf a)) := by
    rw [liftFun_pack φ hu.1 hu.2, liftFun_pack φ hv.1 hv.2]
    constructor
    · intro h
      refine ⟨Or.inl h, ?_⟩
      rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact not_adj_leaf_a_z T' haw' hz'.2 (h1 ▸ h2 ▸ h)
      · exact not_adj_leaf_a_z T' haw' hz'.2 ((h1 ▸ h2 ▸ h).symm)
    · rintro ⟨h, hn⟩
      rcases h with h | h | h
      · exact h
      · exact absurd (Or.inl h) hn
      · exact absurd (Or.inr h) hn
  rw [keyT, keyT']
  have hua : (u = T.leaf a) ↔ ((φ ⟨u, hu⟩).1 = T'.leaf a) :=
    pack_eq_leaf_a_iff φ ha ha' hφa hu
  have huz : (u = z) ↔ ((φ ⟨u, hu⟩).1 = z') := pack_eq_z_iff (a := a) φ hz hz' hφz hu
  have hva : (v = T.leaf a) ↔ ((φ ⟨v, hv⟩).1 = T'.leaf a) :=
    pack_eq_leaf_a_iff φ ha ha' hφa hv
  have hvz : (v = z) ↔ ((φ ⟨v, hv⟩).1 = z') :=
    pack_eq_z_iff (a := a) φ hz hz' hφz hv
  have hnew : ((u = T.leaf a ∧ v = z) ∨ (u = z ∧ v = T.leaf a)) ↔
      (((φ ⟨u, hu⟩).1 = T'.leaf a ∧ (φ ⟨v, hv⟩).1 = z') ∨
        ((φ ⟨u, hu⟩).1 = z' ∧ (φ ⟨v, hv⟩).1 = T'.leaf a)) := by
    constructor
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact Or.inl ⟨hua.mp h1, hvz.mp h2⟩
      · exact Or.inr ⟨huz.mp h1, hva.mp h2⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact Or.inl ⟨hua.mpr h1, hvz.mpr h2⟩
      · exact Or.inr ⟨huz.mpr h1, hva.mpr h2⟩
  rw [hφadj ⟨u, hu⟩ ⟨v, hv⟩, hnew]

/-- ★★★ **`ψ` 保邻接（合流）**：三支（`leaf b`／`w`／`ShrinkV` 内部）拼起来。 -/
theorem lift_adj_iff {T T' : Phylogram.{u, v} X} {a b : X} {w z : T.V} {w' z' : T'.V}
    (hbin : T.toCladogram.IsBinary) (hbin' : T'.toCladogram.IsBinary) (hab : a ≠ b)
    (haw : T.graph.Adj (T.leaf a) w) (hbw : T.graph.Adj (T.leaf b) w)
    (hwz : T.graph.Adj w z) (hza : z ≠ T.leaf a) (hzb : z ≠ T.leaf b)
    (haw' : T'.graph.Adj (T'.leaf a) w') (hbw' : T'.graph.Adj (T'.leaf b) w')
    (hwz' : T'.graph.Adj w' z') (hza' : z' ≠ T'.leaf a) (hzb' : z' ≠ T'.leaf b)
    (φ : ShrinkV T b w ≃ ShrinkV T' b w')
    (hwb : w ≠ T.leaf b) (hw'b : w' ≠ T'.leaf b)
    (ha : T.leaf a ≠ T.leaf b ∧ T.leaf a ≠ w)
    (ha' : T'.leaf a ≠ T'.leaf b ∧ T'.leaf a ≠ w')
    (hφa : φ ⟨T.leaf a, ha⟩ = ⟨T'.leaf a, ha'⟩)
    (hz : z ≠ T.leaf b ∧ z ≠ w) (hz' : z' ≠ T'.leaf b ∧ z' ≠ w')
    (hφz : φ ⟨z, hz⟩ = ⟨z', hz'⟩)
    (hφadj : ∀ p q : ShrinkV T b w,
      (shrinkGraph T a b w z hza).Adj p q ↔ (shrinkGraph T' a b w' z' hza').Adj (φ p) (φ q)) :
    ∀ u v : T.V, T.graph.Adj u v ↔ T'.graph.Adj (liftFun φ u) (liftFun φ v) := by
  intro u v
  have hzww : z ≠ w := by
    intro h
    have h2 := hwz
    rw [h] at h2
    exact T.graph.loopless.irrefl w h2
  by_cases hub : u = T.leaf b
  · subst hub
    rw [liftFun_leaf_b φ]
    exact lift_adj_leaf_b (a := a) hbw hbw' φ hwb hw'b v
  · by_cases huw : u = w
    · subst huw
      rw [liftFun_w φ hwb]
      exact lift_adj_w (a := a) hbin hbin' hab haw hbw hwz hza hzb haw' hbw' hwz' hza' hzb'
        φ hwb hw'b ha ha' hφa hz hz' hφz v
    · by_cases hvb : v = T.leaf b
      · subst hvb
        rw [liftFun_leaf_b φ]
        have h := lift_adj_leaf_b (T := T) (T' := T') (a := a) hbw hbw' φ hwb hw'b u
        exact ⟨fun hh => (h.mp hh.symm).symm, fun hh => (h.mpr hh.symm).symm⟩
      · by_cases hvw : v = w
        · subst hvw
          rw [liftFun_w φ hwb]
          have h := lift_adj_w (T := T) (T' := T') (a := a) hbin hbin' hab haw hbw hwz hza hzb
            haw' hbw' hwz' hza' hzb' φ hwb hw'b ha ha' hφa hz hz' hφz u
          exact ⟨fun hh => (h.mp hh.symm).symm, fun hh => (h.mpr hh.symm).symm⟩
        · exact lift_adj_shrink (a := a) haw haw'
            hzww hza hza'
            φ ha ha' hφa hz hz' hφz hφadj ⟨hub, huw⟩ ⟨hvb, hvw⟩

/-- ★★ **`ψ` 保标号**：`ψ (T.leaf x) = T'.leaf x`。

三分：`x = b` 用 ★★ `liftFun_leaf_b`；`x = a` 用 ★★ `liftFun_leaf_a`；
其余 `x` 是 `MergeOld` 的成员，`T.leaf x` 落在 `ShrinkV` 里，用 `φ` 的保标号（`hleaf`）。 -/
theorem liftFun_leaf {T T' : Phylogram.{u, v} X} {a b : X} {w z : T.V} {w' z' : T'.V}
    (hbin : T.toCladogram.IsBinary) (hbin' : T'.toCladogram.IsBinary) (hab : a ≠ b)
    (haw : T.graph.Adj (T.leaf a) w) (hbw : T.graph.Adj (T.leaf b) w)
    (haw' : T'.graph.Adj (T'.leaf a) w') (hbw' : T'.graph.Adj (T'.leaf b) w')
    (φ : ShrinkV T b w ≃ ShrinkV T' b w')
    (hwb : w ≠ T.leaf b) (hw'b : w' ≠ T'.leaf b)
    (ha : T.leaf a ≠ T.leaf b ∧ T.leaf a ≠ w)
    (ha' : T'.leaf a ≠ T'.leaf b ∧ T'.leaf a ≠ w')
    (hφa : φ ⟨T.leaf a, ha⟩ = ⟨T'.leaf a, ha'⟩)
    (hleaf : ∀ u : MergeIdx X a b,
      φ (leafShrink T hbin hab haw hbw u) = leafShrink T' hbin' hab haw' hbw' u)
    (x : X) : liftFun φ (T.leaf x) = T'.leaf x := by
  by_cases hxb : x = b
  · subst hxb
    exact liftFun_leaf_b φ
  · by_cases hxa : x = a
    · subst hxa
      exact liftFun_leaf_a φ ha ha' hφa
    · -- `x ∈ MergeOld`：`T.leaf x` 在 `ShrinkV` 里
      have hxw : T.leaf x ≠ w := leaf_ne_midpoint T hbin hab haw hbw x
      have hxb' : T.leaf x ≠ T.leaf b := fun h => hxb (T.leaf.injective h)
      rw [liftFun_pack φ hxb' hxw]
      have h1 : (⟨T.leaf x, hxb', hxw⟩ : ShrinkV T b w)
          = leafShrink T hbin hab haw hbw (Sum.inl ⟨x, by
              simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert,
                Finset.mem_singleton, not_or]
              exact ⟨hxa, hxb⟩⟩) := Subtype.ext rfl
      rw [h1, hleaf]
      rfl

/-- ★★★ **iso 提升**：把收缩树的顶点等价 ＋ 保邻接 ＋ 保标号，组装成 `T ≅ T'`。

三条输入分别是 ★★★ `lift_adj_iff`（保邻接）、★★ `liftFun_leaf`（保标号）
与 ★★★ `liftEquiv`（顶点等价）。 -/
theorem iso_of_shrink_equiv {T T' : Phylogram.{u, v} X} {a b : X} {w z : T.V} {w' z' : T'.V}
    (hbin : T.toCladogram.IsBinary) (hbin' : T'.toCladogram.IsBinary) (hab : a ≠ b)
    (haw : T.graph.Adj (T.leaf a) w) (hbw : T.graph.Adj (T.leaf b) w)
    (hwz : T.graph.Adj w z) (hza : z ≠ T.leaf a) (hzb : z ≠ T.leaf b)
    (haw' : T'.graph.Adj (T'.leaf a) w') (hbw' : T'.graph.Adj (T'.leaf b) w')
    (hwz' : T'.graph.Adj w' z') (hza' : z' ≠ T'.leaf a) (hzb' : z' ≠ T'.leaf b)
    (φ : ShrinkV T b w ≃ ShrinkV T' b w')
    (hwb : w ≠ T.leaf b) (hw'b : w' ≠ T'.leaf b)
    (ha : T.leaf a ≠ T.leaf b ∧ T.leaf a ≠ w)
    (ha' : T'.leaf a ≠ T'.leaf b ∧ T'.leaf a ≠ w')
    (hφa : φ ⟨T.leaf a, ha⟩ = ⟨T'.leaf a, ha'⟩)
    (hz : z ≠ T.leaf b ∧ z ≠ w) (hz' : z' ≠ T'.leaf b ∧ z' ≠ w')
    (hφz : φ ⟨z, hz⟩ = ⟨z', hz'⟩)
    (hφadj : ∀ p q : ShrinkV T b w,
      (shrinkGraph T a b w z hza).Adj p q ↔ (shrinkGraph T' a b w' z' hza').Adj (φ p) (φ q))
    (hleaf : ∀ u : MergeIdx X a b,
      φ (leafShrink T hbin hab haw hbw u) = leafShrink T' hbin' hab haw' hbw' u) :
    Nonempty (Iso T.toCladogram T'.toCladogram) := by
  have hadj := lift_adj_iff hbin hbin' hab haw hbw hwz hza hzb haw' hbw' hwz' hza' hzb'
    φ hwb hw'b ha ha' hφa hz hz' hφz hφadj
  have hleafc := liftFun_leaf (z := z) (z' := z') hbin hbin' hab haw hbw haw' hbw' φ hwb hw'b ha ha' hφa hleaf
  refine ⟨⟨?_, ?_⟩⟩
  · exact
      { toEquiv := liftEquiv φ hwb hw'b
        map_rel_iff' := fun {u v} => (hadj u v).symm }
  · intro x
    exact hleafc x

/-! ## 7. 归纳装配：**拓扑唯一性**

对 `|Y|` 强归纳。`|Y| ≤ 2` 用 ★★ `Cladogram.iso_of_card_le_two`；否则取 `Q`-最小对 `(a,b)`，
两棵树都把它当樱桃（★★★ `isCherry_of_njStep`），各自收缩（★★★ `shrinkPhylogram`），
归纳假设给收缩树的同构，最后由 ★★★ `iso_of_shrink_equiv` 提升回 `T ≅ T'`。 -/

/-- ★★★ **拓扑唯一性**：`δ` 的两个「正权 ＋ 二叉」实现树必同构。

这正是 `nj_recovers_topology_additive` 的数学内容：NJ 每轮选的 `Q`-最小对**必是真樱桃**
（★★★ `isCherry_of_njStep`），而「正权 ＋ 二叉 ＋ 实现」在归约下保持（★★★ `njReductionStep`），
故 NJ 的递归输出与真树实现同一个 `δ`，从而同构。 -/
theorem iso_of_realizes_binary : ∀ (n : ℕ),
    ∀ {Y : Type u} [Fintype Y] [DecidableEq Y], Fintype.card Y ≤ n →
      ∀ (δ : NJ.Dissimilarity Y) (T T' : Phylogram.{u, v} Y),
        (∀ e : Edge T.toCladogram, 0 < T.w e) → T.toCladogram.IsBinary →
        (∀ x y : Y, T.dist (T.leaf x) (T.leaf y) = δ.val x y) →
        (∀ e : Edge T'.toCladogram, 0 < T'.w e) → T'.toCladogram.IsBinary →
        (∀ x y : Y, T'.dist (T'.leaf x) (T'.leaf y) = δ.val x y) →
        Nonempty (Iso T.toCladogram T'.toCladogram) := by
  intro n
  induction n with
  | zero =>
      intro Y _ _ hcard δ T T' _ _ _ _ _ _
      exact Cladogram.iso_of_card_le_two (by omega)
  | succ n ih =>
      intro Y _ _ hcard δ T T' hwT hbinT hrealT hwT' hbinT' hrealT'
      by_cases hsmall : Fintype.card Y ≤ 2
      · exact Cladogram.iso_of_card_le_two hsmall
      · have hge3 : 3 ≤ Fintype.card Y := by omega
        obtain ⟨a, b, hstep⟩ := exists_njStep δ (by omega : 2 ≤ Fintype.card Y)
        have hab : a ≠ b := hstep.1
        have hcT : T.IsCherry a b := NJShrink.isCherry_of_njStep δ hwT hrealT hge3 hstep
        have hcT' : T'.IsCherry a b := NJShrink.isCherry_of_njStep δ hwT' hrealT' hge3 hstep
        have hcTk := hcT
        have hcT'k := hcT'
        obtain ⟨-, w, haw, hbw⟩ := hcT
        obtain ⟨-, w', haw', hbw'⟩ := hcT'
        obtain ⟨z, hwz, hza, hzb, -⟩ := NJShrink.exists_third T hbinT hab haw hbw
        obtain ⟨z', hwz', hza', hzb', -⟩ := NJShrink.exists_third T' hbinT' hab haw' hbw'
        have hlaT : T.leaf a ≠ T.leaf b ∧ T.leaf a ≠ w :=
          ⟨fun h => hab (T.leaf.injective h), NJShrink.leaf_ne_midpoint T hbinT hab haw hbw a⟩
        have hzmT : z ≠ T.leaf b ∧ z ≠ w :=
          ⟨hzb, fun h => T.graph.loopless.irrefl z (h ▸ hwz)⟩
        have hlaT' : T'.leaf a ≠ T'.leaf b ∧ T'.leaf a ≠ w' :=
          ⟨fun h => hab (T'.leaf.injective h),
            NJShrink.leaf_ne_midpoint T' hbinT' hab haw' hbw' a⟩
        have hzmT' : z' ≠ T'.leaf b ∧ z' ≠ w' :=
          ⟨hzb', fun h => T'.graph.loopless.irrefl z' (h ▸ hwz')⟩
        have hwbT : w ≠ T.leaf b :=
          (NJShrink.leaf_ne_midpoint T hbinT hab haw hbw b).symm
        have hwbT' : w' ≠ T'.leaf b :=
          (NJShrink.leaf_ne_midpoint T' hbinT' hab haw' hbw' b).symm
        -- 两侧的收缩树
        set ST := NJShrink.shrinkPhylogram T hbinT hab haw hbw hza hzb hwz hwT with hST
        set ST' := NJShrink.shrinkPhylogram T' hbinT' hab haw' hbw' hza' hzb' hwz' hwT' with hST'
        have hposST : ∀ e : Edge ST.toCladogram, 0 < ST.w e :=
          NJShrink.shrinkPhylogram_w_pos T hbinT hab haw hbw hza hzb hwz hwT
        have hbinST : ST.toCladogram.IsBinary :=
          NJShrink.shrinkPhylogram_isBinary T hbinT hab haw hbw hza hzb hwz hwT
        have hrealST : ∀ u v : MergeIdx Y a b,
            ST.dist (ST.leaf u) (ST.leaf v) = (mergeStep δ a b).val u v :=
          fun u v => NJShrink.shrinkPhylogram_dist T δ hbinT hab haw hbw hza hzb hwz hwT hcTk hrealT u v
        have hposST' : ∀ e : Edge ST'.toCladogram, 0 < ST'.w e :=
          NJShrink.shrinkPhylogram_w_pos T' hbinT' hab haw' hbw' hza' hzb' hwz' hwT'
        have hbinST' : ST'.toCladogram.IsBinary :=
          NJShrink.shrinkPhylogram_isBinary T' hbinT' hab haw' hbw' hza' hzb' hwz' hwT'
        have hrealST' : ∀ u v : MergeIdx Y a b,
            ST'.dist (ST'.leaf u) (ST'.leaf v) = (mergeStep δ a b).val u v :=
          fun u v =>
            NJShrink.shrinkPhylogram_dist T' δ hbinT' hab haw' hbw' hza' hzb' hwz' hwT' hcT'k hrealT' u v
        -- 归纳假设
        have hcardS : Fintype.card (MergeIdx Y a b) ≤ n := by
          have h := mergeStep_card (a := a) (b := b) hab
          omega
        obtain ⟨isoS⟩ := ih hcardS (mergeStep δ a b) ST ST'
          hposST hbinST hrealST hposST' hbinST' hrealST'
        -- 取出收缩树的顶点等价与两条保性质
        let φ : ShrinkV T b w ≃ ShrinkV T' b w' := isoS.gIso.toEquiv
        have hφadj : ∀ p q : ShrinkV T b w,
            (shrinkGraph T a b w z hza).Adj p q
              ↔ (shrinkGraph T' a b w' z' hza').Adj (φ p) (φ q) :=
          fun p q => (isoS.gIso.map_rel_iff').symm
        have hφleaf : ∀ u : MergeIdx Y a b,
            φ (leafShrink T hbinT hab haw hbw u) = leafShrink T' hbinT' hab haw' hbw' u :=
          fun u => isoS.leaf_compat u
        have hφa : φ ⟨T.leaf a, hlaT⟩ = ⟨T'.leaf a, hlaT'⟩ := hφleaf (Sum.inr ())
        have hφz : φ ⟨z, hzmT⟩ = ⟨z', hzmT'⟩ := by
          have h1 : (shrinkGraph T' a b w' z' hza').Adj
              (φ ⟨T.leaf a, hlaT⟩) (φ ⟨z, hzmT⟩) :=
            (hφadj ⟨T.leaf a, hlaT⟩ ⟨z, hzmT⟩).mp (Or.inr (Or.inl ⟨rfl, rfl⟩))
          rw [hφa] at h1
          have h2 : (φ ⟨z, hzmT⟩).1 = z' :=
            (NJShrink.shrinkGraph_adj_leaf_a_iff T' a b w' z' hza' haw' hlaT'
              (v := φ ⟨z, hzmT⟩)).mp h1
          exact Subtype.ext h2
        exact iso_of_shrink_equiv hbinT hbinT' hab haw hbw hwz hza hzb haw' hbw' hwz' hza' hzb'
          φ hwbT hwbT' hlaT hlaT' hφa hzmT hzmT' hφz hφadj hφleaf

/-- ★★★ **L5a｜`nj_recovers_topology_additive`**：可加（正权 binary 实现）情形下，
`δ` **唯一决定**系统发生树的拓扑 —— 即任何一致算法（含 NJ）都只能给出同一个拓扑。

`n := Fintype.card Y` 处取 ★★★ `iso_of_realizes_binary`。 -/
theorem nj_recovers_topology_additive {Y : Type u} [Fintype Y] [DecidableEq Y]
    (δ : NJ.Dissimilarity Y) (T T' : Phylogram.{u, v} Y)
    (hwT : ∀ e : Edge T.toCladogram, 0 < T.w e) (hbinT : T.toCladogram.IsBinary)
    (hrealT : ∀ x y : Y, T.dist (T.leaf x) (T.leaf y) = δ.val x y)
    (hwT' : ∀ e : Edge T'.toCladogram, 0 < T'.w e) (hbinT' : T'.toCladogram.IsBinary)
    (hrealT' : ∀ x y : Y, T'.dist (T'.leaf x) (T'.leaf y) = δ.val x y) :
    Nonempty (Iso T.toCladogram T'.toCladogram) :=
  iso_of_realizes_binary (Fintype.card Y) (le_refl _) δ T T'
    hwT hbinT hrealT hwT' hbinT' hrealT'

end Phylo.Stat.NJRecovers
