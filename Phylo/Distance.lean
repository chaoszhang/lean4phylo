/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.SDiff

/-!
# `Phylo.Distance` —— 有限集对称差距离

**通用**骨架：`symmDiffCard S S' = |S △ S'|`，并证明它是度量。

下游使用者：
* `Split.rfDistance`（`Phylo/Algorithm/RF.lean`）—— Robinson–Foulds 距离；
* `quartetDistance`（`Phylo/Quartet.lean`）—— quartet 距离。
-/

/-- **有限集对称差距离**：两个有限集的对称差基数。 -/
def symmDiffCard {β : Type*} [DecidableEq β] (S S' : Finset β) : ℕ :=
  ((S \ S') ∪ (S' \ S)).card

theorem symmDiffCard_def {β : Type*} [DecidableEq β] (S S' : Finset β) :
    symmDiffCard S S' = ((S \ S') ∪ (S' \ S)).card := rfl

/-- 对称差距离**对称**。 -/
theorem symmDiffCard_comm {β : Type*} [DecidableEq β] (S S' : Finset β) :
    symmDiffCard S S' = symmDiffCard S' S := by
  rw [symmDiffCard_def, symmDiffCard_def, Finset.union_comm]

/-- 与自身距离为 0。 -/
@[simp] theorem symmDiffCard_self {β : Type*} [DecidableEq β] (S : Finset β) :
    symmDiffCard S S = 0 := by
  simp [symmDiffCard_def]

/-- **分离性**：距离为 0 ⟺ 两集相等。 -/
@[simp] theorem symmDiffCard_eq_zero_iff {β : Type*} [DecidableEq β] {S S' : Finset β} :
    symmDiffCard S S' = 0 ↔ S = S' := by
  rw [symmDiffCard_def, Finset.card_eq_zero, Finset.union_eq_empty,
    Finset.sdiff_eq_empty_iff_subset, Finset.sdiff_eq_empty_iff_subset]
  constructor
  · rintro ⟨h1, h2⟩
    exact Finset.Subset.antisymm h1 h2
  · intro h
    exact ⟨by rw [h], by rw [h]⟩

/-- **三角不等式**。 -/
theorem symmDiffCard_triangle {β : Type*} [DecidableEq β] (S R T : Finset β) :
    symmDiffCard S T ≤ symmDiffCard S R + symmDiffCard R T := by
  rw [symmDiffCard_def, symmDiffCard_def, symmDiffCard_def]
  refine le_trans (Finset.card_le_card ?_) (Finset.card_union_le _ _)
  intro x hx
  simp only [Finset.mem_union, Finset.mem_sdiff] at hx ⊢
  tauto

/-- ★★ **对称差的基数公式**（W11h / Q2-① 的通用器材）：

`|S △ S'| = |S| + |S'| − 2·|S ∩ S'|`。

用于把「quartet 距离 ≤ …」这类不等式化归到**基数**运算上（`RF` 与 `quartet` 两个距离
共用本骨架 `symmDiffCard`）。 -/
theorem symmDiffCard_eq_card_add_sub_two_inter {β : Type*} [DecidableEq β]
    (S S' : Finset β) :
    symmDiffCard S S' = S.card + S'.card - 2 * (S ∩ S').card := by
  have h1 : (S \ S').card = S.card - (S ∩ S').card := by
    rw [Finset.card_sdiff, Finset.inter_comm]
  have h2 : (S' \ S).card = S'.card - (S ∩ S').card := Finset.card_sdiff
  have hdisj : Disjoint (S \ S') (S' \ S) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_sdiff.mp hx').1
  have hsub : (S ∩ S').card ≤ S.card := Finset.card_le_card Finset.inter_subset_left
  have hsub' : (S ∩ S').card ≤ S'.card := Finset.card_le_card Finset.inter_subset_right
  rw [symmDiffCard_def, Finset.card_union_of_disjoint hdisj, h1, h2]
  omega

/-- ★★ **上界**：对称差不超过两集大小之和（Q2-①「quartet 距离 ≤ …」的最朴素形式）。 -/
theorem symmDiffCard_le_card_add {β : Type*} [DecidableEq β] (S S' : Finset β) :
    symmDiffCard S S' ≤ S.card + S'.card := by
  rw [symmDiffCard_def]
  calc ((S \ S') ∪ (S' \ S)).card
      ≤ (S \ S').card + (S' \ S).card := Finset.card_union_le _ _
    _ ≤ S.card + S'.card :=
        Nat.add_le_add (Finset.card_le_card (Finset.sdiff_subset))
          (Finset.card_le_card (Finset.sdiff_subset))
