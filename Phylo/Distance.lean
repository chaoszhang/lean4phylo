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
