/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.Split

/-!
# `Phylo.Algorithm.RF` —— Robinson–Foulds 距离

`CONCEPTS.md` §5 M5 算法层：**RF 距离**是两个 split 系统的**对称差大小**
`d(S,S') = |S △ S'|`。本文件证明它是**度量**（对称、分离、三角不等式），
于任意有限 split 系统上成立 —— 不依赖树的构造。

（注：一般还有加权 / 簇版 RF；此处给**无权簇版**，够 M5 起步用。）
-/

namespace Split

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- **Robinson–Foulds 距离**：两个 split 系统的**对称差**的元素个数。 -/
def rfDistance (S S' : Finset (Split α)) : ℕ := ((S \ S') ∪ (S' \ S)).card

/-- 对称差展开。 -/
theorem rfDistance_def (S S' : Finset (Split α)) :
    rfDistance S S' = ((S \ S') ∪ (S' \ S)).card := rfl

/-- RF 距离**对称**。 -/
theorem rfDistance_comm (S S' : Finset (Split α)) : rfDistance S S' = rfDistance S' S := by
  rw [rfDistance_def, rfDistance_def, Finset.union_comm]

/-- 与自身 RF 距离为 0。 -/
@[simp] theorem rfDistance_self (S : Finset (Split α)) : rfDistance S S = 0 := by
  simp [rfDistance_def]

/-- **分离性**：RF 距离为 0 ⟺ 两个系统相等。 -/
@[simp] theorem rfDistance_eq_zero_iff {S S' : Finset (Split α)} :
    rfDistance S S' = 0 ↔ S = S' := by
  rw [rfDistance_def, Finset.card_eq_zero, Finset.union_eq_empty,
    Finset.sdiff_eq_empty_iff_subset, Finset.sdiff_eq_empty_iff_subset]
  constructor
  · rintro ⟨h1, h2⟩
    exact Finset.Subset.antisymm h1 h2
  · intro h
    exact ⟨by rw [h], by rw [h]⟩

/-- **三角不等式**：`d(S,T) ≤ d(S,R) + d(R,T)`。 -/
theorem rfDistance_triangle (S R T : Finset (Split α)) :
    rfDistance S T ≤ rfDistance S R + rfDistance R T := by
  rw [rfDistance_def, rfDistance_def, rfDistance_def]
  refine le_trans (Finset.card_le_card ?_) (Finset.card_union_le _ _)
  intro x hx
  simp only [Finset.mem_union, Finset.mem_sdiff] at hx ⊢
  tauto

end Split
