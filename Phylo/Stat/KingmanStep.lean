/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.Stat.KingmanJumpChain

/-!
# `Phylo.Stat.KingmanStep` —— 跳链的**一步去向计数**（(2.1) 的正向语句）

`Phylo/Stat/KingmanLaw.lean` 底部把「层间一致性的**测度层**形式」与「整条跳链的轨迹空间对象」
归结为**同一个计数**（那里写成了两个 `def … : Prop` 缺口）。本文件补上其中的**核心计数**：
从 `k+1` 块划分 `Q` 出发，一次合并的「去向」恰有 `C(k+1,2)` 个 ——
这就是 Kingman 跳链每步在 `C(k+1,2)` 个选择里**均匀**挑一个的**计数依据**。

## 证明路线（**结构路线**，不枚举）

`2 · #{去向} = #(有序块对)`：
* **每个去向恰接 2 个有序块对**：`KingmanJumpChain.card_pairSet`；
* **有序块对的总数**：`KingmanJumpChain.card_offDiag`（`= |Q.parts|·(|Q.parts|−1)`）；
* 两者之间用**纤维分解**（`offDiag Q.parts = ⋃_{P ∈ 去向} pairSet Q P`，彼此不交）接起来。
-/

noncomputable section

open Classical

namespace Phylo.Stat.KingmanStep

open Phylo.Stat.KingmanJumpChain

variable {n : ℕ}

/-- ★★ **合并结果的块数**：`Q` 有 `k+1` 块时，合并任意两个不同块得到 `k` 块。 -/
theorem mergeOf_parts_card {k : ℕ} (Q : PartK n (k + 1))
    (p : Finset (Fin n) × Finset (Fin n)) (hp : p ∈ offDiag Q.1.parts) :
    (mergeOf (Q.1, p)).parts.card = k := by
  obtain ⟨h1, h2, hne⟩ := mem_offDiag.mp hp
  rw [mergeOf_eq Q.1 p.1 p.2 h1 h2 hne, card_mergePart, Q.2]
  omega

/-- ★★ **`mergeOf` 的结果确实是一个「去向」**。 -/
theorem mergeOf_mergeInto {k : ℕ} (Q : PartK n (k + 1))
    (p : Finset (Fin n) × Finset (Fin n)) (hp : p ∈ offDiag Q.1.parts) :
    MergeInto Q.1 (mergeOf (Q.1, p)) := by
  obtain ⟨h1, h2, hne⟩ := mem_offDiag.mp hp
  exact ⟨p.1, p.2, h1, h2, hne, (mergeOf_eq Q.1 p.1 p.2 h1 h2 hne).symm⟩

/-- 去向集合（`Q` 的一步合并结果）。 -/
def targets (n k : ℕ) (Q : PartK n (k + 1)) : Finset (PartK n k) :=
  Finset.univ.filter fun P => MergeInto Q.1 P.1

/-- ★★★ **有序块对按「去向」做纤维分解**（两侧互不交、并为全体）。 -/
theorem offDiag_eq_biUnion {k : ℕ} (Q : PartK n (k + 1)) :
    offDiag Q.1.parts = (targets n k Q).biUnion (fun P => pairSet Q.1 P.1) := by
  classical
  ext p
  constructor
  · intro hp
    refine Finset.mem_biUnion.mpr ⟨⟨mergeOf (Q.1, p), mergeOf_parts_card Q p hp⟩, ?_, ?_⟩
    · rw [targets, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, mergeOf_mergeInto Q p hp⟩
    · rw [mem_pairSet]
      exact ⟨hp, rfl⟩
  · intro hp
    obtain ⟨P, _, hpP⟩ := Finset.mem_biUnion.mp hp
    exact (mem_pairSet.mp hpP).1

/-- **常数和的取值**（单独提出，避免在 `rw` 链里被 cast 位置绊住）。 -/
theorem sum_const_targets {k : ℕ} (Q : PartK n (k + 1)) :
    (∑ _P ∈ targets n k Q, (2 : ℕ)) = 2 * (targets n k Q).card := by
  rw [Finset.sum_const, nsmul_eq_mul]
  exact Nat.mul_comm _ _

/-- ★★★ **去向的数 = 有序块对数的一半**（每个去向恰接 `2` 个有序块对）。 -/
theorem two_mul_card_targets {k : ℕ} (Q : PartK n (k + 1)) :
    2 * (targets n k Q).card = (offDiag Q.1.parts).card := by
  classical
  have hdisj : ∀ P ∈ targets n k Q, ∀ P' ∈ targets n k Q, P ≠ P' →
      Disjoint (pairSet Q.1 P.1) (pairSet Q.1 P'.1) := by
    intro P _ P' _ hne
    rw [Finset.disjoint_left]
    intro p hp hp'
    exact hne (Subtype.ext ((mem_pairSet.mp hp).2.symm.trans (mem_pairSet.mp hp').2))
  have hcard := Finset.card_biUnion hdisj
  rw [← offDiag_eq_biUnion (n := n) Q] at hcard
  have hsum : (∑ P ∈ targets n k Q, (pairSet Q.1 P.1).card)
      = ∑ _P ∈ targets n k Q, (2 : ℕ) :=
    Finset.sum_congr rfl (fun P hP => by
      simp only [targets, Finset.mem_filter] at hP
      simp only [card_pairSet, hP.2, ↓reduceIte])
  rw [hcard, hsum, sum_const_targets]

/-- ★★★ **(2.1) 的**正向**计数**（`ℝ` 口径）：从 `k+1` 块划分 `Q` 出发，
一步合并的**去向恰有 `C(k+1,2)` 个**。 -/
theorem card_mergeTargets_cast {k : ℕ} (Q : PartK n (k + 1)) :
    ((targets n k Q).card : ℝ) = ((k + 1).choose 2 : ℕ) := by
  have h : 2 * (targets n k Q).card = (k + 1) * k := by
    have h0 := two_mul_card_targets (n := n) Q
    rw [card_offDiag, Q.2] at h0
    rwa [Nat.add_sub_cancel] at h0
  have hcast : (2 : ℝ) * ((targets n k Q).card : ℝ) = ((k : ℝ) + 1) * (k : ℝ) := by
    have hh := congrArg (Nat.cast : ℕ → ℝ) h
    push_cast at hh
    linarith [hh]
  have h2 : (((k + 1).choose 2 : ℕ) : ℝ) * 2 = ((k : ℝ) + 1) * (k : ℝ) := by
    rw [two_mul_choose_two_cast (k + 1)]
    push_cast
    ring
  linarith

/-- ★★★ **固定 `Q`：一步「去向」上的均匀权重总和 = `Q` 的质量**。

即 `Σ_{P ∈ 去向} C⁻¹ · w(Q) = w(Q)`，其中 `C = C(k+1,2)` ——
这是「一步联合律的**左边缘** `= jumpMeasure n (k+1)`」的核心算术
（把「去向恰 `C(k+1,2)` 个」与「每个去向的权重 `w(Q)/C(k+1,2)`」相乘即得）。 -/
theorem sum_targets_jumpWeight {k : ℕ} (hk0 : 1 ≤ k) (Q : PartK n (k + 1)) :
    (∑ _P ∈ targets n k Q,
        (((k + 1).choose 2 : ℕ) : ℝ)⁻¹ * jumpWeight n (k + 1) Q)
      = jumpWeight n (k + 1) Q := by
  rw [Finset.sum_const, nsmul_eq_mul, card_mergeTargets_cast (n := n) Q]
  have hne : (((k + 1).choose 2 : ℕ) : ℝ) ≠ 0 := by
    have hpos : 0 < (k + 1).choose 2 := Nat.choose_pos (by omega)
    exact_mod_cast Nat.pos_iff_ne_zero.mp hpos
  field_simp

/-- ★★ **整个去向集合上的质量守恒**（对任意 `Finset` 的去向集合求和）：
`Σ_{Q ∈ S} Σ_{P ∈ 去向(Q)} C⁻¹ · w(Q) = Σ_{Q ∈ S} w(Q)` ——
「从 `S` 里的任一 `Q` 出发，一步之后的总质量不变」（左边缘的逐点形式）。 -/
theorem sum_targets_jumpWeight_finset {k : ℕ} (hk0 : 1 ≤ k)
    (S : Finset (PartK n (k + 1))) :
    (∑ Q ∈ S, ∑ _P ∈ targets n k Q,
        (((k + 1).choose 2 : ℕ) : ℝ)⁻¹ * jumpWeight n (k + 1) Q)
      = ∑ Q ∈ S, jumpWeight n (k + 1) Q :=
  Finset.sum_congr rfl fun Q _ => sum_targets_jumpWeight hk0 Q

end Phylo.Stat.KingmanStep
