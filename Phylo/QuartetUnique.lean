/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.Stat.MSC

/-!
# `Phylo.QuartetUnique` —— 二叉树在 4-元集上的 quartet **唯一**（模 `swap`）

一棵树在每个 4-元叶集 `S` 上诱导的 quartet 在无根意义下**唯一**
（模 `swap`，即 `ab|cd = cd|ab`）。这说明「quartet 系统 `q_T`」对二叉树**良定义**
—— 正是 `Phylo.Stat.MSC` 里 `QuartetTree.q` 字段对一般树所缺的那一步。

**证明**（纯组合）：
1. 若 `q₁`、`q₂` 分别由 `T` 的 split `s₁`、`s₂` 在 `S` 上诱导，则 `s₁`、`s₂`
   **相容**（`pairwiseCompatible`），且相容性在限制到 `S` 上保持；
2. `S` 上的两个 **2|2** split 相容 ⟺ 它们相等或互补
   （4 元集上的三个 2|2 split 两两**不**相容）。
-/

universe u v

variable {X : Type u} [Fintype X] [DecidableEq X]

namespace Split

/-- **同一 `A` 侧的 split 相等**（`sideB` 是 `sideA` 的补，故 `parts` 相同）。 -/
theorem eq_of_sideA_eq {α : Type*} [Fintype α] [DecidableEq α] {s t : Split α}
    (h : s.sideA = t.sideA) : s = t := by
  refine KPartition.eq_iff_parts s t |>.mpr ?_
  funext i
  fin_cases i
  · exact h
  · show s.sideB = t.sideB
    rw [sideB_eq_compl, sideB_eq_compl, h]

end Split

open Classical in
/-- ★★★ **二叉树在 4-元集上展示唯一的 quartet（模 `swap`）**。

若 `q₁`、`q₂` 都是 `T` 在 `S` 上展示的 **2|2** split（`|sideA| = 2`），
则 `q₁ = q₂` 或 `q₁ = q₂.swap`。

**用途**：说明「树的 quartet 系统」`q_T` 良定义（`QuartetTree` 的 `q` 字段）。 -/
theorem Cladogram.displaysSplitOn_unique {T : Cladogram.{u, v} X} {S : Finset X}
    {q₁ q₂ : Split ↥S} (h₁ : T.DisplaysSplitOn S q₁) (h₂ : T.DisplaysSplitOn S q₂)
    (hS : S.card = 4) (hc₁ : q₁.sideA.card = 2) (hc₂ : q₂.sideA.card = 2) :
    q₁ = q₂ ∨ q₁ = q₂.swap := by
  classical
  obtain ⟨s, hs, hqs⟩ := h₁
  obtain ⟨t, ht, hqt⟩ := h₂
  have hcomp : Split.Compatible s t := pairwiseCompatible T s hs t ht
  have hcard₁ : (q₁.sideAᶜ : Finset ↥S).card = 2 := by
    rw [Finset.card_compl, Fintype.card_coe, hS, hc₁]
  have hcard₂ : (q₂.sideAᶜ : Finset ↥S).card = 2 := by
    rw [Finset.card_compl, Fintype.card_coe, hS, hc₂]
  -- 把 `q.sideA` 写成 `S` 内的过滤形式
  have hq₁ : q₁.sideA = Finset.univ.filter (fun x : ↥S => x.1 ∈ s.sideA) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hqs x
  have hq₂ : q₂.sideA = Finset.univ.filter (fun x : ↥S => x.1 ∈ t.sideA) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hqt x
  -- 补侧同理（`sideB` 是 `sideA` 的补）
  have hq₁B : q₁.sideAᶜ = Finset.univ.filter (fun x : ↥S => x.1 ∈ s.sideB) := by
    ext x
    simp only [Finset.mem_compl, hq₁, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hx
      rwa [s.sideB_eq_compl, Finset.mem_compl]
    · intro hx hsA
      exact (Finset.disjoint_left.mp s.disjoint_sides) hsA hx
  have hq₂B : q₂.sideAᶜ = Finset.univ.filter (fun x : ↥S => x.1 ∈ t.sideB) := by
    ext x
    simp only [Finset.mem_compl, hq₂, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hx
      rwa [t.sideB_eq_compl, Finset.mem_compl]
    · intro hx htA
      exact (Finset.disjoint_left.mp t.disjoint_sides) htA hx
  -- 不交性传递到 `S` 上
  have hdisj : ∀ {A B : Finset X}, Disjoint A B →
      Disjoint (Finset.univ.filter (fun x : ↥S => x.1 ∈ A))
        (Finset.univ.filter (fun x : ↥S => x.1 ∈ B)) := by
    intro A B hd
    rw [Finset.disjoint_left]
    intro x hxA hxB
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hxA hxB
    exact (Finset.disjoint_left.mp hd) hxA hxB
  -- 「`q₁` 与 `q₂` 互补」⟹ `q₁ = q₂.swap`
  have swap_of_compl : q₂.sideA = q₁.sideAᶜ → q₁ = q₂.swap := by
    intro heq
    have hsw : q₁.swap = q₂ :=
      Split.eq_of_sideA_eq
        ((Split.swap_sideA q₁).trans ((Split.sideB_eq_compl q₁).trans heq.symm))
    have hfin := congrArg Split.swap hsw
    rwa [Split.swap_swap] at hfin
  rcases hcomp with hd | hd | hd | hd
  · -- `Disjoint s.A t.A`：`q₁.A ∩ q₂.A = ∅` ⟹ `q₂.A = q₁.Aᶜ`
    have hdd : Disjoint q₁.sideA q₂.sideA := by
      rw [hq₁, hq₂]
      exact hdisj hd
    have hsub : q₂.sideA ⊆ q₁.sideAᶜ := fun x hx => by
      rw [Finset.mem_compl]
      exact fun hx1 => (Finset.disjoint_left.mp hdd) hx1 hx
    exact Or.inr (swap_of_compl (Finset.eq_of_subset_of_card_le hsub (by rw [hcard₁, hc₂])))
  · -- `Disjoint s.A t.B`：`q₁.A ∩ q₂.B = ∅` ⟹ `q₁.A ⊆ q₂.A`
    have hdd : Disjoint q₁.sideA q₂.sideAᶜ := by
      rw [hq₁, hq₂B]
      exact hdisj hd
    have hsub : q₁.sideA ⊆ q₂.sideA := fun x hx => by
      by_contra hx2
      exact (Finset.disjoint_left.mp hdd) hx (by simpa [Finset.mem_compl] using hx2)
    exact Or.inl (Split.eq_of_sideA_eq (Finset.eq_of_subset_of_card_le hsub (by rw [hc₂, hc₁])))
  · -- `Disjoint s.B t.A`：`q₁.B ∩ q₂.A = ∅` ⟹ `q₂.A ⊆ q₁.A`
    have hdd : Disjoint q₁.sideAᶜ q₂.sideA := by
      rw [hq₁B, hq₂]
      exact hdisj hd
    have hsub : q₂.sideA ⊆ q₁.sideA := fun x hx => by
      by_contra hx1
      exact (Finset.disjoint_left.mp hdd) (by simpa [Finset.mem_compl] using hx1) hx
    exact Or.inl (Split.eq_of_sideA_eq
      (Finset.eq_of_subset_of_card_le hsub (by rw [hc₁, hc₂]))).symm
  · -- `Disjoint s.B t.B`：`q₁.B ∩ q₂.B = ∅` ⟹ `q₁.Aᶜ ⊆ q₂.A`
    have hdd : Disjoint q₁.sideAᶜ q₂.sideAᶜ := by
      rw [hq₁B, hq₂B]
      exact hdisj hd
    have hsub : q₁.sideAᶜ ⊆ q₂.sideA := fun x hx => by
      by_contra hx2
      exact (Finset.disjoint_left.mp hdd) hx (by simpa [Finset.mem_compl] using hx2)
    refine Or.inr (swap_of_compl ?_)
    exact (Finset.eq_of_subset_of_card_le hsub (by rw [hcard₁, hc₂])).symm
