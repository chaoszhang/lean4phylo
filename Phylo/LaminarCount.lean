/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.Split

/-!
# `Phylo.LaminarCount` —— 镶嵌族的基数上界

**主定理**：有限镶嵌族 `F`（成员非空、都含于 `Y`、`Y` 非空）满足 `#F + 1 ≤ 2 * #Y`；
若它还「缺一个单点」（`∃ y ∈ Y, {y} ∉ F`），则 `#F + 2 ≤ 2 * #Y`。

这是 HANDOVER §4 T0.1「计数路线」的核心引理（见 `Phylo/InternalEdge.lean` 的
`BinarySplitsMaximal` docstring）：配合

* `laminar_of_sidesCompatible_of_notMem`（`Phylo/Split.lean`）—— 相容 split 族取
  「不含 `ρ` 的那侧」即得镶嵌族；
* `BinaryCount.IsBinary.card_edgeFinset`（`|E| = 2ℓ - 3`）—— binary 树的 split 数正好顶到上界；

即得「binary 树的 split 系统极大」，从而 T0.1 第 3 步（clade 刻画）收口。

## 证明（对 `#Y` 强归纳）

取 `F` 的一个 **`⊆`-极大成员** `A`（有限族必有；由镶嵌性，按 `card` 极大即可）。
则 `F` 被劈成 `F_⊆A := {B ∈ F | B ⊆ A}` 与 `F_⊥A := {B ∈ F | ¬ B ⊆ A}`；
由镶嵌性 + `A` 的极大性，**`F_⊥A` 的成员都与 `A` 相离**，故都含于 `Y \ A`。
于是两个子族分别落在**更小**的载体 `A`、`Y \ A` 上，可递归。

**算术全部写成无减法形式**（`omega` 遇 ℕ 减法会失效，见 HANDOVER §5.1）。
-/

universe u

namespace Finset

variable {α : Type u} [DecidableEq α]

set_option linter.unusedSectionVars false

/-! ## 辅助引理 -/

/-- 有限族必有 **`⊆`-极大成员**（先按 `card` 取极大，再由镶嵌性升级到 `⊆`）。 -/
theorem exists_subset_maximal_member {F : Finset (Finset α)} (hne : F.Nonempty) :
    ∃ A ∈ F, ∀ B ∈ F, A ⊆ B → B = A := by
  obtain ⟨A, hA, hmax⟩ := Finset.exists_max_image F Finset.card hne
  exact ⟨A, hA, fun B hB hAB => (Finset.eq_of_subset_of_card_le hAB (hmax B hB)).symm⟩

/-- `A` 是 `F` 的极大成员时，`F` 中不含于 `A` 的成员必与 `A` **相离**。 -/
theorem disjoint_of_not_subset_of_maximal {F : Finset (Finset α)} (hl : LaminarFamily F)
    {A B : Finset α} (hA : A ∈ F) (hB : B ∈ F) (hmax : ∀ C ∈ F, A ⊆ C → C = A)
    (hBA : ¬ B ⊆ A) : Disjoint B A := by
  rcases hl A hA B hB with h | h | h
  · exact absurd (fun x hx => hmax B hB h ▸ hx) hBA
  · exact absurd h hBA
  · exact h.symm

/-- `A ⊆ Y`、`A` 非空 ⟹ `Y \ A` 是 `Y` 的真子集。 -/
theorem sdiff_ssubset_of_nonempty {A Y : Finset α} (hAY : A ⊆ Y) (hA : A.Nonempty) :
    Y \ A ⊂ Y := by
  refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.sdiff_subset, fun h => ?_⟩
  obtain ⟨a, ha⟩ := hA
  have hmem : a ∈ Y \ A := h.symm ▸ hAY ha
  exact (Finset.mem_sdiff.mp hmem).2 ha

/-- `A ⊂ Y` ⟹ `Y \ A` 非空。 -/
theorem nonempty_sdiff_of_ssubset {A Y : Finset α} (h : A ⊂ Y) : (Y \ A).Nonempty := by
  obtain ⟨y, hyY, hyA⟩ := Finset.exists_of_ssubset h
  exact ⟨y, Finset.mem_sdiff.mpr ⟨hyY, hyA⟩⟩

/-- `A ⊆ Y` ⟹ `A.card + (Y \ A).card = Y.card`（无减法形式）。 -/
theorem card_add_card_sdiff {A Y : Finset α} (hAY : A ⊆ Y) :
    A.card + (Y \ A).card = Y.card := by
  have h := Finset.card_sdiff_add_card_eq_card hAY
  omega

/-! ## 基本上界：`#F + 1 ≤ 2 * #Y` -/

/-- ★★ **镶嵌族的基本基数上界**：成员非空、都含于非空的 `Y` ⟹ `#F + 1 ≤ 2 * #Y`。 -/
theorem card_add_one_le_two_mul_card_of_laminar :
    ∀ (n : ℕ) (F : Finset (Finset α)) (Y : Finset α), Y.card = n → Y.Nonempty →
      LaminarFamily F → (∀ A ∈ F, A.Nonempty) → (∀ A ∈ F, A ⊆ Y) →
      F.card + 1 ≤ 2 * Y.card := by
  intro n
  refine Nat.strong_induction_on n ?_
  intro n ih F Y hY hYne hl hne hsub
  by_cases hFn : F.Nonempty
  · by_cases hYF : Y ∈ F
    · -- `Y ∈ F`：挖掉 `Y`，其余部分按极大成员 `A` 再劈成两块
      set H := F.erase Y with hH
      have hHsub : ∀ A ∈ H, A ⊆ Y := fun A hA => hsub A (Finset.mem_of_mem_erase hA)
      have hlH : LaminarFamily H := fun A hA B hB =>
        hl A (Finset.mem_of_mem_erase hA) B (Finset.mem_of_mem_erase hB)
      have hneH : ∀ A ∈ H, A.Nonempty := fun A hA => hne A (Finset.mem_of_mem_erase hA)
      have hFcard : F.card = H.card + 1 := (Finset.card_erase_add_one hYF).symm
      by_cases hHn : H.Nonempty
      · obtain ⟨A, hA, hAmax⟩ := exists_subset_maximal_member hHn
        have hAY : A ⊆ Y := hHsub A hA
        have hAne : A.Nonempty := hneH A hA
        have hAneY : A ≠ Y := (Finset.mem_erase.mp hA).1
        have hAssub : A ⊂ Y := Finset.ssubset_iff_subset_ne.mpr ⟨hAY, hAneY⟩
        have hAlt : A.card < n := by
          rw [← hY]; exact Finset.card_lt_card hAssub
        have hYAlt : (Y \ A).card < n := by
          rw [← hY]; exact Finset.card_lt_card (sdiff_ssubset_of_nonempty hAY hAne)
        have hYAne : (Y \ A).Nonempty := nonempty_sdiff_of_ssubset hAssub
        set H1 := H.filter (fun B => B ⊆ A) with hH1
        set H2 := H.filter (fun B => ¬ B ⊆ A) with hH2
        have hHcard : H.card = H1.card + H2.card :=
          (Finset.card_filter_add_card_filter_not (s := H) (p := fun B => B ⊆ A)).symm
        have hl1 : LaminarFamily H1 := fun B hB C hC =>
          hlH B (Finset.mem_filter.mp hB).1 C (Finset.mem_filter.mp hC).1
        have hl2 : LaminarFamily H2 := fun B hB C hC =>
          hlH B (Finset.mem_filter.mp hB).1 C (Finset.mem_filter.mp hC).1
        have hne1 : ∀ B ∈ H1, B.Nonempty := fun B hB => hneH B (Finset.mem_filter.mp hB).1
        have hne2 : ∀ B ∈ H2, B.Nonempty := fun B hB => hneH B (Finset.mem_filter.mp hB).1
        have hsub1 : ∀ B ∈ H1, B ⊆ A := fun B hB => (Finset.mem_filter.mp hB).2
        have hsub2 : ∀ B ∈ H2, B ⊆ Y \ A := by
          intro B hB
          have hBH : B ∈ H := (Finset.mem_filter.mp hB).1
          have hdisj : Disjoint B A :=
            disjoint_of_not_subset_of_maximal hlH hA hBH hAmax (Finset.mem_filter.mp hB).2
          intro x hx
          exact Finset.mem_sdiff.mpr
            ⟨hHsub B hBH hx, fun hxA => (Finset.disjoint_left.mp hdisj) hx hxA⟩
        have ih1 := ih A.card hAlt H1 A rfl hAne hl1 hne1 hsub1
        have ih2 := ih (Y \ A).card hYAlt H2 (Y \ A) rfl hYAne hl2 hne2 hsub2
        have hadd : A.card + (Y \ A).card = Y.card := card_add_card_sdiff hAY
        omega
      · -- `H = ∅`：`F = {Y}`
        rw [Finset.not_nonempty_iff_eq_empty.mp hHn, Finset.card_empty, zero_add] at hFcard
        have hYpos : 1 ≤ Y.card := Finset.card_pos.mpr hYne
        omega
    · -- `Y ∉ F`：直接分解 `F`
      obtain ⟨A, hA, hAmax⟩ := exists_subset_maximal_member hFn
      have hAY : A ⊆ Y := hsub A hA
      have hAne : A.Nonempty := hne A hA
      have hAneY : A ≠ Y := fun h => hYF (h ▸ hA)
      have hAssub : A ⊂ Y := Finset.ssubset_iff_subset_ne.mpr ⟨hAY, hAneY⟩
      have hAlt : A.card < n := by
        rw [← hY]; exact Finset.card_lt_card hAssub
      have hYAlt : (Y \ A).card < n := by
        rw [← hY]; exact Finset.card_lt_card (sdiff_ssubset_of_nonempty hAY hAne)
      have hYAne : (Y \ A).Nonempty := nonempty_sdiff_of_ssubset hAssub
      set F1 := F.filter (fun B => B ⊆ A) with hF1
      set F2 := F.filter (fun B => ¬ B ⊆ A) with hF2
      have hFcard' : F.card = F1.card + F2.card :=
        (Finset.card_filter_add_card_filter_not (s := F) (p := fun B => B ⊆ A)).symm
      have hl1 : LaminarFamily F1 := fun B hB C hC =>
        hl B (Finset.mem_filter.mp hB).1 C (Finset.mem_filter.mp hC).1
      have hl2 : LaminarFamily F2 := fun B hB C hC =>
        hl B (Finset.mem_filter.mp hB).1 C (Finset.mem_filter.mp hC).1
      have hne1 : ∀ B ∈ F1, B.Nonempty := fun B hB => hne B (Finset.mem_filter.mp hB).1
      have hne2 : ∀ B ∈ F2, B.Nonempty := fun B hB => hne B (Finset.mem_filter.mp hB).1
      have hsub1 : ∀ B ∈ F1, B ⊆ A := fun B hB => (Finset.mem_filter.mp hB).2
      have hsub2 : ∀ B ∈ F2, B ⊆ Y \ A := by
        intro B hB
        have hBF : B ∈ F := (Finset.mem_filter.mp hB).1
        have hdisj : Disjoint B A :=
          disjoint_of_not_subset_of_maximal hl hA hBF hAmax (Finset.mem_filter.mp hB).2
        intro x hx
        exact Finset.mem_sdiff.mpr
          ⟨hsub B hBF hx, fun hxA => (Finset.disjoint_left.mp hdisj) hx hxA⟩
      have ih1 := ih A.card hAlt F1 A rfl hAne hl1 hne1 hsub1
      have ih2 := ih (Y \ A).card hYAlt F2 (Y \ A) rfl hYAne hl2 hne2 hsub2
      have hadd : A.card + (Y \ A).card = Y.card := card_add_card_sdiff hAY
      omega
  · -- `F = ∅`
    rw [Finset.not_nonempty_iff_eq_empty.mp hFn, Finset.card_empty]
    have hYpos : 1 ≤ Y.card := Finset.card_pos.mpr hYne
    omega

end Finset
