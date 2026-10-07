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

/-! ## away-map：把相容 split 族「翻转」成镶嵌族

`ρ ∈ α` 固定。对每条 split `t`，取**不含 `ρ` 的那一侧** `t.away ρ`，并记下
`t.idx ρ ∈ Fin 2` 表明取的是 `sideA` 还是 `sideB`。于是 `t ↦ (t.away ρ, t.idx ρ)`
是**单射**（知道「不含 `ρ` 的那侧」与「哪一侧」就还原了整条 split），
故 `#S ≤ 2 · #(S.image away)`；而相容族的 away-image 由
`laminar_of_sidesCompatible_of_notMem` 知是**镶嵌族**。 -/

namespace Split

variable {α : Type u} [Fintype α] [DecidableEq α]

/-- **同一 `sideA` ⟹ split 相等**（`sideB` 是补，故 `parts` 相同）。 -/
theorem eq_of_sideA_eq {s t : Split α} (h : s.sideA = t.sideA) : s = t := by
  refine KPartition.eq_iff_parts s t |>.mpr ?_
  funext i
  fin_cases i
  · exact h
  · show s.sideB = t.sideB
    rw [Split.sideB_eq_compl, Split.sideB_eq_compl, h]

/-- `t` 的第 `i` 侧是否含 `ρ`。 -/
noncomputable def idx (ρ : α) (t : Split α) : Fin 2 := if ρ ∈ t.sideA then 1 else 0

/-- `t` 中**不含** `ρ` 的那一侧。 -/
noncomputable def away (ρ : α) (t : Split α) : Finset α :=
  if ρ ∈ t.sideA then t.sideB else t.sideA

theorem away_of_mem (ρ : α) {t : Split α} (h : ρ ∈ t.sideA) : t.away ρ = t.sideB :=
  if_pos h

theorem away_of_notMem (ρ : α) {t : Split α} (h : ρ ∉ t.sideA) : t.away ρ = t.sideA :=
  if_neg h

theorem idx_of_mem (ρ : α) {t : Split α} (h : ρ ∈ t.sideA) : t.idx ρ = 1 := if_pos h

theorem idx_of_notMem (ρ : α) {t : Split α} (h : ρ ∉ t.sideA) : t.idx ρ = 0 := if_neg h

/-- `ρ` 不在 `t.away ρ` 里。 -/
theorem not_mem_away (ρ : α) (t : Split α) : ρ ∉ t.away ρ := by
  by_cases h : ρ ∈ t.sideA
  · rw [away_of_mem ρ h]
    exact fun hb => (Finset.disjoint_left.mp t.disjoint_sides) h hb
  · rwa [away_of_notMem ρ h]

/-- `t.away ρ` 非空。 -/
theorem away_nonempty (ρ : α) (t : Split α) : (t.away ρ).Nonempty := by
  by_cases h : ρ ∈ t.sideA
  · rw [away_of_mem ρ h]; exact t.nonempty 1
  · rw [away_of_notMem ρ h]; exact t.nonempty 0

/-- `t.away ρ ⊆ univ \ {ρ}`。 -/
theorem away_subset (ρ : α) (t : Split α) : t.away ρ ⊆ Finset.univ \ {ρ} := by
  intro x hx
  exact Finset.mem_sdiff.mpr
    ⟨Finset.mem_univ x, fun hx' => t.not_mem_away ρ (Finset.mem_singleton.mp hx' ▸ hx)⟩

/-- `(away ρ, idx ρ)` **单射**（故每个纤维 ≤ 2）。 -/
theorem away_idx_injective (ρ : α) :
    Function.Injective (fun t : Split α => (t.away ρ, t.idx ρ)) := by
  intro t u h
  have h1 : t.away ρ = u.away ρ := congrArg Prod.fst h
  have h2 : t.idx ρ = u.idx ρ := congrArg Prod.snd h
  by_cases ht : ρ ∈ t.sideA
  · have hu : ρ ∈ u.sideA := by
      by_contra hu
      rw [idx_of_mem ρ ht, idx_of_notMem ρ hu] at h2
      exact absurd h2 (by decide)
    rw [away_of_mem ρ ht, away_of_mem ρ hu] at h1
    refine Split.eq_of_sideA_eq ?_
    have ht' : t.sideA = t.sideBᶜ := by rw [Split.sideB_eq_compl, compl_compl]
    have hu' : u.sideA = u.sideBᶜ := by rw [Split.sideB_eq_compl, compl_compl]
    rw [ht', hu', h1]
  · have hu : ρ ∉ u.sideA := by
      by_contra hu
      rw [idx_of_notMem ρ ht, idx_of_mem ρ hu] at h2
      exact absurd h2 (by decide)
    rw [away_of_notMem ρ ht, away_of_notMem ρ hu] at h1
    exact Split.eq_of_sideA_eq h1

/-- 相容 split 的 away-侧**相容**（`SidesCompatible`）。 -/
theorem sidesCompatible_away (ρ : α) {t u : Split α} (h : Compatible t u) :
    SidesCompatible (t.away ρ) (u.away ρ) := by
  have hbase : SidesCompatible t.sideA u.sideA := compatible_iff_sides.mp h
  by_cases ht : ρ ∈ t.sideA <;> by_cases hu : ρ ∈ u.sideA
  · rw [away_of_mem ρ ht, away_of_mem ρ hu, Split.sideB_eq_compl, Split.sideB_eq_compl]
    exact sidesCompatible_compl_right.mpr (sidesCompatible_compl_left.mpr hbase)
  · rw [away_of_mem ρ ht, away_of_notMem ρ hu, Split.sideB_eq_compl]
    exact sidesCompatible_compl_left.mpr hbase
  · rw [away_of_notMem ρ ht, away_of_mem ρ hu, Split.sideB_eq_compl]
    exact sidesCompatible_compl_right.mpr hbase
  · rw [away_of_notMem ρ ht, away_of_notMem ρ hu]; exact hbase

end Split

namespace Finset

variable {α : Type u} [Fintype α] [DecidableEq α]

/-- ★★ **`#S ≤ 2 · #(S.image away)`**（由 `(away, idx)` 单射 + 乘积计数）。 -/
theorem card_le_two_mul_card_image_away (S : Finset (Split α)) (ρ : α) :
    S.card ≤ 2 * (S.image (fun t => t.away ρ)).card := by
  have hcard : (S.image (fun t => (t.away ρ, t.idx ρ))).card = S.card :=
    Finset.card_image_of_injective S (Split.away_idx_injective ρ)
  have hle : (S.image (fun t => (t.away ρ, t.idx ρ))).card
      ≤ ((S.image (fun t => t.away ρ)) ×ˢ (Finset.univ : Finset (Fin 2))).card := by
    refine Finset.card_le_card ?_
    intro p hp
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hp
    exact Finset.mem_product.mpr
      ⟨Finset.mem_image.mpr ⟨t, ht, rfl⟩, Finset.mem_univ _⟩
  have hprod : ((S.image (fun t => t.away ρ)) ×ˢ (Finset.univ : Finset (Fin 2))).card
      = 2 * (S.image (fun t => t.away ρ)).card := by
    rw [Finset.card_product]
    simp [mul_comm]
  omega

/-- ★★★ **相容 split 族的基数上界**：`#S + 6 ≤ 4 · |α|`。

即 `X` 上两两相容的 split 族至多 `4|X| - 6` 条 —— 正是 **binary 树**的 split 数。
配合「binary 树的 split 数恰为 `4|X| - 6`」即得 `SplitsMaximal`（`BinarySplitsMaximal`）。 -/
theorem card_add_six_le_four_mul_card_of_pairwise_compatible
    (S : Finset (Split α)) (ρ : α) (h2 : 2 ≤ Fintype.card α)
    (hcompat : ∀ s ∈ S, ∀ t ∈ S, s ≠ t → Split.Compatible s t) :
    S.card + 6 ≤ 4 * Fintype.card α := by
  set F := S.image (fun t => t.away ρ) with hF
  have hl : LaminarFamily F := by
    intro A hA B hB
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hB
    rcases eq_or_ne t u with rfl | hne
    · exact Or.inl (Finset.Subset.refl _)
    · exact laminar_of_sidesCompatible_of_notMem
        (Split.sidesCompatible_away ρ (hcompat t ht u hu hne))
        (Split.not_mem_away ρ t) (Split.not_mem_away ρ u)
  have hYcard : (Finset.univ \ {ρ} : Finset α).card + 1 = Fintype.card α := by
    have h := Finset.card_sdiff_add_card_eq_card
      (s := ({ρ} : Finset α)) (t := (Finset.univ : Finset α)) (Finset.subset_univ _)
    simpa using h
  have hYne : (Finset.univ \ {ρ} : Finset α).Nonempty := by
    obtain ⟨x, y, hxy⟩ := Fintype.one_lt_card_iff_nontrivial.mp (by omega : 1 < Fintype.card α)
    by_cases hx : x = ρ
    · exact ⟨y, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, by simpa [← hx] using hxy.symm⟩⟩
    · exact ⟨x, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, by simpa using hx⟩⟩
  have hbound : F.card + 1 ≤ 2 * (Finset.univ \ {ρ} : Finset α).card := by
    refine card_add_one_le_two_mul_card_of_laminar _ F _ rfl hYne hl ?_ ?_
    · intro A hA
      obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hA
      exact Split.away_nonempty ρ t
    · intro A hA
      obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hA
      exact Split.away_subset ρ t
  have hle := card_le_two_mul_card_image_away S ρ
  rw [hF] at hbound
  have h1 : (S.image (fun t => t.away ρ)).card + 3 ≤ 2 * Fintype.card α := by omega
  omega

end Finset
