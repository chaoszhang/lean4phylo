/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.Stat.TrivialSplitCount
import Mathlib.Tactic

/-!
# `Phylo.Stat.SplitFin4Count` —— `Split (Fin 4)` 的**计数事实**（W13l 目标 1）

## 1. 要证什么

库内整套 quartet 记账都建立在「四叶上有 **14** 个（**有向**）split」这条事实上
（`QuartetFreq.p_sum_one` 对 **14** 个有序分量求和 = 1），但此前只有**零件**、没有总数：

* `MSCProof.card_splits_two`（`Phylo/Stat/MSCProof.lean:665`）：**`2|2`** 恰 **6** 个；
* `TrivialSplitCount.card_trivial_splits_four`（`:199`）：**平凡（`1|3`）** 恰 **8** 个；
* `14 = 6 + 8` 此前**只在数值脚本里**出现过（W13f 实测，未形式化）。

本文件补上 `Fintype.card (Split (Fin 4)) = 14` 并给三类分解。

## 2. 路线

**关键结构性事实**（`Phylo/Split.lean:70` 注释：`Fin 2` 索引把两侧**有序化**）：
由 `Split.union_sides`（`:220`）＋ `Split.disjoint_sides`（`:216`），**`sideA` 完全决定整个
`Split`**（`sideB = univ \ sideA`）。于是

```
Split (Fin 4) ≃ {S : Finset (Fin 4) // S.Nonempty ∧ S ≠ univ}      -- 2^4 - 2 = 14
```

正向 `sideA`、反向 `Phylo.splitOf`，互逆由 `CASTERTopoSplit.eq_of_sideA_eq` 收口。
⇒ **不**在 `↥(Finset.univ : Finset (Fin 4))` 上做**子类型等价**搬运
（W13f 已实测它与 `Fin 4` **不是** defeq，那是**已记录的坑**）。

## 3. 三类分解（`|sideA| ∈ {1,2,3}`，`|sideA| = 4` 不可达）

| 类 | 计数 | 收口方式 |
|---|---|---|
| `2\|2` | **6** | `sideA` 与 `(univ : Finset (Fin 4)).powersetCard 2` **双射**（`card_splits_two` 同一双射） |
| `1\|3`（含两朝向） | **8** | `14 − 6`（`card_sdiff`），并与 `TrivialSplitCount.trivialFamily 4` 的 `8` 对照 |
| 合计 | **14** | 两族互补 ⇒ 相加 |

## 4. 诚实边界

* 只做**计数**；`QuartetFreq` 的构造与 `p_sum_one` 不在本文件范围。
* `#eval Fintype.card (Split (Fin 4))` **求不出来**（`instFintypeKPartition` 是
  `noncomputable` ⇒ `dependsOnNoncomputable`，BRIEF §9 已记录）⇒ §2 只用**可计算**的
  `Finset (Finset (Fin 4))`（幂集）枚举作代理。
* 无占位证明、无新公理、无编译器求值捷径；不新增库外 import。
-/

set_option autoImplicit false

noncomputable section

open Finset

namespace Phylo.Stat.SplitFin4Count

private theorem empty_ne_univ_fin4 : (∅ : Finset (Fin 4)) ≠ Finset.univ := by
  intro h
  have hc : (0 : ℕ) = 4 := by
    have h2 := congrArg Finset.card h
    simpa only [Finset.card_univ, Fintype.card_fin, Finset.card_empty] using h2
  omega

/-- `(univ : Finset (Finset (Fin 4))).card = 16`（`instFintypeFinset` 用幂集给出）。 -/
theorem card_univ_finset_fin4 : (Finset.univ : Finset (Finset (Fin 4))).card = 16 := by
  show ((Finset.univ : Finset (Fin 4)).powerset).card = 16
  rw [Finset.card_powerset, Finset.card_univ, Fintype.card_fin]
  norm_num

theorem card_finset_fin4 : Fintype.card (Finset (Fin 4)) = 16 :=
  card_univ_finset_fin4

/-- `Fin 4` 的 `Finset` 中**非空真子集**恰 `14` 个。 -/
theorem card_erase_erase : (((Finset.univ : Finset (Finset (Fin 4))).erase ∅).erase
    (Finset.univ : Finset (Fin 4))).card = 14 := by
  have h1 : (∅ : Finset (Fin 4)) ∈ (Finset.univ : Finset (Finset (Fin 4))) :=
    Finset.mem_univ _
  have h2 : (Finset.univ : Finset (Fin 4)) ∈
      (Finset.univ : Finset (Finset (Fin 4))).erase (∅ : Finset (Fin 4)) := by
    rw [Finset.mem_erase]
    exact ⟨empty_ne_univ_fin4.symm, Finset.mem_univ _⟩
  rw [Finset.card_erase_of_mem h2, Finset.card_erase_of_mem h1]
  rw [show (Finset.univ : Finset (Finset (Fin 4))).card = 16 from card_univ_finset_fin4]

/-! ## §0. 「非空真子集」型与两条互逆映射 -/

/-- **非空真子集**型（有序口径下与 `Split (Fin 4)` 双射）。 -/
def NonemptyProper := {S : Finset (Fin 4) // S.Nonempty ∧ S ≠ Finset.univ}

instance instFintypeNonemptyProper : Fintype NonemptyProper :=
  Fintype.ofFinset
    (((Finset.univ : Finset (Finset (Fin 4))).erase ∅).erase
      (Finset.univ : Finset (Fin 4)))
    (by
      intro S
      show S ∈ (((Finset.univ : Finset (Finset (Fin 4))).erase ∅).erase
        (Finset.univ : Finset (Fin 4))) ↔ S.Nonempty ∧ S ≠ Finset.univ
      simp only [Finset.mem_erase, Finset.mem_univ, and_true]
      constructor
      · rintro ⟨hnu, hne⟩
        exact ⟨Finset.nonempty_iff_ne_empty.mpr hne, hnu⟩
      · rintro ⟨hne, hnu⟩
        exact ⟨hnu, Finset.nonempty_iff_ne_empty.mp hne⟩)

/-- `Split (Fin 4)` ⟶ 非空真子集（取 `sideA`）。

`sideA ≠ univ`：若 `sideA = univ`，则 `sideB` 的元素既在 `sideB` 又在 `sideA`，
与 `Split.disjoint_sides` 及 `sideB.Nonempty` 矛盾。 -/
def toSubset (s : Split (Fin 4)) : NonemptyProper :=
  ⟨s.sideA, s.nonempty 0, fun h => by
    obtain ⟨y, hy⟩ := s.nonempty 1
    exact (Finset.disjoint_left.mp (Split.disjoint_sides s) (h ▸ Finset.mem_univ y)) hy⟩

/-- 非空真子集 ⟶ `Split (Fin 4)`（`Phylo.splitOf`）。 -/
def ofSubset (T : NonemptyProper) : Split (Fin 4) :=
  Phylo.splitOf T.1 T.2.1 (Phylo.compl_nonempty_of_ne_univ T.2.2)

theorem toSubset_ofSubset (T : NonemptyProper) : toSubset (ofSubset T) = T := by
  have h : (ofSubset T).sideA = T.1 := Phylo.splitOf_sideA T.1 T.2.1 _
  exact Subtype.ext h

theorem ofSubset_toSubset (s : Split (Fin 4)) : ofSubset (toSubset s) = s := by
  apply Phylo.Stat.CASTERTopoSplit.eq_of_sideA_eq
  simp only [ofSubset, toSubset, Phylo.splitOf_sideA]

theorem toSubset_bijective : Function.Bijective toSubset :=
  ⟨fun a b h => by rw [← ofSubset_toSubset a, ← ofSubset_toSubset b, h],
   fun T => ⟨ofSubset T, toSubset_ofSubset T⟩⟩

/-- ★★★ **主目标**：`Split (Fin 4)` 在**有序**口径下恰有 **`14`** 个元素。 -/
theorem card_splits_fin4 : Fintype.card (Split (Fin 4)) = 14 := by
  rw [Fintype.card_congr (Equiv.ofBijective toSubset toSubset_bijective)]
  exact card_erase_erase

/-! ## §1. 三类分解 -/

/-- `2|2` 族（有序口径：`sideA` 基数 `2`）。 -/
def twoTwoFamily : Finset (Split (Fin 4)) :=
  Finset.univ.filter (fun r : Split (Fin 4) => r.sideA.card = 2)

/-- `1|3` 族（含两朝向）：`sideA` 基数 `1` 或 `3`。 -/
def oneThreeFamily : Finset (Split (Fin 4)) :=
  Finset.univ.filter (fun r : Split (Fin 4) => r.sideA.card = 1 ∨ r.sideA.card = 3)

/-- 两侧基数之和 = `4`。 -/
theorem card_sideA_add_card_sideB (s : Split (Fin 4)) :
    s.sideA.card + s.sideB.card = 4 := by
  rw [Phylo.Stat.CASTERTopoSplit.card_sideA_add_card_sideB s, Fintype.card_fin]

/-- `Fin 4` 上有向 split 的 `sideA` 基数**只能是** `1`、`2`、`3`。 -/
theorem card_sideA_cases (s : Split (Fin 4)) :
    s.sideA.card = 1 ∨ s.sideA.card = 2 ∨ s.sideA.card = 3 := by
  have h := card_sideA_add_card_sideB s
  have hb : 0 < s.sideB.card := Finset.card_pos.mpr (s.nonempty 1)
  have ha : 0 < s.sideA.card := Finset.card_pos.mpr (s.nonempty 0)
  omega

/-- 互补谓词的两个 `filter` 基数相加 = 全集基数。 -/
theorem card_filter_add_card_filter_not' {β : Type*} [Fintype β] (p : β → Prop)
    [DecidablePred p] :
    (Finset.univ.filter p).card + (Finset.univ.filter (fun b => ¬ p b)).card
      = Fintype.card β := by
  rw [show (Finset.univ.filter (fun b : β => ¬ p b))
      = {b ∈ (Finset.univ : Finset β) | ¬ p b} from rfl]
  rw [Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset β)) p,
    Finset.card_univ]

/-- ★★ **`2|2` 族恰 `6` 个**：`sideA` 与 `(univ : Finset (Fin 4)).powersetCard 2` 双射
（与 `MSCProof.card_splits_two` 是**同一个**双射）。 -/
theorem card_two_two : (twoTwoFamily).card
    = ((Finset.univ : Finset (Fin 4)).powersetCard 2).card := by
  rw [← Finset.card_image_of_injOn (f := fun r : Split (Fin 4) => r.sideA)]
  · congr 1
    ext T
    rw [Finset.mem_image, Finset.mem_powersetCard]
    constructor
    · rintro ⟨r, hr, rfl⟩
      rw [twoTwoFamily, Finset.mem_filter] at hr
      exact ⟨Finset.subset_univ _, hr.2⟩
    · rintro ⟨hsub, hcard⟩
      have h1 : T.Nonempty := Finset.card_pos.mp (by omega)
      have h2 : Tᶜ.Nonempty := Phylo.compl_nonempty_of_ne_univ (by
        intro hT
        rw [hT, Finset.card_univ, Fintype.card_fin] at hcard
        omega)
      refine ⟨Phylo.splitOf T h1 h2, ?_, Phylo.splitOf_sideA T h1 h2⟩
      rw [twoTwoFamily, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by rw [Phylo.splitOf_sideA]; exact hcard⟩
  · intro a _ b _ h
    exact Phylo.Stat.CASTERTopoSplit.eq_of_sideA_eq h

/-- ★★ **`2|2` 族 `= 6`**（`C(4,2) = 6`）。 -/
theorem card_two_two_eq : (twoTwoFamily).card = 6 := by
  rw [card_two_two, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  decide

/-- ★★ **`1|3` 族（含两朝向）恰 `8` 个**（`14 − 6`）。 -/
theorem card_one_three : (oneThreeFamily).card = 8 := by
  have hsub : twoTwoFamily ⊆ (Finset.univ : Finset (Split (Fin 4))) :=
    fun _ _ => Finset.mem_univ _
  have hone : oneThreeFamily
      = (Finset.univ : Finset (Split (Fin 4))) \ twoTwoFamily := by
    ext r
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, oneThreeFamily,
      Finset.mem_filter, twoTwoFamily]
    constructor
    · rintro (h | h) <;> omega
    · intro h
      rcases card_sideA_cases r with h1 | h2 | h3
      · exact Or.inl h1
      · exact absurd h2 h
      · exact Or.inr h3
  rw [hone, Finset.card_sdiff, Finset.inter_comm, Finset.inter_eq_right.mpr hsub,
    card_two_two_eq, Finset.card_univ, card_splits_fin4]

/-- ★★★ **分解**：`#(2|2) + #(1|3) = #(Split (Fin 4))`。 -/
theorem card_splits_fin4_decomposition :
    (twoTwoFamily).card + (oneThreeFamily).card = Fintype.card (Split (Fin 4)) := by
  rw [card_two_two_eq, card_one_three, card_splits_fin4]

/-- ★★★ **逐字数值形式**：`6 + 8 = 14`。 -/
theorem six_add_eight : (6 : ℕ) + 8 = 14 := by norm_num

/-- ★★★ **主目标（数值 + 分解一次性）**。 -/
theorem card_splits_fin4_sum :
    (twoTwoFamily).card = 6 ∧ (oneThreeFamily).card = 8 ∧
      Fintype.card (Split (Fin 4)) = 14 :=
  ⟨card_two_two_eq, card_one_three, card_splits_fin4⟩

/-! ## §2. 可计算的枚举代理（`Split (Fin 4)` 的 `Fintype` 非可计算） -/

/-- **可计算代理**：`Fin 4` 的**非空真子集**数（= 有序 split 数）。 -/
def nonemptyProperCount : ℕ :=
  (((Finset.univ : Finset (Fin 4)).powerset.erase ∅).erase
    (Finset.univ : Finset (Fin 4))).card

/-- **可计算代理**：`2|2` 的（有向）split 数（= `card = 2` 的子集数）。 -/
def twoTwoCount : ℕ := ((Finset.univ : Finset (Fin 4)).powersetCard 2).card

theorem nonemptyProperCount_eq : nonemptyProperCount = 14 := by
  show (((Finset.univ : Finset (Finset (Fin 4))).erase ∅).erase
    (Finset.univ : Finset (Fin 4))).card = 14
  exact card_erase_erase

theorem twoTwoCount_eq : twoTwoCount = 6 := by
  show ((Finset.univ : Finset (Fin 4)).powersetCard 2).card = 6
  rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  decide

end Phylo.Stat.SplitFin4Count
