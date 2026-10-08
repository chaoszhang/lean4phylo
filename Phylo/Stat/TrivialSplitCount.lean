/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.Stat.SplitProbabilities

/-!
# `Phylo.Stat.TrivialSplitCount` —— `Split (Fin n)` 上**平凡 split 的计数**（补证缺口 G1）

## 1. 要证什么（`SplitProbabilities` 文件头 §5「缺口 G1」）

`Split α = KPartition α 2` 用 `Fin 2` 把两侧**有序化**（`sideA = parts 0`、`sideB = parts 1`，
`Phylo/Split.lean` 第 210–220 行），所以一个**无向** split 在本库对应 `r` 与 `r.swap` **两个**值
（`SplitProbabilities` 文件头 §3）。于是 ADR2017 第 355–357 行的「`X` 有 `n` 个平凡 split」
在本库的**有向**口径下是 `2n` 个 —— 这正是 `Phylo.Stat.SplitProbabilities.card_trivial_splits_gap`
登记的缺口（原为**未证**）。本文件补上它，并把缺口 G1 的 `Prop` 本身**证成定理**
（`card_trivial_splits_gap_holds`）。

## 2. 手法（照 `MSCProof` §6 的 `card_splits_two`）

`r ↦ r.sideA` 把「`sideA` 单点」的 split 与 `(Finset.univ : Finset (Fin n)).powersetCard 1`
**双射**：

* **单射** —— `CASTERTopoSplit.eq_of_sideA_eq`（`sideA` 与 `sideB = sideAᶜ` 决定 `parts`）；
* **满射** —— `Phylo.splitOf A hA hAc`：`A.card = 1` ⇒ `A` 非空；`A ≠ univ` 由 `2 ≤ n` 保证
  （`Phylo.compl_nonempty_of_ne_univ`）。

故 `card = (univ.powersetCard 1).card = n.choose 1 = n`。`sideB` 那一半用 `r ↦ r.swap`
（`Split.swap_sideA` 把 `sideA`/`sideB` 对调，`Split.swap_swap` 给出对合 ⇒ 单射）搬过来。
合并用 `Finset.filter_or` + `Finset.card_union_of_disjoint`：两支**不交**是因为
`CASTERTopoSplit.card_sideA_add_card_sideB` 说两侧基数之和 `= n`，若两支都是单点则 `n = 2`，
与 `3 ≤ n` 矛盾 —— **这正是假设 `3 ≤ n` 的来源**（`n = 2` 时 `Split (Fin 2)` 只有 `2 < 4` 个
元素，见 §4 的可计算复核）。

## 3. 诚实边界

* 本文件**只**做计数（缺口 G1）。文件头 §3 的**记账桥**与缺口 G2/G3 **不在**本文件范围内。
* `3 ≤ n` 是**充分**条件，不是在参数全空间上的必要刻画：
  `n = 2` 时左端 `2`、右端 `4`（两支**重合**，正是 §3 用 `disjoint` 的地方失效）；
  `n = 1` 时 `Split (Fin 1)` **为空**（两个非空块无法覆盖单点集）⇒ 左端 `0`、右端 `2`；
  `n = 0` 时两端**都是** `0`（空情形下公式平凡成立）。
  故主定理带假设 `3 ≤ n`；两条分半计数 `card_sideA_one` / `card_sideB_one` 只需要 `2 ≤ n`。
  本文件**不**声称 `3 ≤ n` 是必要的。
* 零 `sorry` / 零 `axiom` / 零新公理；**不新增** Mathlib import（只 import 库内文件）。
-/

noncomputable section

open Classical

namespace Phylo.Stat.TrivialSplitCount

variable {n : ℕ}

/-! ## 0. 两个「单点侧」族 -/

/-- `sideA` 单点的 split 族。 -/
def sideAOneFamily (n : ℕ) : Finset (Split (Fin n)) :=
  (Finset.univ : Finset (Split (Fin n))).filter (fun r => r.sideA.card = 1)

/-- `sideB` 单点的 split 族。 -/
def sideBOneFamily (n : ℕ) : Finset (Split (Fin n)) :=
  (Finset.univ : Finset (Split (Fin n))).filter (fun r => r.sideB.card = 1)

/-- 平凡 split 族（**有向**口径：`sideA` 或 `sideB` 单点）。 -/
def trivialFamily (n : ℕ) : Finset (Split (Fin n)) :=
  (Finset.univ : Finset (Split (Fin n))).filter
    (fun r => r.sideA.card = 1 ∨ r.sideB.card = 1)

/-! ## 1. ★★ `sideA` 单点的 split 恰 `n` 个 -/

/-- ★★ **`sideA` 单点的（有向）split 恰 `n` 个**（`n ≥ 2`）。

`r ↦ r.sideA` 与 `(Finset.univ : Finset (Fin n)).powersetCard 1` 双射。 -/
theorem card_sideA_one (n : ℕ) (hn : 2 ≤ n) : (sideAOneFamily n).card = n := by
  set s : Finset (Split (Fin n)) := sideAOneFamily n with hs
  have hinj : Set.InjOn (fun r : Split (Fin n) => r.sideA) ↑s := by
    intro r1 _ r2 _ h
    exact Phylo.Stat.CASTERTopoSplit.eq_of_sideA_eq h
  have hcard : s.card = ((Finset.univ : Finset (Fin n)).powersetCard 1).card := by
    rw [← Finset.card_image_of_injOn hinj]
    congr 1
    ext T
    constructor
    · intro hT
      obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hT
      rw [hs] at hr
      simp only [sideAOneFamily, Finset.mem_filter, Finset.mem_univ, true_and] at hr
      rw [Finset.mem_powersetCard]
      exact ⟨Finset.subset_univ r.sideA, hr⟩
    · intro hT
      rw [Finset.mem_powersetCard] at hT
      obtain ⟨-, hcardT⟩ := hT
      have h1 : T.Nonempty := Finset.card_pos.mp (by omega)
      have h2 : Tᶜ.Nonempty := by
        apply Phylo.compl_nonempty_of_ne_univ
        intro hTuniv
        rw [hTuniv, Finset.card_univ, Fintype.card_fin] at hcardT
        omega
      refine Finset.mem_image.mpr ⟨Phylo.splitOf T h1 h2, ?_, ?_⟩
      · rw [hs]
        simp only [sideAOneFamily, Finset.mem_filter, Finset.mem_univ, true_and,
          Phylo.splitOf_sideA]
        exact hcardT
      · simp only [Phylo.splitOf_sideA]
  rw [hs] at hcard ⊢
  rw [hcard, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin, Nat.choose_one_right]

/-! ## 2. ★★ `sideB` 单点的 split 恰 `n` 个 -/

/-- ★★ **`sideB` 单点的（有向）split 恰 `n` 个**（`n ≥ 2`）。

由 `r ↦ r.swap` 把第 1 条搬过来（`Split.swap_sideA` 对调两侧，`Split.swap_swap` 是对合）。 -/
theorem card_sideB_one (n : ℕ) (hn : 2 ≤ n) : (sideBOneFamily n).card = n := by
  have himg : sideBOneFamily n = (sideAOneFamily n).image Split.swap := by
    ext r
    simp only [sideBOneFamily, sideAOneFamily, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_image]
    constructor
    · intro hr
      exact ⟨r.swap, by simpa using hr, by simp⟩
    · rintro ⟨q, hq, rfl⟩
      simpa using hq
  rw [himg, Finset.card_image_of_injective _ Split.swap_injective, card_sideA_one n hn]

/-! ## 3. ★★★ 两支不交 ⟹ 主定理 -/

/-- ★★ 两支**不交**（`n ≥ 3`）：若两侧基数都 `= 1`，则 `card_sideA_add_card_sideB` 给出 `n = 2`。 -/
theorem disjoint_sideAOne_sideBOne (n : ℕ) (hn : 3 ≤ n) :
    Disjoint (sideAOneFamily n) (sideBOneFamily n) := by
  rw [Finset.disjoint_left]
  intro r hr hr'
  rw [sideAOneFamily, Finset.mem_filter] at hr
  rw [sideBOneFamily, Finset.mem_filter] at hr'
  have h := Phylo.Stat.CASTERTopoSplit.card_sideA_add_card_sideB r
  have hc : Fintype.card (Fin n) = n := Fintype.card_fin n
  omega

/-- ★★★ **主目标**：`Split (Fin n)`（**有向**口径）里平凡 split 恰有 `2n` 个（`n ≥ 3`）。

平凡 = 某一侧的基数为 `1`。每个无向平凡 split `{x} | X∖{x}` 在有序口径下计两次
（`r` 与 `r.swap`），故是 `2n` 而不是 `n`。 -/
theorem card_trivial_splits (n : ℕ) (hn : 3 ≤ n) : (trivialFamily n).card = 2 * n := by
  have hdisj := disjoint_sideAOne_sideBOne n hn
  have hunion : trivialFamily n = sideAOneFamily n ∪ sideBOneFamily n := by
    rw [trivialFamily, sideAOneFamily, sideBOneFamily, Finset.filter_or]
  rw [hunion, Finset.card_union_of_disjoint hdisj, card_sideA_one n (by omega),
    card_sideB_one n (by omega)]
  omega

/-- ★★★ 主目标的**逐字形式**（谓词内联，与登记缺口 `card_trivial_splits_gap` 的措辞一致）。 -/
theorem card_trivial_splits' (n : ℕ) (hn : 3 ≤ n) :
    ((Finset.univ : Finset (Split (Fin n))).filter
        (fun r => r.sideA.card = 1 ∨ r.sideB.card = 1)).card = 2 * n :=
  card_trivial_splits n hn

/-- ★★★ **缺口 G1 闭合**：`Phylo.Stat.SplitProbabilities.card_trivial_splits_gap`
（登记为「未证」的 `Prop`）**成立**。 -/
theorem card_trivial_splits_gap_holds : Phylo.Stat.SplitProbabilities.card_trivial_splits_gap := by
  intro n hn
  -- ⚠️ 两个 `filter` 的**谓词**是同一件事，但 `DecidablePred` 实例的**项**不同
  -- （一个是 `IsTrivialSplit` 的、一个是内联析取的），故不能直接 `exact`；
  -- 用 `Finset.filter_congr_decidable`（`Finset.ext` + `mem_filter` 在这版 Mathlib 上不够）。
  have h : (Finset.univ.filter
        (fun r : Split (Fin n) => Phylo.Stat.SplitProbabilities.IsTrivialSplit r))
      = (Finset.univ.filter
        (fun r : Split (Fin n) => r.sideA.card = 1 ∨ r.sideB.card = 1)) := by
    simp only [Phylo.Stat.SplitProbabilities.IsTrivialSplit]
    exact Finset.filter_congr_decidable _ _ _
  rw [h]
  exact card_trivial_splits n hn

/-! ## 4. 数值/穷举复核（**可计算代理**，`n = 2…6`）

⚠️ `Split (Fin n)` 的 `Fintype` 来自 `Fintype.ofInjective`（`Phylo/Split.lean` 第 194–197 行），
**非可计算**，故 `decide` 无法枚举它（这正是缺口 G1 当年没被 `decide` 掉的原因）。

但「**有序** split ↔ 非空真子集 `A`」（`A = sideA`，`B = Aᶜ`）是双射，而 `Finset (Fin n)`
的枚举**可计算**，于是下面的代理函数可以 `decide`。它是**独立于 §1–§3 证明路线**的数值复核
（脚本版另见 `scripts/msc/trivial_split_count.py`）。 -/

/-- **可计算代理**：有序 split `A | Aᶜ` 中**平凡者**的计数（`A` 就是 `sideA`）。 -/
def trivialSplitCountComputable (n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Finset (Fin n))).filter
    (fun A => A.Nonempty ∧ Aᶜ.Nonempty ∧ (A.card = 1 ∨ Aᶜ.card = 1))).card

-- `n = 2`：两侧都是单点，两支**重叠** ⇒ `2`，**不是** `2n = 4`（故主定理需要 `3 ≤ n`）。
example : trivialSplitCountComputable 2 = 2 := by decide

-- `n = 3…6`：与 `card_trivial_splits` 的 `2n` 逐一吻合。
example : trivialSplitCountComputable 3 = 6 := by decide
example : trivialSplitCountComputable 4 = 8 := by decide
example : trivialSplitCountComputable 5 = 10 := by decide
example : trivialSplitCountComputable 6 = 12 := by decide

/-- ★★ `n = 4` 的实例（`2 * 4 = 8`）：`Split (Fin 4)` 的 14 个有向 split 中
`8` 个是 `1|3`、`6` 个是 `2|2`（后者见 `MSCProof.card_splits_two` 的 `↥univ` 口径）。 -/
theorem card_trivial_splits_four : (trivialFamily 4).card = 8 :=
  card_trivial_splits 4 (by norm_num)

end Phylo.Stat.TrivialSplitCount
