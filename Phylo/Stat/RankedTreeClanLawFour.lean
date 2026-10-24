/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.Stat.RankedTreeCladogram
import Phylo.Stat.ReciprocalMonophyly

/-!
# `Phylo.Stat.RankedTreeClanLawFour` —— `n = 4` 的端到端**对齐**

`Phylo/Stat/RankedTreeCladogram.lean` 造出了 ★★★ M3 `tree` 槽
`rankedTreeCladogram : RankedTree n → Cladogram (Fin n)`，并在 `n = 4` 上算出
`clanEvent 4 A`（`Ω = RankedTree 4` 的 **18 条**合并史、`prob ≡ 1/H 4 = 1/18`）。

本文件把它**接到闭形式**：

```
clanEvent 4 A = clanProb 4 A.card                （A 非空、A.card < 4）
clanEvent 4 A = MSCTreeLaw.clanEvent yhkLawFour A （同一条律，两个载体一致）
```

* `A.card = 2`：`6 / 18 = 1/3 = clanProb 4 2`（★★ `clanEvent_four_two`、
  ★★ `clanProb_four_two`、★★★ `yhkLawFour_clanEvent_two`）；
* `A.card = 1, 3`：`1 = clanProb 4 1 = clanProb 4 3`（必然事件，
  ★★ `clanEvent_four_trivial`、★ `clanProb_one`、★ `clanProb_pred`、
  ★★★ `MSCTreeLaw.clanEvent_eq_clanProb_of_trivial_card`）。

即 **W26 的 `yhkLawFour`（`Ω = Fin 3`、三棵 quartet 树等权 `1/3`）与 `RankedTree 4`
上的真实诱导律是同一个数**——「三棵拓扑各 6 条」就是 `1/3` 的来源。
-/

namespace Phylo.Stat.RankedTreeClanLawFour

open Phylo.Stat.RankedTreeCladogram
open Phylo.Stat.ReciprocalMonophyly
open Phylo.Stat.RankedGeneTree

/-- ★★ **`n = 4`、基数 `2`：`clanProb 4 2` 一侧的桥**（`1/3 = 1/3`，两处闭形式的对照）。 -/
theorem clanProb_four_two_eq : clanProb 4 2 = 1 / 3 := clanProb_four_two

/-- ★★★ **真实载体版**：`Ω = RankedTree 4`、`prob ≡ 1/H 4`、`tree = rankedTreeCladogram 4`
时，非空真子集 `A` 的 clan 事件概率 **就是** `clanProb 4 |A|`。 -/
theorem clanEvent_four_eq_clanProb (A : Finset (Fin 4)) (hA : A.Nonempty) (hlt : A.card < 4) :
    clanEvent 4 (by norm_num) A = clanProb 4 A.card := by
  have hpos : 1 ≤ A.card := Finset.card_pos.mpr hA
  by_cases h2 : A.card = 2
  · rw [clanEvent_four_two A h2, h2, clanProb_four_two]
  · have htriv : A.card = 1 ∨ A.card = 3 := by omega
    rw [clanEvent_four_trivial A htriv]
    rcases htriv with h1 | h3
    · rw [h1, clanProb_one (by norm_num)]
    · rw [h3, clanProb_pred (by norm_num)]

/-- ★★★ **与 `yhkLawFour` 对齐**：同一 `n = 4` 上，`RankedTree 4` 上的真实诱导律
与 W26 造的 `MSCTreeLaw` 实例 `yhkLawFour`（`Ω = Fin 3`、三棵 quartet 树等权）给出**相同**的
clan 事件概率。 -/
theorem clanEvent_four_eq_yhkLawFour (A : Finset (Fin 4)) (hA : A.Nonempty)
    (hlt : A.card < 4) :
    clanEvent 4 (by norm_num) A = MSCTreeLaw.clanEvent yhkLawFour A := by
  have hpos : 1 ≤ A.card := Finset.card_pos.mpr hA
  by_cases h2 : A.card = 2
  · rw [clanEvent_four_eq_clanProb A hA hlt, yhkLawFour_clanEvent_two A h2]
  · have htriv : A.card = 1 ∨ A.card = 3 := by omega
    rw [clanEvent_four_eq_clanProb A hA hlt,
      MSCTreeLaw.clanEvent_eq_clanProb_of_trivial_card (n := 4) (L := yhkLawFour)
        (by norm_num) A htriv]

end Phylo.Stat.RankedTreeClanLawFour
