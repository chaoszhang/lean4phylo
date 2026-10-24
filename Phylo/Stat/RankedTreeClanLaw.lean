/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.Stat.RankedTreeCladogram
import Phylo.Stat.ReciprocalMonophyly

/-!
# `Phylo.Stat.RankedTreeClanLaw` —— `Ω = RankedTree n` 上的 clan 律：**条件装配**（`_of_`）

★★★ M3 `tree` 槽（`RankedTreeCladogram.lean`）已把 `YHKClanLawGap` 的左端写成**具名事件**

```
clanEvent n hn A = ∑_{ω : A 是 clan 的合并史} 1 / H n
```

★★★ `mem_clanHistories_iff_of_card` 又把非平凡基数（`2 ≤ |A| ≤ n−2`）上的事件压成
`A ∈ blockFamily n ω ∨ Aᶜ ∈ blockFamily n ω`；于是（★★★ `card_clanHistories_eq`）

```
#{A 是 clan} = #{A 是块} + #{Aᶜ 是块} − #{A 与 Aᶜ 同时是块}
```

本文件把最后一步接上：只要两件**计数闭形式**成立，

* **块计数**：`#{ω : A 是块} = H n · pn n (|A|)`（`|A| = a`）；
* **交项计数**：`#{ω : A 与 Aᶜ 同时是块} = H n · pnHatExh n a`
  （★ 注意是 **`pnHatExh`**（Lemma 4.3 的穷尽式 `2/((n−1)·C(n,a))`），**不是** `pnHat`
  —— 后者是 Lemma 4.4 的一般式，`b = n − a` 时**不**等于 Lemma 4.3，见
  `ReciprocalMonophyly.lean` §3 与 `pnHat_eq_pn_mul`（要求 `a + b < n`））；

则 ★★★ `clanEvent n hn A = clanProb n A.card`（用库内 ★★★ `clanProb_eq_inclusionExclusion`，
`ReciprocalMonophyly.lean:404`，**不重证代数**）。

⚠️ 命名：本文件给的是**条件形式**（后缀 `_of_`），**不是** `_holds` —— 块计数由泳道 b 的
`ArithStep` 收口后，最后一行装配才叫 `_holds`。
-/

namespace Phylo.Stat.RankedTreeClanLaw

open Phylo.Stat.RankedTreeCladogram
open Phylo.Stat.ReciprocalMonophyly
open Phylo.Stat.CoalescentHistoryCount

/-- ★★ **`H n > 0`**（`n ≥ 2`）：`H n = Hnat n`（★★ `cast_Hnat`），而
`Hnat n = ∏_{k=2}^{n} C(k,2)`（★★ `Hnat_eq_prod`）逐项正。 -/
theorem H_pos (n : ℕ) : 0 < RankedGeneTree.H n := by
  rw [← cast_Hnat n]
  have h : 0 < Hnat n := by
    rw [Hnat_eq_prod]
    refine Finset.prod_pos (fun k _ => ?_)
    exact Nat.choose_pos (by omega : 2 ≤ k + 2)
  exact_mod_cast h

/-- ★★★ **条件装配**（`_of_`）：两件计数闭形式 ⟹ `clanEvent n hn A = clanProb n A.card`。

* `hblk` —— 块计数：`#{ω : B 是块} = H n · pn n (|B|)`（对 `2 ≤ |B| ≤ n−2` 的 `B`）；
* `hinter` —— 交项计数：`#{ω : A 与 Aᶜ 同时是块} = H n · pnHatExh n (|A|)`。

★ 证明只做三件**计数层**的事（基数包含-排除、`∑ 1/H = card/H`、代入），
代数恒等式 `pn(a) + pn(n−a) − pnHatExh(a) = clanProb n a` 直接引用库内定理。 -/
theorem clanEvent_eq_clanProb_of_blockCount {n : ℕ} (hn : 2 ≤ n) (h3 : 3 ≤ n)
    {A : Finset (Fin n)} (h1 : 2 ≤ A.card) (h2 : A.card ≤ n - 2)
    (hblk : ∀ B : Finset (Fin n), 2 ≤ B.card → B.card ≤ n - 2 →
      ((blockHistories n B).card : ℝ) = RankedGeneTree.H n * pn n B.card)
    (hinter : ((blockHistories n A ∩ blockHistories n Aᶜ).card : ℝ) =
      RankedGeneTree.H n * pnHatExh n A.card) :
    clanEvent n hn A = clanProb n A.card := by
  -- `Aᶜ` 也满足块计数的前提（`|Aᶜ| = n − |A|`）
  have hcompl : Aᶜ.card = n - A.card := card_compl_eq n A
  have h1c : 2 ≤ Aᶜ.card := by rw [hcompl]; omega
  have h2c : Aᶜ.card ≤ n - 2 := by rw [hcompl]; omega
  have hb : ((blockHistories n A).card : ℝ) = RankedGeneTree.H n * pn n A.card := hblk A h1 h2
  have hbc : ((blockHistories n Aᶜ).card : ℝ) = RankedGeneTree.H n * pn n (n - A.card) := by
    have h := hblk Aᶜ h1c h2c
    rwa [hcompl] at h
  -- 基数层的包含-排除（ℝ 上，加法形式；避免 `Nat` 减法的侧条件）
  have hci : ((clanHistories n hn A).card : ℝ)
      + ((blockHistories n A ∩ blockHistories n Aᶜ).card : ℝ)
      = ((blockHistories n A).card : ℝ) + ((blockHistories n Aᶜ).card : ℝ) := by
    have hset : clanHistories n hn A = blockHistories n A ∪ blockHistories n Aᶜ := by
      ext ω
      rw [mem_clanHistories_iff_of_card hn h3 h1 h2 ω]
      simp only [mem_blockHistories, Finset.mem_union]
    have h := Finset.card_union_add_card_inter (blockHistories n A) (blockHistories n Aᶜ)
    rw [hset]
    exact_mod_cast h
  -- 求和 = 基数 · (1 / H n)
  have hH : RankedGeneTree.H n ≠ 0 := ne_of_gt (H_pos n)
  have hsum : clanEvent n hn A
      = ((clanHistories n hn A).card : ℝ) * (1 / RankedGeneTree.H n) := by
    unfold clanEvent
    rw [Finset.sum_const, nsmul_eq_mul]
  -- 代入三件计数（加法形式，纯线性）
  have hcard : ((clanHistories n hn A).card : ℝ)
      = RankedGeneTree.H n * pn n A.card + RankedGeneTree.H n * pn n (n - A.card)
        - RankedGeneTree.H n * pnHatExh n A.card := by
    linarith
  have hcard' : ((clanHistories n hn A).card : ℝ)
      = RankedGeneTree.H n * (pn n A.card + pn n (n - A.card) - pnHatExh n A.card) := by
    rw [hcard]; ring
  rw [hsum, hcard',
    clanProb_eq_inclusionExclusion (n := n) (a := A.card) (by omega) (by omega)]
  have hX : RankedGeneTree.H n * (pn n A.card + pn n (n - A.card) - pnHatExh n A.card)
      * (1 / RankedGeneTree.H n)
      = pn n A.card + pn n (n - A.card) - pnHatExh n A.card := by
    field_simp
  exact hX

end Phylo.Stat.RankedTreeClanLaw
