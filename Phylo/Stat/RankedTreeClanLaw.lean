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

/-! ## 3. 交项计数：`n = 4` 的**内核核过**实例

任务（一般 `n`）是 `#{ω : A 与 Aᶜ 同时是块} = H n · pnHatExh n |A|`
（⟺ 根分裂恰为 `A | Aᶜ` ⟺ 最后一次合并把 `A` 与 `Aᶜ` 并起来）。
一般 `n` 的组合计数**本批未完成**（见报告 §卡点）；这里落 `n = 4` 的实例，
它正是 `H_2·H_2·C(2,1) = 2` 与 `H 4 · pnHatExh 4 2 = 18 · (1/9) = 2` 的**数值锚点**，
同时也是「必须用 `pnHatExh` 而不是 `pnHat`」的机器证据（后者给 `2/45`，乘 `H 4` 是 `4/5`）。 -/

/-- ★ **`pnHatExh 4 2 = 1/9`**（Lemma 4.3 的穷尽式；对比 `pnHat 4 2 2 = 2/45`，后者**不对**）。 -/
theorem pnHatExh_four_two : pnHatExh 4 2 = 1 / 9 := by
  norm_num [pnHatExh, Nat.choose]

/-- ★★ **`n = 4` 的交项：`pnHat 4 2 2 = 2/45`，乘 `H 4` 给 `4/5 ≠ 2`**（★D 的机器留痕）。 -/
theorem H_four_mul_pnHat_four_two : RankedGeneTree.H 4 * pnHat 4 2 2 = 4 / 5 := by
  rw [RankedGeneTree.H_four, pnHat]
  norm_num

set_option maxRecDepth 100000 in
/-- ★★★ **闭式计数（内核规约）**：`Fin 4` 的每个二元子集 `A`，``H 4 = 18`` 条合并史中恰有
**2** 条使 `A` 与 `Aᶜ` **同时**是非单点块（＝根分裂恰为 `A | Aᶜ` 的那两条 balanced ranking）。 -/
theorem card_inter_blockFamily_four :
    ∀ A ∈ (Finset.univ : Finset (Finset (Fin 4))).filter (fun A => decide (A.card = 2) = true),
      ((Finset.univ : Finset (RankedGeneTree.RankedTree 4)).filter
        (fun ω => (decide (A ∈ blockFamily 4 ω) && decide (Aᶜ ∈ blockFamily 4 ω)) = true)).card
        = 2 := by
  decide

/-- ★★★ **`n = 4` 的交项计数 = `H 4 · pnHatExh 4 2`**（一般 `n` 的 `n = 4` 实例）。 -/
theorem card_blockHistories_inter_four (A : Finset (Fin 4)) (hA : A.card = 2) :
    ((blockHistories 4 A ∩ blockHistories 4 Aᶜ).card : ℝ)
      = RankedGeneTree.H 4 * pnHatExh 4 2 := by
  classical
  have hmem : A ∈ (Finset.univ : Finset (Finset (Fin 4))).filter
      (fun A => decide (A.card = 2) = true) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hA]
    rfl
  have hclosed := card_inter_blockFamily_four A hmem
  have hcongr : blockHistories 4 A ∩ blockHistories 4 Aᶜ
      = (Finset.univ : Finset (RankedGeneTree.RankedTree 4)).filter
        (fun ω => (decide (A ∈ blockFamily 4 ω) && decide (Aᶜ ∈ blockFamily 4 ω)) = true) := by
    rw [inter_blockHistories_eq]
    apply Finset.filter_congr
    intro ω _
    simp only [Bool.and_eq_true, decide_eq_true_eq]
  rw [hcongr, hclosed, pnHatExh_four_two, RankedGeneTree.H_four]
  norm_num

end Phylo.Stat.RankedTreeClanLaw
