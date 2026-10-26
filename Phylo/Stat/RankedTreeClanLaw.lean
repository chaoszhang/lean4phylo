/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.Stat.RankedTreeCladogram
import Phylo.Stat.ReciprocalMonophyly
import Phylo.Stat.CladeCount

/-!
# `Phylo.Stat.RankedTreeClanLaw` —— `Ω = RankedTree n` 上的 clan 律

## 0. 本文件干什么

★★★ M3 `tree` 槽（`RankedTreeCladogram.lean`）把 `YHKClanLawGap` 的左端写成**具名事件**

```
clanEvent n hn A = ∑_{ω : A 是 clan 的合并史} 1 / H n
```

★★★ `mem_clanHistories_iff_of_card` 又把非平凡基数（`2 ≤ |A| ≤ n−2`）上的事件压成
`A ∈ blockFamily n ω ∨ Aᶜ ∈ blockFamily n ω`；于是（★★★ `card_clanHistories_eq`）

```
#{A 是 clan} = #{A 是块} + #{Aᶜ 是块} − #{A 与 Aᶜ 同时是块}
```

其中**块计数**由泳道 b 的 ★★★ `CladeCount.cladeCount_univ` **无条件**给出（本文件
§2 把它从 `cladeCount` 的货币翻到 `blockHistories` 的货币），**交项计数**是唯一的具名缺件
`blockInterCount`。于是本文件的最强结论是 ★★★ `yhkClanLawGap_of_blockInterCount`：

```
blockInterCount  ⟹  YHKClanLawGap
```

★ **W32（2026-10-26）已收口**：`YHKClanLawGap` 现已由本文件末尾的 ★★★ `yhkClanLawGap_holds`（`Phylo/Stat/RankedTreeClanLaw.lean:1166`）无条件证成（`blockInterCount` 由 ★★★ `blockInterCount_holds`（`:1153`）收口）；上面「唯一的具名缺件」「本文件的最强结论是 `_of_`」描述的是当时的状态，保留作留痕。

## 1. 纪律

* `_of_` 命名（**不是** `_holds`）；缺件登记为 `def … : Prop`（`blockInterCount`），不用 `axiom`/`sorry`；
* 名字里**没有** `gap`/`Gap`（`blockInterCount` / `yhkClanLawGap_of_blockInterCount` 除外 ——
  后者是**缺口名的装配引理**，按派工书「`_of_`」规矩命名，台账不会记成收口）。

★ **W32（2026-10-26）已收口**：本文件末尾另有 ★★★ `yhkClanLawGap_holds`，`YHKClanLawGap` 已收口、台账已记「已收口」；上面「不是 `_holds` / 台账不会记成收口」描述的是当时的状态，保留作留痕。
-/

namespace Phylo.Stat.RankedTreeClanLaw

open Phylo.Stat.RankedTreeCladogram
open Phylo.Stat.ReciprocalMonophyly
open Phylo.Stat.CoalescentHistoryCount
open Phylo.Stat.CladeCount
open Classical

/-- ★★ **`H n > 0`**：`H n = Hnat n`（★★ `cast_Hnat`），而
`Hnat n = ∏_{k=2}^{n} C(k,2)`（★★ `Hnat_eq_prod`）逐项正。 -/
theorem H_pos (n : ℕ) : 0 < RankedGeneTree.H n := by
  rw [← cast_Hnat n]
  have h : 0 < Hnat n := by
    rw [Hnat_eq_prod]
    refine Finset.prod_pos (fun k _ => ?_)
    exact Nat.choose_pos (by omega : 2 ≤ k + 2)
  exact_mod_cast h

/-! ## 2b. 交项计数的两条形态之间的**纯算术桥**

组合计数自然会给出 `H a · H (n−a) · C(n−2, a−1)`（「`A` 与 `Aᶜ` 各自内部成树」×「内部结点
排序交错」），而闭形式侧是 `H n · pnHatExh n a`。两者**相等**：

```
H n · pnHatExh n a = H a · H (n−a) · C(n−2, a−1)      （2 ≤ a ≤ n−2）
```

证法：两边都用 `H_eq_factorial`（`H ℓ = ℓ!(ℓ−1)!/2^{ℓ−1}`）展开，
`(a+b−1)! = (a+b−1)·(a+b−2)!`、`2^{a+b−1} = 2·2^{a−1}·2^{b−1}`、
`C(m,k) = m!/(k!(m−k)!)`，两边都化成 `a!·b!·(n−2)!/2^{n−2}`。 -/

/-- `m.choose k` 的阶乘比形式（`k ≤ m`）：`C(m,k) = m!/(k!(m−k)!)`。 -/
theorem choose_eq_fact_div (m k : ℕ) (h : k ≤ m) :
    ((m.choose k : ℕ) : ℝ) = (m.factorial : ℝ) / ((k.factorial : ℝ) * ((m - k).factorial : ℝ)) := by
  have h1 : ((m.choose k : ℕ) : ℝ) * ((k.factorial : ℝ) * ((m - k).factorial : ℝ))
      = (m.factorial : ℝ) := by
    have := congrArg (fun x : ℕ => (x : ℝ)) (Nat.choose_mul_factorial_mul_factorial h)
    push_cast at this
    linear_combination this
  have hk : ((k.factorial : ℝ)) ≠ 0 := by
    have := Nat.factorial_pos k
    positivity
  have hmk : ((m - k).factorial : ℝ) ≠ 0 := by
    have := Nat.factorial_pos (m - k)
    positivity
  rw [eq_div_iff (mul_ne_zero hk hmk)]
  linarith [h1]

/-- ★★★ **算术桥（两变量版）**：`H (a+b) · pnHatExh (a+b) a = H a · H b · C(a+b−2, a−1)`。 -/
theorem H_mul_pnHatExh_eq' {a b : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b) :
    RankedGeneTree.H (a + b) * pnHatExh (a + b) a
      = RankedGeneTree.H a * RankedGeneTree.H b * (((a + b - 2).choose (a - 1) : ℕ) : ℝ) := by
  have ha1 : a ≤ a + b := by omega
  have h2 : a - 1 ≤ a + b - 2 := by omega
  have hsub : a + b - 2 - (a - 1) = b - 1 := by omega
  rw [RankedGeneTree.H_eq_factorial (a + b), RankedGeneTree.H_eq_factorial a,
    RankedGeneTree.H_eq_factorial b, pnHatExh,
    choose_eq_fact_div (a + b) a ha1, choose_eq_fact_div (a + b - 2) (a - 1) h2, hsub]
  rw [show a + b - a = b from by omega]
  rw [show ((a + b : ℕ) : ℝ) - 1 = ((a + b - 1 : ℕ) : ℝ) from by
    push_cast [Nat.cast_sub (by omega : 1 ≤ a + b)]
    norm_num]
  have hfac : ((a + b - 1).factorial : ℝ)
      = ((a + b - 1 : ℕ) : ℝ) * ((a + b - 2).factorial : ℝ) := by
    have h : a + b - 1 = (a + b - 2) + 1 := by omega
    rw [h, Nat.factorial_succ]
    push_cast
    ring
  have hpow : (2 : ℝ) ^ (a + b - 1) = 2 * ((2 : ℝ) ^ (a - 1) * (2 : ℝ) ^ (b - 1)) := by
    have h : a + b - 1 = (a - 1) + (b - 1) + 1 := by omega
    rw [h, pow_succ, pow_add]
    ring
  have hne : ((a + b - 1 : ℕ) : ℝ) ≠ 0 := by
    have h : (0 : ℕ) < a + b - 1 := by omega
    exact_mod_cast (ne_of_gt h)
  rw [hfac, hpow]
  field_simp

/-- ★★★ **算术桥**（`n, a` 形态）：`H n · pnHatExh n a = H a · H (n−a) · C(n−2, a−1)`，
`2 ≤ a ≤ n−2`。

⇒ 只要有人给出**组合计数** `#{ω : A 与 Aᶜ 同时是块} = H a · H (n−a) · C(n−2, a−1)`，
本定理立刻把它翻成 ★★★ `clanEvent_eq_clanProb_of_blockCount` 所需的
`hinter : … = H n · pnHatExh n A.card`。 -/
theorem H_mul_pnHatExh_eq {n a : ℕ} (h1 : 2 ≤ a) (h2 : a ≤ n - 2) :
    RankedGeneTree.H n * pnHatExh n a
      = RankedGeneTree.H a * RankedGeneTree.H (n - a) * (((n - 2).choose (a - 1) : ℕ) : ℝ) := by
  have hb : 2 ≤ n - a := by omega
  have hsub : a + (n - a) - 2 = n - 2 := by omega
  have hmain := H_mul_pnHatExh_eq' (a := a) (b := n - a) h1 hb
  rw [hsub] at hmain
  rw [show a + (n - a) = n from by omega] at hmain
  exact hmain

/-! ## 2c. 块计数：从泳道 b 的 `cladeCount` 货币翻到 `blockHistories` 货币

泳道 b 的 ★★★ `cladeCount_univ`（`CladeCount.lean`）**无条件**给出
`(cladeCount univ A : ℝ) = H n * pn n |A|`，其中 `cladeCount` 数的是
「`s`-相对合并史里 `A` 是 clade」的条数（`IsCladeH`）。本小节把它接到我们的
`blockHistories`（`RankedTree` 上的「`A` 是非单点块」）—— 两个 `Finset` 用
`Finset.card_bij`（双射：`ω ↦ ω.1`）对齐，谓词用 ★ `mem_blockFamily_iff_isCladeH` 翻译。 -/

/-- ★★ **块 ↔ `IsCladeH` 的翻译**（非平凡基数）：`A` 是 `ω` 的非单点块 ⟺
`A` 是 `ω` 的合并史（`s = univ`、`L ≤ n−1`）在某层的块。 -/
theorem mem_blockFamily_iff_isCladeH {n : ℕ} (ω : RankedGeneTree.RankedTree n)
    {A : Finset (Fin n)} (h1 : 2 ≤ A.card) (h2 : A.card ≤ n - 2) :
    A ∈ blockFamily n ω ↔ IsCladeH (Finset.univ : Finset (Fin n)) (n - 1) ω.1 A := by
  rw [mem_blockFamily, isCladeH_iff]
  constructor
  · rintro ⟨hc, -, -⟩
    rw [RankedGeneTree.cladesOf, Finset.mem_biUnion] at hc
    obtain ⟨L, hL, hAb⟩ := hc
    rw [Finset.mem_range] at hL
    rw [RankedGeneTree.blocksOf, Finset.mem_image] at hAb
    obtain ⟨w, -, hw⟩ := hAb
    refine ⟨L, by omega, w, ?_, ?_⟩
    · rw [← hw]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
    · rw [← hw]
      rfl
  · rintro ⟨L, hL, w, -, hw⟩
    refine ⟨?_, h1, h2⟩
    rw [RankedGeneTree.cladesOf, Finset.mem_biUnion]
    refine ⟨L, Finset.mem_range.mpr (by omega), ?_⟩
    rw [RankedGeneTree.blocksOf, Finset.mem_image]
    exact ⟨w, Finset.mem_univ _, by rw [hw]; rfl⟩

/-- ★★★ **块计数的货币兑换**：`#{ω : A ∈ blockFamily n ω} = cladeCountS (n−1) univ A`。 -/
theorem card_blockHistories_eq_cladeCountS (n : ℕ) {A : Finset (Fin n)}
    (h1 : 2 ≤ A.card) (h2 : A.card ≤ n - 2) :
    (blockHistories n A).card
      = cladeCountS (n - 1) (Finset.univ : Finset (Fin n)) A := by
  unfold blockHistories CladeCount.cladeCountS
  refine Finset.card_bij (fun ω (_ : ω ∈ (Finset.univ : Finset (RankedGeneTree.RankedTree n)).filter
    (fun ω => A ∈ blockFamily n ω)) => ω.1) ?_ ?_ ?_
  · intro ω hω
    obtain ⟨-, hpred⟩ := Finset.mem_filter.mp hω
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, (isMH_univ_iff n ω.1).mpr ω.2⟩,
        (mem_blockFamily_iff_isCladeH ω h1 h2).mp hpred⟩
  · intro ω₁ _ ω₂ _ heq
    exact Subtype.ext heq
  · intro f hf
    obtain ⟨hf1, hf2⟩ := Finset.mem_filter.mp hf
    refine ⟨⟨f, (isMH_univ_iff n f).mp (Finset.mem_filter.mp hf1).2⟩, ?_, rfl⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, (mem_blockFamily_iff_isCladeH _ h1 h2).mpr hf2⟩

/-- ★★★ **块计数（无条件）**：`#{ω : A 是非单点块} = H n · pn n |A|`（`2 ≤ |A| ≤ n−2`）。

由泳道 b 的 ★★★ `cladeCount_univ`（那里 `ArithStep` 已收口）＋ 上面的货币兑换。 -/
theorem card_blockHistories_univ (n : ℕ) {A : Finset (Fin n)}
    (h1 : 2 ≤ A.card) (h2 : A.card ≤ n - 2) :
    ((blockHistories n A).card : ℝ) = RankedGeneTree.H n * pn n A.card := by
  rw [card_blockHistories_eq_cladeCountS n h1 h2]
  have h := cladeCountS_eq_H_mul_pn (n - 1) n (Finset.univ : Finset (Fin n)) A
    (by rw [Finset.card_univ, Fintype.card_fin,
      Nat.sub_one_add_one_eq_of_pos (by omega : 0 < n)])
    (Finset.subset_univ _) (by omega) (by omega)
  rw [Nat.sub_one_add_one_eq_of_pos (by omega : 0 < n)] at h
  exact h

/-! ## 3. 条件装配（`_of_`） -/

/-- ★★★ **条件装配**（`_of_`）：块计数（本文件 §2c，**无条件**）＋ 交项计数
（`hinter`）⟹ `clanEvent n hn A = clanProb n A.card`。

★ 证明只做三件**计数层**的事（基数包含-排除、`∑ 1/H = card/H`、代入），
代数恒等式 `pn(a) + pn(n−a) − pnHatExh(a) = clanProb n a` 直接引用库内定理。 -/
theorem clanEvent_eq_clanProb_of_blockCount {n : ℕ} (hn : 2 ≤ n) (h3 : 3 ≤ n)
    {A : Finset (Fin n)} (h1 : 2 ≤ A.card) (h2 : A.card ≤ n - 2)
    (hinter : ((blockHistories n A ∩ blockHistories n Aᶜ).card : ℝ) =
      RankedGeneTree.H n * pnHatExh n A.card) :
    clanEvent n hn A = clanProb n A.card := by
  -- `Aᶜ` 也满足块计数的前提（`|Aᶜ| = n − |A|`）
  have hcompl : Aᶜ.card = n - A.card := card_compl_eq n A
  have h1c : 2 ≤ Aᶜ.card := by rw [hcompl]; omega
  have h2c : Aᶜ.card ≤ n - 2 := by rw [hcompl]; omega
  have hb : ((blockHistories n A).card : ℝ) = RankedGeneTree.H n * pn n A.card :=
    card_blockHistories_univ n h1 h2
  have hbc : ((blockHistories n Aᶜ).card : ℝ) = RankedGeneTree.H n * pn n (n - A.card) := by
    have h := card_blockHistories_univ n h1c h2c
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

/-- ★★★ **条件装配（组合形态的 `hinter`）**：交项计数用**自然组合形态**
`H |A| · H (n−|A|) · C(n−2, |A|−1)` 给出即可（由 ★★★ `H_mul_pnHatExh_eq` 自动翻成闭形式）。 -/
theorem clanEvent_eq_clanProb_of_blockCount' {n : ℕ} (hn : 2 ≤ n) (h3 : 3 ≤ n)
    {A : Finset (Fin n)} (h1 : 2 ≤ A.card) (h2 : A.card ≤ n - 2)
    (hinter : ((blockHistories n A ∩ blockHistories n Aᶜ).card : ℝ)
      = RankedGeneTree.H A.card * RankedGeneTree.H (n - A.card)
        * (((n - 2).choose (A.card - 1) : ℕ) : ℝ)) :
    clanEvent n hn A = clanProb n A.card :=
  clanEvent_eq_clanProb_of_blockCount hn h3 h1 h2
    (by rw [hinter, H_mul_pnHatExh_eq h1 h2])

/-! ## 4. `n = 4`：**整条 M4 链**的内核验证（块计数 ＋ 交项计数 ⇒ 装配）

这一节用 `_of_` 装配的**同一个接口**在 `n = 4` 上重证一遍 `clanEvent = clanProb`
（与 `RankedTreeClanLawFour.lean` 里直接数 `clanHistories` 的证明**相互独立**）——
若接口有形状错误，这里会立刻炸。三件数（都 `decide` 内核核过）：

* `#{A 是块} = 4 = H 4 · pn 4 2`（`H 4 · 2/9 = 4`）；
* `#{A 与 Aᶜ 同时是块} = 2 = H 4 · pnHatExh 4 2`（`18 · 1/9 = 2`）；
* 包含-排除：`6 = 4 + 4 − 2`（★★★ `card_clanHistories_four`）。 -/

/-- ★ **`pn 4 2 = 2/9`**（与 `H 4 = 18` 相乘给 `4`）。 -/
theorem pn_four_two : pn 4 2 = 2 / 9 := by
  norm_num [pn, Nat.choose]

/-- ★ **`pnHatExh 4 2 = 1/9`**（Lemma 4.3 的穷尽式；对比 `pnHat 4 2 2 = 2/45`，后者**不对**）。 -/
theorem pnHatExh_four_two : pnHatExh 4 2 = 1 / 9 := by
  norm_num [pnHatExh, Nat.choose]

/-- ★★ **`n = 4` 的交项：`pnHat 4 2 2 = 2/45`，乘 `H 4` 给 `4/5 ≠ 2`**（★D 的机器留痕）。 -/
theorem H_four_mul_pnHat_four_two : RankedGeneTree.H 4 * pnHat 4 2 2 = 4 / 5 := by
  rw [RankedGeneTree.H_four, pnHat]
  norm_num

set_option maxRecDepth 100000 in
/-- ★★★ **闭式计数（内核规约）**：`Fin 4` 的每个二元子集 `A`，18 条合并史中恰有 **4** 条
使 `A` 是非单点块。 -/
theorem card_blockFamily_four_block :
    ∀ A ∈ (Finset.univ : Finset (Finset (Fin 4))).filter (fun A => decide (A.card = 2) = true),
      ((Finset.univ : Finset (RankedGeneTree.RankedTree 4)).filter
        (fun ω => decide (A ∈ blockFamily 4 ω) = true)).card = 4 := by
  decide

set_option maxRecDepth 100000 in
/-- ★★★ **闭式计数（内核规约）**：`Fin 4` 的每个二元子集 `A`，18 条合并史中恰有 **2** 条
使 `A` 与 `Aᶜ` **同时**是非单点块（＝根分裂恰为 `A | Aᶜ`）。 -/
theorem card_inter_blockFamily_four :
    ∀ A ∈ (Finset.univ : Finset (Finset (Fin 4))).filter (fun A => decide (A.card = 2) = true),
      ((Finset.univ : Finset (RankedGeneTree.RankedTree 4)).filter
        (fun ω => (decide (A ∈ blockFamily 4 ω) && decide (Aᶜ ∈ blockFamily 4 ω)) = true)).card
        = 2 := by
  decide

/-- ★★★ **`n = 4` 的块计数 = `H 4 · pn 4 2`**（内核核过；一般 `n` 由 §2c 无条件给出）。 -/
theorem card_blockHistories_four (A : Finset (Fin 4)) (hA : A.card = 2) :
    ((blockHistories 4 A).card : ℝ) = RankedGeneTree.H 4 * pn 4 2 := by
  classical
  have hmem : A ∈ (Finset.univ : Finset (Finset (Fin 4))).filter
      (fun A => decide (A.card = 2) = true) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hA]
    rfl
  have hclosed := card_blockFamily_four_block A hmem
  have hcongr : blockHistories 4 A
      = (Finset.univ : Finset (RankedGeneTree.RankedTree 4)).filter
        (fun ω => decide (A ∈ blockFamily 4 ω) = true) := by
    unfold blockHistories
    apply Finset.filter_congr
    intro ω _
    simp only [decide_eq_true_eq]
  rw [hcongr, hclosed, pn_four_two, RankedGeneTree.H_four]
  norm_num

/-- ★★★ **`n = 4` 的交项计数 = `H 4 · pnHatExh 4 2`**（内核核过）。 -/
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

/-- ★★★ **`n = 4`：经 M4 接口的独立重证**（块计数 ＋ 交项计数 ＋ ★★★
`clanEvent_eq_clanProb_of_blockCount`）。 -/
theorem clanEvent_four_eq_clanProb_of_count (A : Finset (Fin 4)) (hA : A.card = 2) :
    clanEvent 4 (by norm_num) A = clanProb 4 A.card := by
  exact clanEvent_eq_clanProb_of_blockCount (n := 4) (by norm_num) (by norm_num)
    (A := A) (by omega) (by omega)
    (by
      have h := card_blockHistories_inter_four A hA
      rw [hA]
      exact h)

/-! ## 5. ★★★ 包装到缺口形状：`blockInterCount ⟹ YHKClanLawGap` -/

/-- **唯一的具名缺件**（交项计数）：`A` 与 `Aᶜ` **同时**是非单点块的历史条数
`= H n · pnHatExh n |A|`（`2 ≤ |A| ≤ n−2`）。

★ 这正是「根分裂恰为 `A | Aᶜ`」的计数；等价组合形态是
`H |A| · H (n−|A|) · C(n−2, |A|−1)`（由 ★★★ `H_mul_pnHatExh_eq` 与前者等同）。
★ 名字**不带** `gap`/`Gap`；它是 `def … : Prop`，不是 `axiom`、不是 `sorry`。

★ **W32（2026-10-26）已收口**：本 `def` 已由 ★★★ `blockInterCount_holds`（`Phylo/Stat/RankedTreeClanLaw.lean:1153`）无条件证成，不再是缺件；上面「唯一的具名缺件」描述的是当时的状态，保留作留痕。 -/
def blockInterCount (n : ℕ) : Prop :=
  ∀ A : Finset (Fin n), 2 ≤ A.card → A.card ≤ n - 2 →
    ((blockHistories n A ∩ blockHistories n Aᶜ).card : ℝ) = RankedGeneTree.H n * pnHatExh n A.card

/-- `clanHistories` 与「裸 `Finset.filter`」的一致性（供把 `clanEvent` 的结论搬进
`YHKClanLawGap` 的裸求和式）。 -/
theorem clanHistories_eq_filter (n : ℕ) (hn : 2 ≤ n) (A : Finset (Fin n)) :
    clanHistories n hn A
      = Finset.univ.filter (fun ω => (rankedTreeCladogram n hn ω).IsClade A) := by
  unfold clanHistories
  apply Finset.filter_congr
  intro ω _
  rfl

/-- ★★★ **`blockInterCount ⟹ YHKClanLawGap`**（**`_of_`**，不叫 `_holds`）。

三档：
* `|A| = 1`、`|A| = n−1`：★★★ `yhkClanLawGap_trivial_card_slice`（必然事件，**任意**律）；
* `2 ≤ |A| ≤ n−2`：★★★ `clanEvent_eq_clanProb_of_blockCount`（块计数**无条件**，交项吃 `Hc`）。

`Ω := RankedTree n`、`prob ≡ 1/H n`、`tree := rankedTreeCladogram n hn`；
归一化用 ★★★ `sum_rankedTree_uniform`。★ `n = 2` 时中间档为空（`2 ≤ |A| ≤ 0` 无解），
故 `rankedTreeCladogram` 的 `n ≥ 3`/`n = 2` 分档在这里自动落地。 -/
theorem yhkClanLawGap_of_blockInterCount (Hc : ∀ m : ℕ, blockInterCount m) : YHKClanLawGap := by
  intro n hn
  have hsum : (∑ _ω : RankedGeneTree.RankedTree n, (1 / RankedGeneTree.H n)) = 1 :=
    sum_rankedTree_uniform n hn
  refine ⟨RankedGeneTree.RankedTree n, inferInstance, fun _ => 1 / RankedGeneTree.H n,
    fun _ => ?_, hsum, fun ω => rankedTreeCladogram n hn ω, ?_⟩
  · have hH := H_pos n
    positivity
  · intro A hA hlt
    have hpos : 1 ≤ A.card := Finset.card_pos.mpr hA
    by_cases hcard1 : A.card = 1
    · exact yhkClanLawGap_trivial_card_slice hn (fun _ => 1 / RankedGeneTree.H n) hsum
        (fun ω => rankedTreeCladogram n hn ω) hA (Or.inl hcard1)
    · by_cases hcardn : A.card = n - 1
      · exact yhkClanLawGap_trivial_card_slice hn (fun _ => 1 / RankedGeneTree.H n) hsum
          (fun ω => rankedTreeCladogram n hn ω) hA (Or.inr hcardn)
      · have h1 : 2 ≤ A.card := by omega
        have h2 : A.card ≤ n - 2 := by omega
        have h3 : 3 ≤ n := by omega
        have hmain := clanEvent_eq_clanProb_of_blockCount hn h3 h1 h2 (Hc n A h1 h2)
        rw [← clanHistories_eq_filter n hn A]
        exact hmain

/-! ## 6. P2 的垫脚石：交错计数 ＋ 组合形态 ＋ 根分裂刻画

`blockInterCount`（交项计数）**本批未证**；本节交掉它外面三层：

1. ★ `card_shuffle`：交错数 `= C(p+q, p)`（直接用现成的 `Finset.powersetCard`）；
2. ★★ `blockInterCount_iff_combinatorial`：`pnHatExh` 形态 ⟺ 「两侧内部成树 × 交错」形态；
3. ★★★ `both_blocks_iff_rootSplit`：**关键结构刻画** ——
   「`A` 与 `Aᶜ` 同时是块」⟺「第 `n−2` 层（**根分裂层**）的两块恰为 `A` 与 `Aᶜ`」。
   ⇒ 下批要证的计数就是「**根分裂恰为 `A | Aᶜ`**」的合并史条数。 -/

/-- ★ **交错（shuffle）计数**：把长度 `p`、`q` 的两列交错，方案数 `= C(p+q, p)`
（↔ `Fin (p+q)` 里选 `p` 个位置的子集；用现成的 `Finset.powersetCard`，**不**新造 `Shuffle` 类型）。 -/
theorem card_shuffle (p q : ℕ) :
    ((Finset.univ : Finset (Fin (p + q))).powersetCard p).card = (p + q).choose p := by
  rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

/-- ★★ **`blockInterCount` 的组合形态（等价）**：把 `pnHatExh` 形态换成
「`A` 侧内部成树 × `Aᶜ` 侧内部成树 × 交错」，即
`H |A| · H (n−|A|) · C(n−2, |A|−1)`（由 ★★★ `H_mul_pnHatExh_eq` 双向翻译）。 -/
theorem blockInterCount_iff_combinatorial (n : ℕ) :
    blockInterCount n ↔
      ∀ A : Finset (Fin n), 2 ≤ A.card → A.card ≤ n - 2 →
        ((blockHistories n A ∩ blockHistories n Aᶜ).card : ℝ)
          = RankedGeneTree.H A.card * RankedGeneTree.H (n - A.card)
            * (((n - 2).choose (A.card - 1) : ℕ) : ℝ) := by
  constructor
  · intro H A h1 h2
    rw [H A h1 h2, H_mul_pnHatExh_eq h1 h2]
  · intro H A h1 h2
    rw [H A h1 h2, ← H_mul_pnHatExh_eq h1 h2]

/-- ★★★ **关键结构刻画**（P2 的垫脚石）：「`A` 与 `Aᶜ` 同时是（非单点）块」⟺
「第 `n−2` 层（**根分裂层**）的两块恰为 `A` 与 `Aᶜ`」。

正向的论证（**已在此证出**）：设 `A` 是第 `LA` 层的块、`Aᶜ` 是第 `LAc` 层的块，
取各自的见证 `wa ∈ A`、`wb ∈ Aᶜ`，令 `X`、`Y` 为第 `n−2` 层含它们的块。
由 ★★ `RankedGeneTree.block_subset_of_le` 得 `A ⊆ X`、`Aᶜ ⊆ Y`；
`A ∈ blockFamily` 的基数界 `|A| ≤ n−2` 排除 `LA = n−1`（那一层只有 `univ`），故 `LA ≤ n−2`。
由 `IsMergeHistory` 在步 `n−2` 的 `IsStep` 知第 `n−2` 层的代表映射**不是常值**
（`x < y` 却映到同值），故 `X ≠ univ`、`Y ≠ univ`。
★ `X`、`Y` 是**同一个映射的两条纤维** ⇒ 相等或相离；相等时 `A ∪ Aᶜ = univ ⊆ X = univ`（矛盾）
⇒ `Disjoint X Y`，于是 `A = X`、`Aᶜ = Y`（两边夹逼，用 `Aᶜ = univ ∖ A`）。
反向：第 `n−2` 层是 `range n` 里的一层 ⇒ 在 `cladesOf` 里。 -/
theorem both_blocks_iff_rootSplit {n : ℕ} (hn : 2 ≤ n) (ω : RankedGeneTree.RankedTree n)
    {A : Finset (Fin n)} (h1 : 2 ≤ A.card) (h2 : A.card ≤ n - 2) :
    (A ∈ blockFamily n ω ∧ Aᶜ ∈ blockFamily n ω) ↔
      (A ∈ RankedGeneTree.blocksOf n (RankedGeneTree.chainMap n ω.1 (n - 2)) ∧
        Aᶜ ∈ RankedGeneTree.blocksOf n (RankedGeneTree.chainMap n ω.1 (n - 2))) := by
  classical
  constructor
  · rintro ⟨hA, hAc⟩
    obtain ⟨LA, hLA, hAb⟩ := by
      simpa only [RankedGeneTree.cladesOf, Finset.mem_biUnion] using
        mem_cladesOf_of_mem_blockFamily hA
    obtain ⟨wa, -, hwa⟩ := by
      simpa only [RankedGeneTree.blocksOf, Finset.mem_image] using hAb
    obtain ⟨LAc, hLAc, hAcb⟩ := by
      simpa only [RankedGeneTree.cladesOf, Finset.mem_biUnion] using
        mem_cladesOf_of_mem_blockFamily hAc
    obtain ⟨wb, -, hwb⟩ := by
      simpa only [RankedGeneTree.blocksOf, Finset.mem_image] using hAcb
    have hwa' : wa ∈ A := by
      rw [← hwa]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
    have hwb' : wb ∈ Aᶜ := by
      rw [← hwb]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
    rw [Finset.mem_range] at hLA hLAc
    -- 层号上界：`LA = n−1` ⇒ `A = univ`，与 `|A| ≤ n−2` 冲突
    have hconst : ∀ z, RankedGeneTree.chainMap n ω.1 (n - 1) z
        = RankedGeneTree.chainMap n ω.1 (n - 1) wa := fun z => ω.2.2 z wa
    have hLAle : LA ≤ n - 2 := by
      rcases Nat.lt_or_ge LA (n - 1) with hlt | hge
      · omega
      · exfalso
        have hLAeq : LA = n - 1 := by omega
        rw [hLAeq] at hwa
        have hAuniv : A = Finset.univ := by
          rw [← hwa]
          refine Finset.eq_univ_of_forall (fun z => ?_)
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hconst z⟩
        have hcard : A.card = n := by rw [hAuniv, Finset.card_univ, Fintype.card_fin]
        omega
    have hLAcle : LAc ≤ n - 2 := by
      rcases Nat.lt_or_ge LAc (n - 1) with hlt | hge
      · omega
      · exfalso
        have hLAceq : LAc = n - 1 := by omega
        rw [hLAceq] at hwb
        have hconstb : ∀ z, RankedGeneTree.chainMap n ω.1 (n - 1) z
            = RankedGeneTree.chainMap n ω.1 (n - 1) wb := fun z => ω.2.2 z wb
        have hAcuniv : Aᶜ = Finset.univ := by
          rw [← hwb]
          refine Finset.eq_univ_of_forall (fun z => ?_)
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hconstb z⟩
        have hcard : Aᶜ.card = n := by rw [hAcuniv, Finset.card_univ, Fintype.card_fin]
        have hA2 : A.card = n := by
          have := card_compl_eq n A
          omega
        omega
    have hAX : A ⊆ Finset.univ.filter (fun z =>
        RankedGeneTree.chainMap n ω.1 (n - 2) z = RankedGeneTree.chainMap n ω.1 (n - 2) wa) := by
      rw [← hwa]
      exact RankedGeneTree.block_subset_of_le ω.1 hLAle wa
    have hAcY : Aᶜ ⊆ Finset.univ.filter (fun z =>
        RankedGeneTree.chainMap n ω.1 (n - 2) z = RankedGeneTree.chainMap n ω.1 (n - 2) wb) := by
      rw [← hwb]
      exact RankedGeneTree.block_subset_of_le ω.1 hLAcle wb
    -- 第 `n−2` 层的代表映射不是常值
    have hstep := ω.2.1 ⟨n - 2, by omega⟩
    obtain ⟨hx, hy, hxy⟩ := hstep
    have hne : ¬ ∀ z w, RankedGeneTree.chainMap n ω.1 (n - 2) z
        = RankedGeneTree.chainMap n ω.1 (n - 2) w := by
      intro hc
      have hEq : (ω.1 ⟨n - 2, by omega⟩).1 = (ω.1 ⟨n - 2, by omega⟩).2 := by
        rw [← hx, ← hy]
        exact hc _ _
      omega
    have hXne : Finset.univ.filter (fun z =>
        RankedGeneTree.chainMap n ω.1 (n - 2) z
          = RankedGeneTree.chainMap n ω.1 (n - 2) wa) ≠ Finset.univ := by
      intro hc
      apply hne
      intro z w
      have hz : RankedGeneTree.chainMap n ω.1 (n - 2) z
          = RankedGeneTree.chainMap n ω.1 (n - 2) wa := by
        have hmem : z ∈ Finset.univ.filter (fun z =>
            RankedGeneTree.chainMap n ω.1 (n - 2) z
              = RankedGeneTree.chainMap n ω.1 (n - 2) wa) := by
          rw [hc]; exact Finset.mem_univ z
        simpa using hmem
      have hw : RankedGeneTree.chainMap n ω.1 (n - 2) w
          = RankedGeneTree.chainMap n ω.1 (n - 2) wa := by
        have hmem : w ∈ Finset.univ.filter (fun z =>
            RankedGeneTree.chainMap n ω.1 (n - 2) z
              = RankedGeneTree.chainMap n ω.1 (n - 2) wa) := by
          rw [hc]; exact Finset.mem_univ w
        simpa using hmem
      rw [hz, hw]
    have hYne : Finset.univ.filter (fun z =>
        RankedGeneTree.chainMap n ω.1 (n - 2) z
          = RankedGeneTree.chainMap n ω.1 (n - 2) wb) ≠ Finset.univ := by
      intro hc
      apply hne
      intro z w
      have hz : RankedGeneTree.chainMap n ω.1 (n - 2) z
          = RankedGeneTree.chainMap n ω.1 (n - 2) wb := by
        have hmem : z ∈ Finset.univ.filter (fun z =>
            RankedGeneTree.chainMap n ω.1 (n - 2) z
              = RankedGeneTree.chainMap n ω.1 (n - 2) wb) := by
          rw [hc]; exact Finset.mem_univ z
        simpa using hmem
      have hw : RankedGeneTree.chainMap n ω.1 (n - 2) w
          = RankedGeneTree.chainMap n ω.1 (n - 2) wb := by
        have hmem : w ∈ Finset.univ.filter (fun z =>
            RankedGeneTree.chainMap n ω.1 (n - 2) z
              = RankedGeneTree.chainMap n ω.1 (n - 2) wb) := by
          rw [hc]; exact Finset.mem_univ w
        simpa using hmem
      rw [hz, hw]
    -- 同一映射的两条纤维：相等或相离
    have hXY : (Finset.univ.filter (fun z =>
          RankedGeneTree.chainMap n ω.1 (n - 2) z
            = RankedGeneTree.chainMap n ω.1 (n - 2) wa)
        = Finset.univ.filter (fun z =>
          RankedGeneTree.chainMap n ω.1 (n - 2) z
            = RankedGeneTree.chainMap n ω.1 (n - 2) wb)) ∨
        Disjoint (Finset.univ.filter (fun z =>
          RankedGeneTree.chainMap n ω.1 (n - 2) z
            = RankedGeneTree.chainMap n ω.1 (n - 2) wa))
          (Finset.univ.filter (fun z =>
          RankedGeneTree.chainMap n ω.1 (n - 2) z
            = RankedGeneTree.chainMap n ω.1 (n - 2) wb)) := by
      rcases eq_or_ne (RankedGeneTree.chainMap n ω.1 (n - 2) wa)
          (RankedGeneTree.chainMap n ω.1 (n - 2) wb) with heq | hneq
      · left
        ext z
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [heq]
      · right
        rw [Finset.disjoint_left]
        intro z hzX hzY
        exact hneq ((Finset.mem_filter.mp hzX).2.symm.trans (Finset.mem_filter.mp hzY).2)
    rcases hXY with heq | hdisj
    · exfalso
      apply hYne
      rw [← heq]
      refine Finset.eq_univ_of_forall (fun z => ?_)
      by_cases hzA : z ∈ A
      · exact hAX hzA
      · have hzAc : z ∈ Aᶜ := by simpa using hzA
        have hzY : z ∈ Finset.univ.filter (fun z =>
            RankedGeneTree.chainMap n ω.1 (n - 2) z
              = RankedGeneTree.chainMap n ω.1 (n - 2) wb) := hAcY hzAc
        rwa [← heq] at hzY
    · -- `Disjoint X Y` ⇒ `A = X`、`Aᶜ = Y`
      have hXsubA : Finset.univ.filter (fun z =>
          RankedGeneTree.chainMap n ω.1 (n - 2) z
            = RankedGeneTree.chainMap n ω.1 (n - 2) wa) ⊆ A := by
        intro z hzX
        by_contra hzA
        have hzAc : z ∈ Aᶜ := by simpa using hzA
        exact (Finset.disjoint_left.mp hdisj) hzX (hAcY hzAc)
      have hYsubAc : Finset.univ.filter (fun z =>
          RankedGeneTree.chainMap n ω.1 (n - 2) z
            = RankedGeneTree.chainMap n ω.1 (n - 2) wb) ⊆ Aᶜ := by
        intro z hzY
        by_contra hzAc
        have hzA : z ∈ A := by simpa using hzAc
        exact (Finset.disjoint_left.mp hdisj) (hAX hzA) hzY
      have hXeq : Finset.univ.filter (fun z =>
          RankedGeneTree.chainMap n ω.1 (n - 2) z
            = RankedGeneTree.chainMap n ω.1 (n - 2) wa) = A :=
        Finset.Subset.antisymm hXsubA hAX
      have hYeq : Finset.univ.filter (fun z =>
          RankedGeneTree.chainMap n ω.1 (n - 2) z
            = RankedGeneTree.chainMap n ω.1 (n - 2) wb) = Aᶜ :=
        Finset.Subset.antisymm hYsubAc hAcY
      refine ⟨?_, ?_⟩
      · rw [← hXeq]
        exact Finset.mem_image.mpr ⟨wa, Finset.mem_univ _, rfl⟩
      · rw [← hYeq]
        exact Finset.mem_image.mpr ⟨wb, Finset.mem_univ _, rfl⟩
  · rintro ⟨hA, hAc⟩
    have hA' : A ∈ RankedGeneTree.cladesOf n ω.1 := by
      rw [RankedGeneTree.cladesOf, Finset.mem_biUnion]
      exact ⟨n - 2, Finset.mem_range.mpr (by omega), hA⟩
    have hAc' : Aᶜ ∈ RankedGeneTree.cladesOf n ω.1 := by
      rw [RankedGeneTree.cladesOf, Finset.mem_biUnion]
      exact ⟨n - 2, Finset.mem_range.mpr (by omega), hAc⟩
    refine ⟨mem_blockFamily.mpr ⟨hA', h1, h2⟩, mem_blockFamily.mpr ⟨hAc', ?_, ?_⟩⟩
    · rw [card_compl_eq n A]; omega
    · rw [card_compl_eq n A]; omega

variable {N : ℕ}

/-! ## 试验：chainMap 与 gchain 在倒数第二层的对齐 -/

theorem chainMap_last_level (n : ℕ) (f : Fin (n - 1) → Fin n × Fin n) :
    RankedGeneTree.chainMap n f (n - 2) = gchain (n - 1) f ((n - 1) - 1) := rfl

/-! ## 纤维二分 -/

theorem fiber_eq_of_mem_blocksOf {n : ℕ} {r : Fin n → Fin n} {A : Finset (Fin n)}
    (hA : A ∈ RankedGeneTree.blocksOf n r) :
    ∃ a : Fin n, A = Finset.univ.filter (fun z => r z = r a) := by
  rw [RankedGeneTree.blocksOf, Finset.mem_image] at hA
  obtain ⟨w, -, hw⟩ := hA
  exact ⟨w, hw.symm⟩

theorem fiber_dichotomy {n : ℕ} {r : Fin n → Fin n} {A : Finset (Fin n)}
    (hA : A ∈ RankedGeneTree.blocksOf n r) (hAc : Aᶜ ∈ RankedGeneTree.blocksOf n r)
    (w : Fin n) :
    Finset.univ.filter (fun z => r z = r w) = A ∨
      Finset.univ.filter (fun z => r z = r w) = Aᶜ := by
  obtain ⟨a, ha⟩ := fiber_eq_of_mem_blocksOf hA
  obtain ⟨b, hb⟩ := fiber_eq_of_mem_blocksOf hAc
  have hw : w ∈ A ∪ Aᶜ := by
    rw [Finset.union_compl]
    exact Finset.mem_univ w
  rcases Finset.mem_union.mp hw with h | h
  · left
    have hrw : r w = r a := by
      rw [ha] at h
      simpa using h
    rw [ha, hrw]
  · right
    have hrw : r w = r b := by
      rw [hb] at h
      simpa using h
    rw [hb, hrw]

/-! ## s 上「恰两层」的等价关系描述 -/

def SplitEq (s A : Finset (Fin N)) (r : Fin N → Fin N) : Prop :=
  ∀ w ∈ s, ∀ w' ∈ s, r w = r w' ↔ (w ∈ A ↔ w' ∈ A)

instance instDecidableSplitEq (s A : Finset (Fin N)) (r : Fin N → Fin N) :
    Decidable (SplitEq s A r) := by unfold SplitEq; infer_instance

def LastSplit (s A : Finset (Fin N)) (m : ℕ) (f : Fin m → Fin N × Fin N) : Prop :=
  SplitEq s A (gchain m f (m - 1))

instance instDecidableLastSplit (s A : Finset (Fin N)) (m : ℕ) (f : Fin m → Fin N × Fin N) :
    Decidable (LastSplit s A m f) := by unfold LastSplit; infer_instance

def IsMHP (s A : Finset (Fin N)) (m : ℕ) (f : Fin m → Fin N × Fin N) : Prop :=
  IsMH s m f ∧ LastSplit s A m f

instance instDecidableIsMHP (s A : Finset (Fin N)) (m : ℕ) : DecidablePred (IsMHP s A m) :=
  fun f => by unfold IsMHP; infer_instance

def mhFinsetP (N m : ℕ) (s A : Finset (Fin N)) : Finset (Fin m → Fin N × Fin N) :=
  (Finset.univ : Finset (Fin m → Fin N × Fin N)).filter (IsMHP s A m ·)

theorem mem_mhFinsetP {m : ℕ} {s A : Finset (Fin N)} {f : Fin m → Fin N × Fin N} :
    f ∈ mhFinsetP N m s A ↔ IsMHP s A m f := by
  simp [mhFinsetP]

/-! ## 「两侧都是块」⟺「倒数第二层恰为 A | Aᶜ」 -/

theorem splitEq_univ_iff_blocksOf {n : ℕ} {r : Fin n → Fin n} {A : Finset (Fin n)}
    (h1 : 2 ≤ A.card) (h2 : A.card ≤ n - 2) :
    SplitEq (Finset.univ : Finset (Fin n)) A r ↔
      (A ∈ RankedGeneTree.blocksOf n r ∧ Aᶜ ∈ RankedGeneTree.blocksOf n r) := by
  constructor
  · intro h
    have hane : A.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨a, ha⟩ := hane
    have hAcne : Aᶜ.Nonempty := by
      rw [← Finset.card_pos, card_compl_eq n A]; omega
    obtain ⟨b, hb⟩ := hAcne
    have hfib : ∀ w : Fin n, w ∈ A → Finset.univ.filter (fun z => r z = r w) = A := by
      intro w hw
      ext z
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact (h z (Finset.mem_univ z) w (Finset.mem_univ w)).trans (by simp [hw])
    have hfibc : ∀ w : Fin n, w ∉ A → Finset.univ.filter (fun z => r z = r w) = Aᶜ := by
      intro w hw
      ext z
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_compl]
      constructor
      · intro hz
        rw [h z (Finset.mem_univ z) w (Finset.mem_univ w)] at hz
        exact fun hzA => hw (hz.mp hzA)
      · intro hzA
        rw [h z (Finset.mem_univ z) w (Finset.mem_univ w)]
        exact ⟨fun h => absurd h hzA, fun h2 => absurd h2 hw⟩
    constructor
    · rw [RankedGeneTree.blocksOf, Finset.mem_image]
      exact ⟨a, Finset.mem_univ a, hfib a ha⟩
    · rw [RankedGeneTree.blocksOf, Finset.mem_image]
      exact ⟨b, Finset.mem_univ b, hfibc b (Finset.mem_compl.mp hb)⟩
  · rintro ⟨hA, hAc⟩ w _ w' _
    constructor
    · intro heq
      have hmem' : w' ∈ Finset.univ.filter (fun z => r z = r w) := by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact heq.symm
      have hmem : w ∈ Finset.univ.filter (fun z => r z = r w) := by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rcases fiber_dichotomy hA hAc w with h | h
      · rw [h] at hmem hmem'
        exact ⟨fun _ => hmem', fun _ => hmem⟩
      · rw [h] at hmem hmem'
        exact ⟨fun h1 => absurd h1 (Finset.mem_compl.mp hmem), fun h1 => absurd h1 (Finset.mem_compl.mp hmem')⟩
    · intro hiff
      by_cases hw : w ∈ A
      · have hw' : w' ∈ A := hiff.mp hw
        rcases fiber_dichotomy hA hAc w with h | h
        · have h2 : w' ∈ Finset.univ.filter (fun z => r z = r w) := by rw [h]; exact hw'
          exact (by simpa using h2 : r w' = r w).symm
        · exfalso
          have : w ∈ Aᶜ := h ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
          exact (Finset.mem_compl.mp this) hw
      · have hwAc : w ∈ Aᶜ := Finset.mem_compl.mpr hw
        have hw' : w' ∉ A := fun hh => hw (hiff.mpr hh)
        have hw'Ac : w' ∈ Aᶜ := Finset.mem_compl.mpr hw'
        rcases fiber_dichotomy hA hAc w with h | h
        · exfalso
          have : w ∈ A := h ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
          exact hw this
        · have h2 : w' ∈ Finset.univ.filter (fun z => r z = r w) := by rw [h]; exact hw'Ac
          exact (by simpa using h2 : r w' = r w).symm


/-! ## 主桥：交项计数 = 「倒数第二层恰为 A | Aᶜ」的合并史条数 -/

theorem inter_card_eq_mhFinsetP (n : ℕ) {A : Finset (Fin n)}
    (h1 : 2 ≤ A.card) (h2 : A.card ≤ n - 2) :
    (blockHistories n A ∩ blockHistories n Aᶜ).card
      = (mhFinsetP n (n - 1) (Finset.univ : Finset (Fin n)) A).card := by
  classical
  have hn : 2 ≤ n := by omega
  rw [inter_blockHistories_eq]
  refine Finset.card_bij
    (fun ω (_ : ω ∈ Finset.univ.filter (fun ω : RankedGeneTree.RankedTree n =>
      A ∈ blockFamily n ω ∧ Aᶜ ∈ blockFamily n ω)) => ω.1) ?_ ?_ ?_
  · intro ω hω
    obtain ⟨-, hA, hAc⟩ := Finset.mem_filter.mp hω
    rw [mem_mhFinsetP]
    refine ⟨(isMH_univ_iff n ω.1).mpr ω.2, ?_⟩
    exact (splitEq_univ_iff_blocksOf h1 h2).mpr ((both_blocks_iff_rootSplit hn ω h1 h2).mp ⟨hA, hAc⟩)
  · intro ω₁ _ ω₂ _ heq
    exact Subtype.ext heq
  · intro g hg
    rw [mem_mhFinsetP] at hg
    obtain ⟨hmh, hls⟩ := hg
    refine ⟨⟨g, (isMH_univ_iff n g).mp hmh⟩, ?_, rfl⟩
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, (both_blocks_iff_rootSplit hn ⟨g, (isMH_univ_iff n g).mp hmh⟩ h1 h2).mpr
      ((splitEq_univ_iff_blocksOf h1 h2).mp hls)⟩

/-! ## 装配：mhFinsetP 的闭式计数 ⟹ lockInterCount -/

theorem blockInterCount_of_mhFinsetPCard
    (H : ∀ (n : ℕ) (A : Finset (Fin n)), 2 ≤ A.card → A.card ≤ n - 2 →
      (mhFinsetP n (n - 1) (Finset.univ : Finset (Fin n)) A).card
        = Hnat A.card * Hnat (n - A.card) * ((n - 2).choose (A.card - 1))) :
    ∀ n : ℕ, blockInterCount n := by
  intro n A h1 h2
  rw [inter_card_eq_mhFinsetP n h1 h2, H n A h1 h2]
  push_cast
  rw [cast_Hnat, cast_Hnat, ← H_mul_pnHatExh_eq h1 h2]

theorem card_headFiber_isBlockAt_both {k : ℕ} (hk : 1 ≤ k) (s A : Finset (Fin N)) (_hAs : A ⊆ s)
    (p : PairIn N s) (hx : p.1.1 ∈ A) (hy : p.1.2 ∈ A) :
    ((headFiber (m := k) s p).filter (fun f => IsBlockAt s (k + 1) f k A)).card
      = ((mhFinset N k (s.erase p.1.2)).filter
          (fun g => IsBlockAt (s.erase p.1.2) k g (k - 1) (A.erase p.1.2))).card := by
  refine card_headFiber_filter (m := k) s p (fun f => IsBlockAt s (k + 1) f k A)
    (fun g => IsBlockAt (s.erase p.1.2) k g (k - 1) (A.erase p.1.2)) ?_
  intro f h0 _
  have h := isBlockAt_succ_both (s := s) (m := k) (f := f) (x := p.1.1) (y := p.1.2)
    (A := A) h0 p.2.2.2 p.2.2.1 hx hy (L := k - 1)
  rwa [Nat.sub_one_add_one_eq_of_pos hk] at h

theorem card_headFiber_isBlockAt_none {k : ℕ} (hk : 1 ≤ k) (s A : Finset (Fin N)) (_hAs : A ⊆ s)
    (p : PairIn N s) (hx : p.1.1 ∉ A) (hy : p.1.2 ∉ A) :
    ((headFiber (m := k) s p).filter (fun f => IsBlockAt s (k + 1) f k A)).card
      = ((mhFinset N k (s.erase p.1.2)).filter
          (fun g => IsBlockAt (s.erase p.1.2) k g (k - 1) A)).card := by
  refine card_headFiber_filter (m := k) s p (fun f => IsBlockAt s (k + 1) f k A)
    (fun g => IsBlockAt (s.erase p.1.2) k g (k - 1) A) ?_
  intro f h0 _
  have h := isBlockAt_succ_none (s := s) (m := k) (f := f) (x := p.1.1) (y := p.1.2)
    (A := A) h0 p.2.2.2 p.2.1 p.2.2.1 hx hy (L := k - 1)
  rwa [Nat.sub_one_add_one_eq_of_pos hk] at h

theorem sum_headFiber_split_blockAt {k : ℕ} (hk : 1 ≤ k) (s A : Finset (Fin N)) (hAs : A ⊆ s) :
    (∑ p : PairIn N s,
        ((headFiber (m := k) s p).filter (fun f => IsBlockAt s (k + 1) f k A)).card)
      = (∑ p ∈ (Finset.univ : Finset (PairIn N s)).filter (fun p => p.1.1 ∈ A ∧ p.1.2 ∈ A),
            ((mhFinset N k (s.erase p.1.2)).filter
              (fun g => IsBlockAt (s.erase p.1.2) k g (k - 1) (A.erase p.1.2))).card)
        + (∑ p ∈ (Finset.univ : Finset (PairIn N s)).filter (fun p => p.1.1 ∉ A ∧ p.1.2 ∉ A),
            ((mhFinset N k (s.erase p.1.2)).filter
              (fun g => IsBlockAt (s.erase p.1.2) k g (k - 1) A)).card) := by
  have hterm : ∀ p : PairIn N s,
      ((headFiber (m := k) s p).filter (fun f => IsBlockAt s (k + 1) f k A)).card
        = (if p.1.1 ∈ A ∧ p.1.2 ∈ A then
            ((mhFinset N k (s.erase p.1.2)).filter
              (fun g => IsBlockAt (s.erase p.1.2) k g (k - 1) (A.erase p.1.2))).card
          else 0)
          + (if p.1.1 ∉ A ∧ p.1.2 ∉ A then
            ((mhFinset N k (s.erase p.1.2)).filter
              (fun g => IsBlockAt (s.erase p.1.2) k g (k - 1) A)).card
          else 0) := by
    intro p
    by_cases h1 : p.1.1 ∈ A ∧ p.1.2 ∈ A
    · rw [ite_eq_left h1, ite_eq_right (by tauto : ¬ (p.1.1 ∉ A ∧ p.1.2 ∉ A)), add_zero]
      exact card_headFiber_isBlockAt_both hk s A hAs p h1.1 h1.2
    · by_cases h2 : p.1.1 ∉ A ∧ p.1.2 ∉ A
      · rw [ite_eq_right h1, ite_eq_left h2, zero_add]
        exact card_headFiber_isBlockAt_none hk s A hAs p h2.1 h2.2
      · rw [ite_eq_right h1, ite_eq_right h2, add_zero]
        rw [Finset.card_eq_zero, ← Finset.not_nonempty_iff_eq_empty]
        rintro ⟨f, hf⟩
        rw [Finset.mem_filter] at hf
        obtain ⟨hfhead, hfP⟩ := hf
        simp only [headFiber, Finset.mem_filter, Finset.mem_univ, true_and] at hfhead
        have hmix : (p.1.1 ∈ A ∧ p.1.2 ∉ A) ∨ (p.1.1 ∉ A ∧ p.1.2 ∈ A) := by
          rcases not_and_or.mp h1 with h | h
          · exact Or.inr ⟨h, by tauto⟩
          · exact Or.inl ⟨by tauto, h⟩
        have h := not_isBlockAt_succ_mixed (s := s) (m := k) (f := f) (x := p.1.1) (y := p.1.2)
          (A := A) hfhead.1 p.2.1 p.2.2.1 hmix (L := k - 1)
        rw [Nat.sub_one_add_one_eq_of_pos hk] at h
        exact h hfP
  calc (∑ p : PairIn N s,
        ((headFiber (m := k) s p).filter (fun f => IsBlockAt s (k + 1) f k A)).card)
      = ∑ p : PairIn N s,
          ((if p.1.1 ∈ A ∧ p.1.2 ∈ A then
              ((mhFinset N k (s.erase p.1.2)).filter
                (fun g => IsBlockAt (s.erase p.1.2) k g (k - 1) (A.erase p.1.2))).card
            else 0)
            + (if p.1.1 ∉ A ∧ p.1.2 ∉ A then
              ((mhFinset N k (s.erase p.1.2)).filter
                (fun g => IsBlockAt (s.erase p.1.2) k g (k - 1) A)).card
            else 0)) := Finset.sum_congr rfl (fun p _ => hterm p)
    _ = (∑ p : PairIn N s,
            if p.1.1 ∈ A ∧ p.1.2 ∈ A then
              ((mhFinset N k (s.erase p.1.2)).filter
                (fun g => IsBlockAt (s.erase p.1.2) k g (k - 1) (A.erase p.1.2))).card
            else 0)
          + ∑ p : PairIn N s,
            if p.1.1 ∉ A ∧ p.1.2 ∉ A then
              ((mhFinset N k (s.erase p.1.2)).filter
                (fun g => IsBlockAt (s.erase p.1.2) k g (k - 1) A)).card
            else 0 := Finset.sum_add_distrib
    _ = _ := by rw [← Finset.sum_filter, ← Finset.sum_filter]

theorem sdiff_card {A s : Finset (Fin N)} (h : A ⊆ s) : (s \ A).card = s.card - A.card := by
  rw [Finset.card_sdiff, Finset.inter_eq_left.mpr h]

theorem Hnat_pred_mul {a : ℕ} (ha : 2 ≤ a) : Hnat a = a.choose 2 * Hnat (a - 1) := by
  have h := Hnat_succ (a - 1) (by omega : 1 ≤ a - 1)
  rw [Nat.sub_one_add_one_eq_of_pos (by omega : 0 < a)] at h
  rw [h, Nat.mul_comm]

theorem mhFinsetAt_card (M : ℕ) :
    ∀ (N : ℕ) (s A : Finset (Fin N)), s.card = M + 1 → A ⊆ s → 1 ≤ A.card → A.card ≤ M →
      ((mhFinset N M s).filter (fun f => IsBlockAt s M f (M - 1) A)).card
        = Hnat A.card * Hnat ((s \ A).card) * ((M - 1).choose (A.card - 1)) := by
  induction M using Nat.strong_induction_on with
  | _ M ih =>
    intro N s A hs hAs hA1 hAM
    rcases Nat.lt_or_ge M 2 with hlt | hge
    · -- M = 1
      have hM1 : M = 1 := by omega
      subst hM1
      have hAcard : A.card = 1 := by omega
      obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hAcard
      subst hw
      have hws : w ∈ s := hAs (Finset.mem_singleton_self w)
      have hpred : ∀ f : Fin 1 → Fin N × Fin N,
          IsBlockAt s 1 f (1 - 1) ({w} : Finset (Fin N)) := by
        intro f
        refine ⟨w, Finset.mem_singleton_self w, ?_⟩
        rw [show (1 - 1 : ℕ) = 0 from rfl, gchain_zero]
        ext z
        simp only [blockOf, Finset.mem_filter, id_eq, Finset.mem_singleton]
        exact ⟨fun h => ⟨h ▸ hws, h⟩, fun h => h.2⟩
      rw [Finset.filter_true_of_mem (fun f _ => hpred f), card_mhFinset 1 N s hs]
      have hb : (s \ ({w} : Finset (Fin N))).card = 1 := by
        rw [sdiff_card hAs, Finset.card_singleton]
        omega
      rw [hb, Finset.card_singleton]
      norm_num [Hnat]
    · obtain ⟨k, rfl⟩ : ∃ k, M = k + 1 := ⟨M - 1, by omega⟩
      have hk : 1 ≤ k := by omega
      have hsk : s.card = k + 2 := by omega
      simp only [Nat.add_sub_cancel]
      have hdecomp : (mhFinset N (k + 1) s).filter (fun f => IsBlockAt s (k + 1) f k A)
          = (Finset.univ : Finset (PairIn N s)).biUnion
              (fun p => (headFiber (m := k) s p).filter
                (fun f => IsBlockAt s (k + 1) f k A)) := by
        rw [mhFinset_succ_eq_biUnion (m := k) s, Finset.filter_biUnion]
      have hdisj : Set.PairwiseDisjoint (↑(Finset.univ : Finset (PairIn N s)))
          (fun p => (headFiber (m := k) s p).filter
            (fun f => IsBlockAt s (k + 1) f k A)) := by
        intro p _ q _ hpq
        exact Finset.disjoint_of_subset_left (Finset.filter_subset _ _)
          (Finset.disjoint_of_subset_right (Finset.filter_subset _ _) (headFiber_disjoint hpq))
      rw [hdecomp, Finset.card_biUnion hdisj]
      rw [sum_headFiber_split_blockAt hk s A hAs]
      have hbdef : (s \ A).card = k + 2 - A.card := by
        rw [sdiff_card hAs, hsk]
      have hAside : 2 ≤ A.card →
          (∑ p ∈ (Finset.univ : Finset (PairIn N s)).filter
            (fun p => p.1.1 ∈ A ∧ p.1.2 ∈ A),
            ((mhFinset N k (s.erase p.1.2)).filter
              (fun g => IsBlockAt (s.erase p.1.2) k g (k - 1) (A.erase p.1.2))).card)
          = Hnat A.card * Hnat ((s \ A).card) * ((k - 1).choose (A.card - 2)) := by
        intro ha2
        have hc : ∀ p ∈ (Finset.univ : Finset (PairIn N s)).filter
            (fun p => p.1.1 ∈ A ∧ p.1.2 ∈ A),
            ((mhFinset N k (s.erase p.1.2)).filter
              (fun g => IsBlockAt (s.erase p.1.2) k g (k - 1) (A.erase p.1.2))).card
            = Hnat (A.card - 1) * Hnat ((s \ A).card) * ((k - 1).choose (A.card - 2)) := by
          intro p hp
          rw [Finset.mem_filter] at hp
          obtain ⟨-, hpx, hpy⟩ := hp
          have hb' : ((s.erase p.1.2) \ (A.erase p.1.2)).card = (s \ A).card := by
            rw [sdiff_card (by
                  intro z hz
                  rw [Finset.mem_erase] at hz ⊢
                  exact ⟨hz.1, hAs hz.2⟩),
              sdiff_card hAs, Finset.card_erase_of_mem hpy, Finset.card_erase_of_mem p.2.2.1]
            omega
          rw [ih k (by omega) N (s.erase p.1.2) (A.erase p.1.2)
              (by rw [Finset.card_erase_of_mem p.2.2.1]; omega)
              (by intro z hz; rw [Finset.mem_erase] at hz ⊢; exact ⟨hz.1, hAs hz.2⟩)
              (by rw [Finset.card_erase_of_mem hpy]; omega)
              (by rw [Finset.card_erase_of_mem hpy]; omega),
            hb', Finset.card_erase_of_mem hpy,
            show A.card - 1 - 1 = A.card - 2 from by omega]
        rw [Finset.sum_congr rfl hc, Finset.sum_const, nsmul_eq_mul,
          card_pairs_both s A hAs, Hnat_pred_mul ha2]
        simp only [Nat.cast_id]
        ring
      have hAsideOne : A.card = 1 →
          (∑ p ∈ (Finset.univ : Finset (PairIn N s)).filter
            (fun p => p.1.1 ∈ A ∧ p.1.2 ∈ A),
            ((mhFinset N k (s.erase p.1.2)).filter
              (fun g => IsBlockAt (s.erase p.1.2) k g (k - 1) (A.erase p.1.2))).card) = 0 := by
        intro ha1
        have hempty : (Finset.univ : Finset (PairIn N s)).filter
            (fun p => p.1.1 ∈ A ∧ p.1.2 ∈ A) = ∅ := by
          rw [← Finset.card_eq_zero, card_pairs_both s A hAs, ha1]
          simp
        rw [hempty, Finset.sum_empty]
      have hBside : (∑ p ∈ (Finset.univ : Finset (PairIn N s)).filter
            (fun p => p.1.1 ∉ A ∧ p.1.2 ∉ A),
            ((mhFinset N k (s.erase p.1.2)).filter
              (fun g => IsBlockAt (s.erase p.1.2) k g (k - 1) A)).card)
          = Hnat A.card * Hnat ((s \ A).card) * ((k - 1).choose (A.card - 1)) := by
        by_cases hb2 : 2 ≤ (s \ A).card
        · have hc : ∀ p ∈ (Finset.univ : Finset (PairIn N s)).filter
              (fun p => p.1.1 ∉ A ∧ p.1.2 ∉ A),
              ((mhFinset N k (s.erase p.1.2)).filter
                (fun g => IsBlockAt (s.erase p.1.2) k g (k - 1) A)).card
              = Hnat A.card * Hnat ((s \ A).card - 1) * ((k - 1).choose (A.card - 1)) := by
            intro p hp
            rw [Finset.mem_filter] at hp
            obtain ⟨-, hpx, hpy⟩ := hp
            have hsub : A ⊆ s.erase p.1.2 := by
              intro z hz
              rw [Finset.mem_erase]
              exact ⟨fun h => hpy (h ▸ hz), hAs hz⟩
            have ham : A.card ≤ k := by rw [hbdef] at hb2; omega
            have hb' : ((s.erase p.1.2) \ A).card = (s \ A).card - 1 := by
              rw [sdiff_card hsub, Finset.card_erase_of_mem p.2.2.1, hbdef]
              omega
            rw [ih k (by omega) N (s.erase p.1.2) A
              (by rw [Finset.card_erase_of_mem p.2.2.1]; omega) hsub hA1 ham, hb']
          rw [Finset.sum_congr rfl hc, Finset.sum_const, nsmul_eq_mul,
            card_pairs_none s A, Hnat_pred_mul hb2]
          simp only [Nat.cast_id]
          ring
        · have hb1 : (s \ A).card = 1 := by rw [hbdef]; omega
          have hka : A.card = k + 1 := by rw [hbdef] at hb1; omega
          have hempty : (Finset.univ : Finset (PairIn N s)).filter
              (fun p => p.1.1 ∉ A ∧ p.1.2 ∉ A) = ∅ := by
            rw [← Finset.card_eq_zero, card_pairs_none s A, hb1]
            simp
          rw [hempty, Finset.sum_empty, hka]
          have hck : (k - 1).choose (k + 1 - 1) = 0 := by
            rw [show k + 1 - 1 = k from by omega, Nat.choose_eq_zero_of_lt (by omega)]
          rw [hck, Nat.mul_zero]
      rcases eq_or_lt_of_le hA1 with ha1 | ha2
      · rw [hAsideOne ha1.symm, hBside, ← ha1]
        simp
      · have hpascal : (k).choose (A.card - 1)
            = (k - 1).choose (A.card - 2) + (k - 1).choose (A.card - 1) := by
          have h := Nat.choose_succ_succ (k - 1) (A.card - 2)
          rw [show (k - 1).succ = k from by omega,
            show (A.card - 2).succ = A.card - 1 from by omega] at h
          exact h
        rw [hAside ha2, hBside, ← Nat.mul_add, hpascal]

set_option maxHeartbeats 2000000 in
/-- 最后一步的「二值性」：第 
-2 层的表示映射只取两个值（末步的两个代表）。 -/
theorem dich_last {n : ℕ} (hn : 2 ≤ n) {f : Fin (n - 1) → Fin n × Fin n}
    (h : n - 2 < n - 1) (hf : IsMH (Finset.univ : Finset (Fin n)) (n - 1) f) :
    ∃ c : Fin n, (∀ w : Fin n, gchain (n - 1) f (n - 2) w = (f ⟨n - 2, h⟩).2
        ∨ gchain (n - 1) f (n - 2) w = c) ∧ (f ⟨n - 2, h⟩).2 ≠ c := by
  classical
  have hstep : RankedGeneTree.IsStep (gchain (n - 1) f (n - 2)) (f ⟨n - 2, h⟩).1 (f ⟨n - 2, h⟩).2 :=
    hf.2.1 ⟨n - 2, h⟩
  obtain ⟨hrx, hry, hxylt⟩ := hstep
  have hlast : gchain (n - 1) f (n - 1)
      = RankedGeneTree.stepMap (gchain (n - 1) f (n - 2)) (f ⟨n - 2, h⟩).1 (f ⟨n - 2, h⟩).2 := by
    have hh := gchain_succ f (n - 2)
    rw [show n - 2 + 1 = n - 1 from by omega] at hh
    rw [hh, dite_eq_left h]
  have hconst : ∀ w : Fin n, gchain (n - 1) f (n - 1) w = gchain (n - 1) f (n - 1) ⟨0, by omega⟩ :=
    fun w => hf.2.2 w (Finset.mem_univ w) ⟨0, by omega⟩ (Finset.mem_univ _)
  refine ⟨RankedGeneTree.stepMap (gchain (n - 1) f (n - 2)) (f ⟨n - 2, h⟩).1 (f ⟨n - 2, h⟩).2 ⟨0, by omega⟩, ?_, ?_⟩
  · intro w
    have hw := hconst w
    simp only [hlast, RankedGeneTree.stepMap] at hw
    by_cases hc : gchain (n - 1) f (n - 2) w = (f ⟨n - 2, h⟩).2
    · exact Or.inl hc
    · simp only [hc, ↓reduceIte] at hw
      exact Or.inr hw
  · have hx : (f ⟨n - 2, h⟩).1
        = RankedGeneTree.stepMap (gchain (n - 1) f (n - 2)) (f ⟨n - 2, h⟩).1 (f ⟨n - 2, h⟩).2 ⟨0, by omega⟩ := by
      have h0 := hconst (f ⟨n - 2, h⟩).1
      simp only [hlast, RankedGeneTree.stepMap, hrx] at h0
      rw [ite_eq_right (by omega : ¬ ((f ⟨n - 2, h⟩).1 = (f ⟨n - 2, h⟩).2))] at h0
      exact h0
    intro hcon
    have hxy : (f ⟨n - 2, h⟩).1 = (f ⟨n - 2, h⟩).2 := hx.trans hcon.symm
    omega


theorem splitEq_of_isBlockAt {n : ℕ} (hn : 2 ≤ n) {f : Fin (n - 1) → Fin n × Fin n}
    (h : n - 2 < n - 1) (hf : IsMH (Finset.univ : Finset (Fin n)) (n - 1) f) {A : Finset (Fin n)}
    (hA : IsBlockAt (Finset.univ : Finset (Fin n)) (n - 1) f ((n - 1) - 1) A) :
    LastSplit (Finset.univ : Finset (Fin n)) A (n - 1) f := by
  classical
  have hlev : (n - 1) - 1 = n - 2 := by omega
  rw [hlev] at hA
  obtain ⟨a, haA, hAeq⟩ := hA
  obtain ⟨c, hdich, hyc⟩ := dich_last hn h hf
  have hAmem : ∀ z : Fin n,
      (z ∈ A ↔ gchain (n - 1) f (n - 2) z = gchain (n - 1) f (n - 2) a) := by
    intro z
    rw [hAeq, blockOf, Finset.mem_filter]
    exact ⟨fun hh => hh.2, fun hh => ⟨Finset.mem_univ z, hh⟩⟩
  unfold LastSplit SplitEq
  rw [hlev]
  intro w _ w' _
  rw [hAmem w, hAmem w']
  rcases hdich w with hw | hw <;> rcases hdich w' with hw' | hw' <;> rcases hdich a with ha | ha
  all_goals (rw [hw, hw', ha]; simp [hyc, Ne.symm hyc])

theorem mhFinsetP_eq_filter_isBlockAt (n : ℕ) {A : Finset (Fin n)}
    (h1 : 2 ≤ A.card) (h2 : A.card ≤ n - 2) :
    mhFinsetP n (n - 1) (Finset.univ : Finset (Fin n)) A
      = (mhFinset n (n - 1) (Finset.univ : Finset (Fin n))).filter
          (fun f => IsBlockAt (Finset.univ : Finset (Fin n)) (n - 1) f ((n - 1) - 1) A) := by
  classical
  have hn : 2 ≤ n := by omega
  have h : n - 2 < n - 1 := by omega
  have hlev : (n - 1) - 1 = n - 2 := by omega
  have key : ∀ f : Fin (n - 1) → Fin n × Fin n,
      IsMHP (Finset.univ : Finset (Fin n)) A (n - 1) f ↔
        (IsMH (Finset.univ : Finset (Fin n)) (n - 1) f ∧
          IsBlockAt (Finset.univ : Finset (Fin n)) (n - 1) f ((n - 1) - 1) A) := by
    intro f
    unfold IsMHP
    constructor
    · rintro ⟨hmh, hls⟩
      obtain ⟨a, haA⟩ := Finset.card_pos.mp (by omega : 0 < A.card)
      refine ⟨hmh, a, haA, ?_⟩
      unfold LastSplit SplitEq at hls
      rw [hlev] at hls
      ext z
      rw [blockOf, Finset.mem_filter]
      exact ⟨fun hz => ⟨Finset.mem_univ z,
          (hls z (Finset.mem_univ z) a (Finset.mem_univ a)).mpr ⟨fun _ => haA, fun _ => hz⟩⟩,
        fun hz => ((hls z (Finset.mem_univ z) a (Finset.mem_univ a)).mp hz.2).mpr haA⟩
    · rintro ⟨hmh, hba⟩
      exact ⟨hmh, splitEq_of_isBlockAt hn h hmh hba⟩
  unfold mhFinsetP mhFinset
  rw [Finset.filter_filter]
  exact Finset.filter_congr (fun f _ => key f)

theorem blockInterCount_holds (n : ℕ) : blockInterCount n := by
  intro A h1 h2
  have hb : ((Finset.univ : Finset (Fin n)) \ A).card = n - A.card := by
    rw [sdiff_card (Finset.subset_univ A), Finset.card_univ, Fintype.card_fin]
  have hlev : (n - 1) - 1 = n - 2 := by omega
  rw [inter_card_eq_mhFinsetP n h1 h2, mhFinsetP_eq_filter_isBlockAt n h1 h2,
    mhFinsetAt_card (n - 1) n (Finset.univ : Finset (Fin n)) A
      (by simp only [Finset.card_univ, Fintype.card_fin]; omega)
      (Finset.subset_univ A) (by omega) (by omega),
    hb, hlev]
  push_cast
  rw [cast_Hnat, cast_Hnat, ← H_mul_pnHatExh_eq h1 h2]

theorem yhkClanLawGap_holds : YHKClanLawGap :=
  yhkClanLawGap_of_blockInterCount blockInterCount_holds

end Phylo.Stat.RankedTreeClanLaw
