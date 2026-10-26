/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.Stat.RankedTreeClanLaw
import Phylo.Stat.RankedTreeCladogram

/-!
# `Phylo.Stat.ClanPairLaw` —— ZDS2011 Theorem 6.3(ii) 的**四条概率等式**的概率层

## 0. 目标：`H` 的**五条**（`ReciprocalMonophyly.lean` 的 `twoClanLawGap_of_threeEvents`）

`H` 的 `∃` 体里有五条「文献闭式 ＝ 概率」的等式（`a = |A|`, `b = |B|`, 均 `a + b < n`）：

1. `P(A、B 同为 clade) = rn n a b` —— Thm 4.5 **Case 5**；
2. `P(A、X−B 同为 clade，但 B 不是) = Rn n a (n−b) − pnHatExh n b · pn (n−b) a`
   —— 首项 Thm 4.5 **Case 2**，减项即 ④；
3. `P(B、X−A 同为 clade，但 A 不是) = Rn n b (n−a) − pnHatExh n a · pn (n−a) b`
   —— 首项 Thm 4.5 **Case 3**，减项即 ⑤；
4. `p̂_n(b, n−b) · p_{n−b}(a)` —— 乘法定理（`A`、`X−B`、`B` **同时**是 clade）；
5. `p̂_n(a, n−a) · p_{n−a}(b)` —— ⑤（同理）。

（第 5 条 `a + b = n` 的穷尽支 `qnExhaustive` 是 Lemma 6.2 的概率层，**不**在本文件范围：
它归 `YHKClanLawGap` 那条线。）

文献依据（渲染页 `references/pdf/…1101.1311.pdf` **p.12–13** ＝ 论文 p.12–13，逐字核过）：
p.12 的 Theorem 6.3(ii) 公式 ＋ p.13 的 Proof 三事件 (a)(b)(c) 与
"`p̂_n(b, n−b)p_{n−b}(a)` is the probability that `A`, `X − B` and `B` are clades of `T`"。

## 1. 本文件交付什么

**(A) 概率层本体（无条件，`_of_` 之前的部分）**

* `sum_uniform_eq_card_div` / `sum_uniform_eq_iff`：均匀律下
  「概率 ＝ 闭式」⟺「条数 ＝ 闭式 × 分母」。这是**概率 ↔ 计数**的唯一桥梁，
  它把四条概率等式全部化成计数等式。
* `filter_pair_R_eq_union` / `disjoint_pair_R` / `sum_pair_R_eq_sub`：
  ②③ 的**集合分解**（无条件、谓词无关）：
  `事件(b) = {A、X−B 同为 clade} ∖ {A、X−B、B 同为 clade}`，
  故 `P(b) = P(A、X−B) − P(A、X−B、B)`。这就是文献「减项」的**精确**来源。

**(B) 三条计数化陈述（具名 `def … : Prop`，不叫 `_holds`、名字不含 `gap`）**

* `clanPairCount`（①，Case 5）· `clanPairComplCount`（②③ 首项，Case 2/3）·
  `tripleClanCount`（④⑤，乘法定理）· `clanExhaustiveCount`（穷尽支，仅供装配）。

★★ **记账（协调侧 WB `10-26 23:5x` 批 A）**：这 **4** 条 `def … : Prop` **不另立台账行** ——
它们是 `TwoClanLawGap`（`Phylo/Stat/ReciprocalMonophyly.lean:977`）**这一条**欠账的**内部拆解**，
登记成 4 行会让七桶的「真开放」从「对文献欠几条」漂成「库内有多少未证 `Prop`」（`真开放 1 → 5`），
README 与历次周报的对比会立刻断裂。想要后一个指标时应**另开一个指标**，不要塞进七桶。
因此 `scripts/gap_ledger.py` 的**注释**里也记了同一句话（只加注释，判据与桶位一字未改）。

**(C) 装配（`_of_`，**无条件**真证）**：`threeEventProbs_of_counts` ——
四条计数等式 ⇒ `H` 的**整个 `∃` 载荷**（`prob`、非负、`Σ = 1`、四条概率等式）。
`prob` 取均匀律 `1 / |Ω|`。

**(D) ④⑤ 的条件载体（无条件）**：`pnEvent_eq_pn` ——
在 `m` 叶的 ranked 模型上，「`A` 是非单点块」的**概率**恰是 `pn m a`
（`2 ≤ a ≤ m−2`；用 `card_blockHistories_univ`）。这就是 `p_{n−b}(a)` 的载体：
4 ⑤ 的条件事件「在 `n−b` 叶的子树上再要求 `A` 成 clade」的概率**已经落地**。
另加 `pnHatExh_eq_combinatorial` / `tripleCount_combinatorial`：④⑤ 的闭式
`p̂_n(b,n−b)·p_{n−b}(a)` 与**组合形态** `[H b · H (n−b) · C(n−2, b−1) / H n] · p_{n−b}(a)`
（＝「根分裂恰为 `B | Bᶜ` 的条数」×「子树上 `A` 成块的条数」）**等价**。

## 2. 纪律

`_of_` 命名、`def … : Prop` 登记缺件、无 `sorry`/`axiom`、不改任何既有 `def` 的陈述。
-/

noncomputable section

open Classical

namespace Phylo.Stat.ClanPairLaw

open Phylo.Stat
open Phylo.Stat.RankedTreeCladogram
open Phylo.Stat.RankedTreeClanLaw
open Phylo.Stat.ReciprocalMonophyly

variable {n : ℕ} {Ω : Type*} [Fintype Ω]

/-! ## 3. 均匀律：**概率 ＝ 条数 / 分母**（任意有限 `Ω`，谓词无关） -/

omit [Fintype Ω] in
/-- ★ **均匀律下的事件概率 ＝ 条数 / 分母**。 -/
theorem sum_uniform_eq_card_div {D : ℝ} (S : Finset Ω) :
    ∑ _ω ∈ S, (1 / D) = (S.card : ℝ) / D := by
  rw [Finset.sum_const, nsmul_eq_mul, mul_one_div]

omit [Fintype Ω] in
/-- ★★★ **概率层核心**：均匀律 `prob ≡ 1/D` 下

`∑_{ω ∈ S} prob ω = q  ⟺  #S = q · D`　（`D ≠ 0`）。

⇒ 四条概率等式（右端是文献闭式）**全部等价于**四条计数等式。
本文件后面所有 `_of_` 装配都用这一条把概率换成条数。 -/
theorem sum_uniform_eq_iff {D : ℝ} (hD : D ≠ 0) (S : Finset Ω) (q : ℝ) :
    (∑ _ω ∈ S, (1 / D) = q) ↔ ((S.card : ℝ) = q * D) := by
  rw [sum_uniform_eq_card_div, div_eq_iff hD]

/-- ★ **均匀律的归一化**：`Σ_{ω : Ω} 1/D = 1`（`D = |Ω|`、`D ≠ 0`）。 -/
theorem sum_uniform_one {D : ℝ} (hD : D ≠ 0) (hDc : (Fintype.card Ω : ℝ) = D) :
    ∑ _ω : Ω, (1 / D) = 1 := by
  rw [Finset.sum_const, nsmul_eq_mul, mul_one_div, Finset.card_univ, hDc, div_self hD]

/-! ## 4. 三事件的**集合分解**：②③ 的减项从哪来（无条件）

文献 p.13：「`p̂_n(b, n−b)p_{n−b}(a)` is the probability that `A`, `X − B` and `B` are
clades of `T`」，而事件 (b) 是「`A`、`X−B` 是 clade、`B` **不是**」。于是

```
事件 (b) = {A、X−B 同为 clade} ∖ {A、X−B、B 同为 clade}
```

**逐字**：`(p ∧ q ∧ ¬r) ⟺ (p ∧ q) ∧ ¬(p ∧ q ∧ r)`。下面把集合、基数、求和三层都给出。 -/

/-- ★★ **事件 (b) ＝（`A`、`X−B` 同为 clade）减去（`A`、`X−B`、`B` 同为 clade）**。 -/
theorem filter_pair_R_eq_sdiff (U : Ω → Cladogram.{0, 0} (Fin n ⊕ Unit))
    (A B : Finset (Fin n)) :
    (Finset.univ : Finset Ω).filter
        (fun ω => (U ω).IsClade (A.image Sum.inl) ∧
          (U ω).IsClade (Bᶜ.image Sum.inl) ∧ ¬ (U ω).IsClade (B.image Sum.inl))
      = (Finset.univ : Finset Ω).filter
          (fun ω => (U ω).IsClade (A.image Sum.inl) ∧ (U ω).IsClade (Bᶜ.image Sum.inl))
        \ (Finset.univ : Finset Ω).filter
          (fun ω => (U ω).IsClade (A.image Sum.inl) ∧ (U ω).IsClade (Bᶜ.image Sum.inl)
            ∧ (U ω).IsClade (B.image Sum.inl)) := by
  classical
  ext ω
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff]
  tauto

/-- ★★ **（`A`、`X−B` 同为 clade）＝ 事件 (b) ∪（三者同为 clade）**。 -/
theorem filter_pair_R_eq_union (U : Ω → Cladogram.{0, 0} (Fin n ⊕ Unit))
    (A B : Finset (Fin n)) :
    (Finset.univ : Finset Ω).filter
        (fun ω => (U ω).IsClade (A.image Sum.inl) ∧ (U ω).IsClade (Bᶜ.image Sum.inl))
      = (Finset.univ : Finset Ω).filter
          (fun ω => (U ω).IsClade (A.image Sum.inl) ∧
            (U ω).IsClade (Bᶜ.image Sum.inl) ∧ ¬ (U ω).IsClade (B.image Sum.inl))
        ∪ (Finset.univ : Finset Ω).filter
          (fun ω => (U ω).IsClade (A.image Sum.inl) ∧ (U ω).IsClade (Bᶜ.image Sum.inl)
            ∧ (U ω).IsClade (B.image Sum.inl)) := by
  classical
  ext ω
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
  tauto

/-- ★★ **两支互斥**（事件 (b) 与「三者同为 clade」不能同时成立）。 -/
theorem disjoint_event_b_triple (U : Ω → Cladogram.{0, 0} (Fin n ⊕ Unit))
    (A B : Finset (Fin n)) :
    Disjoint
      ((Finset.univ : Finset Ω).filter
        (fun ω => (U ω).IsClade (A.image Sum.inl) ∧
          (U ω).IsClade (Bᶜ.image Sum.inl) ∧ ¬ (U ω).IsClade (B.image Sum.inl)))
      ((Finset.univ : Finset Ω).filter
        (fun ω => (U ω).IsClade (A.image Sum.inl) ∧ (U ω).IsClade (Bᶜ.image Sum.inl)
          ∧ (U ω).IsClade (B.image Sum.inl))) := by
  classical
  rw [Finset.disjoint_left]
  intro ω hω hω'
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω hω'
  exact hω.2.2 hω'.2.2

/-- ★★★ **② 的概率恒等式**（无条件；任意 `prob`，甚至不要求非负）：

`P(事件 b) = P(A、X−B 同为 clade) − P(A、X−B、B 同为 clade)`。

代入 `P(A、X−B) = Rn n a (n−b)`（Case 2）与
`P(A、X−B、B) = pnHatExh n b · pn (n−b) a`（④）即得文献 ②。 -/
theorem sum_pair_R_eq_sub (prob : Ω → ℝ) (U : Ω → Cladogram.{0, 0} (Fin n ⊕ Unit))
    (A B : Finset (Fin n)) :
    (∑ ω ∈ (Finset.univ : Finset Ω).filter
        (fun ω => (U ω).IsClade (A.image Sum.inl) ∧
          (U ω).IsClade (Bᶜ.image Sum.inl) ∧ ¬ (U ω).IsClade (B.image Sum.inl)), prob ω)
      = (∑ ω ∈ (Finset.univ : Finset Ω).filter
            (fun ω => (U ω).IsClade (A.image Sum.inl) ∧ (U ω).IsClade (Bᶜ.image Sum.inl)),
            prob ω)
        - (∑ ω ∈ (Finset.univ : Finset Ω).filter
            (fun ω => (U ω).IsClade (A.image Sum.inl) ∧ (U ω).IsClade (Bᶜ.image Sum.inl)
              ∧ (U ω).IsClade (B.image Sum.inl)), prob ω) := by
  classical
  have hunion := filter_pair_R_eq_union (Ω := Ω) U A B
  have hdj := disjoint_event_b_triple (Ω := Ω) U A B
  rw [hunion, Finset.sum_union hdj]
  ring

/-- ★★ **② 的计数形态**（`ℕ`，加法）：`#(A、X−B 同为 clade) = #事件(b) + #(三者同为 clade)`。 -/
theorem card_pair_R_eq_add (U : Ω → Cladogram.{0, 0} (Fin n ⊕ Unit))
    (A B : Finset (Fin n)) :
    ((Finset.univ : Finset Ω).filter
        (fun ω => (U ω).IsClade (A.image Sum.inl) ∧ (U ω).IsClade (Bᶜ.image Sum.inl))).card
      = ((Finset.univ : Finset Ω).filter
            (fun ω => (U ω).IsClade (A.image Sum.inl) ∧
              (U ω).IsClade (Bᶜ.image Sum.inl) ∧ ¬ (U ω).IsClade (B.image Sum.inl))).card
        + ((Finset.univ : Finset Ω).filter
            (fun ω => (U ω).IsClade (A.image Sum.inl) ∧ (U ω).IsClade (Bᶜ.image Sum.inl)
              ∧ (U ω).IsClade (B.image Sum.inl))).card := by
  classical
  rw [filter_pair_R_eq_union (Ω := Ω) U A B,
    Finset.card_union_of_disjoint (disjoint_event_b_triple (Ω := Ω) U A B)]

/-- ★★ **② 的计数形态**（`ℝ`）：`#事件(b) = #(A、X−B 同为 clade) − #(三者同为 clade)`。 -/
theorem card_event_b_eq_sub (U : Ω → Cladogram.{0, 0} (Fin n ⊕ Unit))
    (A B : Finset (Fin n)) :
    (((Finset.univ : Finset Ω).filter
            (fun ω => (U ω).IsClade (A.image Sum.inl) ∧
              (U ω).IsClade (Bᶜ.image Sum.inl) ∧ ¬ (U ω).IsClade (B.image Sum.inl))).card : ℝ)
      = (((Finset.univ : Finset Ω).filter
            (fun ω => (U ω).IsClade (A.image Sum.inl) ∧ (U ω).IsClade (Bᶜ.image Sum.inl))).card : ℝ)
        - (((Finset.univ : Finset Ω).filter
            (fun ω => (U ω).IsClade (A.image Sum.inl) ∧ (U ω).IsClade (Bᶜ.image Sum.inl)
              ∧ (U ω).IsClade (B.image Sum.inl))).card : ℝ) := by
  have h := card_pair_R_eq_add (Ω := Ω) U A B
  rw [h]
  push_cast
  ring

/-! ### 4b. 对称版：事件 (c)（`A ↔ B` 一次即可，第三组等式用它） -/

/-- ★★ **事件 (c) ＝（`X−A`、`B` 同为 clade）减去（`A`、`X−A`、`B` 同为 clade）**。 -/
theorem filter_pair_L_eq_sdiff (U : Ω → Cladogram.{0, 0} (Fin n ⊕ Unit))
    (A B : Finset (Fin n)) :
    (Finset.univ : Finset Ω).filter
        (fun ω => (U ω).IsClade (Aᶜ.image Sum.inl) ∧
          (U ω).IsClade (B.image Sum.inl) ∧ ¬ (U ω).IsClade (A.image Sum.inl))
      = (Finset.univ : Finset Ω).filter
          (fun ω => (U ω).IsClade (Aᶜ.image Sum.inl) ∧ (U ω).IsClade (B.image Sum.inl))
        \ (Finset.univ : Finset Ω).filter
          (fun ω => (U ω).IsClade (Aᶜ.image Sum.inl) ∧ (U ω).IsClade (B.image Sum.inl)
            ∧ (U ω).IsClade (A.image Sum.inl)) := by
  classical
  ext ω
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff]
  tauto

/-- ★★ **（`X−A`、`B` 同为 clade）＝ 事件 (c) ∪（三者同为 clade）**。 -/
theorem filter_pair_L_eq_union (U : Ω → Cladogram.{0, 0} (Fin n ⊕ Unit))
    (A B : Finset (Fin n)) :
    (Finset.univ : Finset Ω).filter
        (fun ω => (U ω).IsClade (Aᶜ.image Sum.inl) ∧ (U ω).IsClade (B.image Sum.inl))
      = (Finset.univ : Finset Ω).filter
          (fun ω => (U ω).IsClade (Aᶜ.image Sum.inl) ∧
            (U ω).IsClade (B.image Sum.inl) ∧ ¬ (U ω).IsClade (A.image Sum.inl))
        ∪ (Finset.univ : Finset Ω).filter
          (fun ω => (U ω).IsClade (Aᶜ.image Sum.inl) ∧ (U ω).IsClade (B.image Sum.inl)
            ∧ (U ω).IsClade (A.image Sum.inl)) := by
  classical
  ext ω
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
  tauto

/-- ★★ **两支互斥**（事件 (c) 与「三者同为 clade」）。 -/
theorem disjoint_event_c_triple (U : Ω → Cladogram.{0, 0} (Fin n ⊕ Unit))
    (A B : Finset (Fin n)) :
    Disjoint
      ((Finset.univ : Finset Ω).filter
        (fun ω => (U ω).IsClade (Aᶜ.image Sum.inl) ∧
          (U ω).IsClade (B.image Sum.inl) ∧ ¬ (U ω).IsClade (A.image Sum.inl)))
      ((Finset.univ : Finset Ω).filter
        (fun ω => (U ω).IsClade (Aᶜ.image Sum.inl) ∧ (U ω).IsClade (B.image Sum.inl)
          ∧ (U ω).IsClade (A.image Sum.inl))) := by
  classical
  rw [Finset.disjoint_left]
  intro ω hω hω'
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω hω'
  exact hω.2.2 hω'.2.2

/-- ★★★ **③ 的概率恒等式**（无条件）：

`P(事件 c) = P(X−A、B 同为 clade) − P(A、X−A、B 同为 clade)`。
代入 Case 3 与 ⑤ 即得文献 ③。 -/
theorem sum_pair_L_eq_sub (prob : Ω → ℝ) (U : Ω → Cladogram.{0, 0} (Fin n ⊕ Unit))
    (A B : Finset (Fin n)) :
    (∑ ω ∈ (Finset.univ : Finset Ω).filter
        (fun ω => (U ω).IsClade (Aᶜ.image Sum.inl) ∧
          (U ω).IsClade (B.image Sum.inl) ∧ ¬ (U ω).IsClade (A.image Sum.inl)), prob ω)
      = (∑ ω ∈ (Finset.univ : Finset Ω).filter
            (fun ω => (U ω).IsClade (Aᶜ.image Sum.inl) ∧ (U ω).IsClade (B.image Sum.inl)),
            prob ω)
        - (∑ ω ∈ (Finset.univ : Finset Ω).filter
            (fun ω => (U ω).IsClade (Aᶜ.image Sum.inl) ∧ (U ω).IsClade (B.image Sum.inl)
              ∧ (U ω).IsClade (A.image Sum.inl)), prob ω) := by
  classical
  have hunion := filter_pair_L_eq_union (Ω := Ω) U A B
  have hdj := disjoint_event_c_triple (Ω := Ω) U A B
  rw [hunion, Finset.sum_union hdj]
  ring

/-- ★★ **③ 的计数形态**（`ℝ`）：`#事件(c) = #(X−A、B) − #(三者同为 clade)`。 -/
theorem card_event_c_eq_sub (U : Ω → Cladogram.{0, 0} (Fin n ⊕ Unit))
    (A B : Finset (Fin n)) :
    (((Finset.univ : Finset Ω).filter
            (fun ω => (U ω).IsClade (Aᶜ.image Sum.inl) ∧
              (U ω).IsClade (B.image Sum.inl) ∧ ¬ (U ω).IsClade (A.image Sum.inl))).card : ℝ)
      = (((Finset.univ : Finset Ω).filter
            (fun ω => (U ω).IsClade (Aᶜ.image Sum.inl) ∧ (U ω).IsClade (B.image Sum.inl))).card : ℝ)
        - (((Finset.univ : Finset Ω).filter
            (fun ω => (U ω).IsClade (Aᶜ.image Sum.inl) ∧ (U ω).IsClade (B.image Sum.inl)
              ∧ (U ω).IsClade (A.image Sum.inl))).card : ℝ) := by
  classical
  rw [filter_pair_L_eq_union (Ω := Ω) U A B,
    Finset.card_union_of_disjoint (disjoint_event_c_triple (Ω := Ω) U A B)]
  push_cast
  ring

/-! ## 5. 三条计数化陈述（具名缺件，`def … : Prop`）

★ 三条都是**计数**等式：`#事件条数 = 文献闭式 × |Ω|`。由 ★★★ `sum_uniform_eq_iff`，
它们与 `H` 里的概率等式**逐条等价**（见 §6 的装配）。 -/

/-- **① 的计数化**（Thm 4.5 **Case 5**）：`A`、`B` 同为 clade 的条数
`= rn n a b · |Ω|`（`A ∩ B = ∅`、`A ∪ B ⊊ X`）。★ **属 `TwoClanLawGap` 行内**，不另立台账行（见模块头 §1 的记账）。 -/
def clanPairCount (N : ℕ) (Ω : Type*) [Fintype Ω]
    (U : Ω → Cladogram.{0, 0} (Fin N ⊕ Unit)) : Prop :=
  ∀ A B : Finset (Fin N), Disjoint A B → A.Nonempty → B.Nonempty → A.card + B.card < N →
    (((Finset.univ : Finset Ω).filter
        (fun ω => (U ω).IsClade (A.image Sum.inl) ∧
          (U ω).IsClade (B.image Sum.inl))).card : ℝ)
      = rn N A.card B.card * (Fintype.card Ω : ℝ)

/-- **②③ 首项的计数化**（Thm 4.5 **Case 2 / Case 3**，两条由 `A ↔ B` 对称合成一条）：
`A` 与 `Bᶜ` 同为 clade 的条数 `= Rn n a (n−b) · |Ω|`。

★ `Case 3` 是 `(A, B) := (B, A)` 的实例：`Aᶜ` 与 `B` 同为 clade
`= Rn n b (n−a)`。★ **属 `TwoClanLawGap` 行内**，不另立台账行（见模块头 §1 的记账）。 -/
def clanPairComplCount (N : ℕ) (Ω : Type*) [Fintype Ω]
    (U : Ω → Cladogram.{0, 0} (Fin N ⊕ Unit)) : Prop :=
  ∀ A B : Finset (Fin N), Disjoint A B → A.Nonempty → B.Nonempty → A.card + B.card < N →
    (((Finset.univ : Finset Ω).filter
        (fun ω => (U ω).IsClade (A.image Sum.inl) ∧
          (U ω).IsClade (Bᶜ.image Sum.inl))).card : ℝ)
      = Rn N A.card (N - B.card) * (Fintype.card Ω : ℝ)

/-- **④⑤ 的计数化**（乘法定理）：`A`、`X−B`、`B` **三者同为** clade 的条数
`= p̂_n(b, n−b) · p_{n−b}(a) · |Ω|`。

★ 这正是文献 p.13 的 "`p̂_n(b, n−b)p_{n−b}(a)` is the probability that `A`, `X − B`
and `B` are clades" —— 它是 ②③ 的**减项**。★ **属 `TwoClanLawGap` 行内**，不另立台账行（见模块头 §1 的记账）。 -/
def tripleClanCount (N : ℕ) (Ω : Type*) [Fintype Ω]
    (U : Ω → Cladogram.{0, 0} (Fin N ⊕ Unit)) : Prop :=
  ∀ A B : Finset (Fin N), Disjoint A B → A.Nonempty → B.Nonempty → A.card + B.card < N →
    (((Finset.univ : Finset Ω).filter
        (fun ω => (U ω).IsClade (A.image Sum.inl) ∧ (U ω).IsClade (Bᶜ.image Sum.inl)
          ∧ (U ω).IsClade (B.image Sum.inl))).card : ℝ)
      = (pnHatExh N B.card * pn (N - B.card) A.card) * (Fintype.card Ω : ℝ)

/-- **穷尽支的计数化**（`a + b = n`，Theorem 6.3(i) ＝ Lemma 6.2 的概率层；
**不**在本文件证明，只为装配 `H` 的第四组）。★ **属 `TwoClanLawGap` 行内**，不另立台账行（见模块头 §1 的记账）。 -/
def clanExhaustiveCount (N : ℕ) (Ω : Type*) [Fintype Ω]
    (U : Ω → Cladogram.{0, 0} (Fin N ⊕ Unit)) : Prop :=
  ∀ A B : Finset (Fin N), Disjoint A B → A.Nonempty → B.Nonempty → A.card + B.card = N →
    (((Finset.univ : Finset Ω).filter (fun ω => IsClanMinusRoot (U ω) A)).card : ℝ)
      = qnExhaustive A.card B.card * (Fintype.card Ω : ℝ)

/-! ## 6. ★★ 装配（`_of_`，无条件真证）：四条计数 ⇒ `H` 的整个 `∃` 载荷

`prob` 取**均匀律** `1 / |Ω|`（`hDc : |Ω| = D`）。`n = 2` 的分档不在本定理里
（`H` 的 `n ≥ 3` 由调用方给；事实上本定理对**任意** `N` 成立，不需要 `3 ≤ N`）。 -/

/-- ★★★ **Theorem 6.3(ii) 四条概率等式的概率层**（`_of_`）：

四条**计数**等式（①、Case 2/3、④⑤、穷尽支）⇒ `H` 的整个 `∃` 载荷：

```
∃ (prob : Ω → ℝ) (_ : ∀ ω, 0 ≤ prob ω) (_ : ∑ ω, prob ω = 1),
  (P(a) = rn n a b) ∧ (P(b) = Rn n a (n−b) − pnHatExh n b · pn (n−b) a)
    ∧ (P(c) = Rn n b (n−a) − pnHatExh n a · pn (n−a) b) ∧ (穷尽支)
```

其中 `prob ≡ 1/|Ω|`。**证明只做两件事**：把每个 `∑ prob` 换成 `条数 / |Ω|`
（★★★ `sum_uniform_eq_iff`），②③ 用 ★★★ `sum_pair_R_eq_sub` 拆成「首项 − 减项」。 -/
theorem threeEventProbs_of_counts (N : ℕ) {Ω : Type*} [Fintype Ω]
    (U : Ω → Cladogram.{0, 0} (Fin N ⊕ Unit))
    (hD : (Fintype.card Ω : ℝ) ≠ 0)
    (cA : clanPairCount N Ω U) (cR : clanPairComplCount N Ω U)
    (cT : tripleClanCount N Ω U) (cE : clanExhaustiveCount N Ω U) :
    ∃ (prob : Ω → ℝ) (_ : ∀ ω, 0 ≤ prob ω) (_ : ∑ ω, prob ω = 1),
      (∀ A B : Finset (Fin N), Disjoint A B → A.Nonempty → B.Nonempty →
        A.card + B.card < N →
        (∑ ω ∈ (Finset.univ : Finset Ω).filter
            (fun ω => (U ω).IsClade (A.image Sum.inl) ∧
              (U ω).IsClade (B.image Sum.inl)), prob ω) = rn N A.card B.card)
      ∧ (∀ A B : Finset (Fin N), Disjoint A B → A.Nonempty → B.Nonempty →
        A.card + B.card < N →
        (∑ ω ∈ (Finset.univ : Finset Ω).filter
            (fun ω => (U ω).IsClade (A.image Sum.inl) ∧
              (U ω).IsClade (Bᶜ.image Sum.inl) ∧
              ¬ (U ω).IsClade (B.image Sum.inl)), prob ω)
          = Rn N A.card (N - B.card) - pnHatExh N B.card * pn (N - B.card) A.card)
      ∧ (∀ A B : Finset (Fin N), Disjoint A B → A.Nonempty → B.Nonempty →
        A.card + B.card < N →
        (∑ ω ∈ (Finset.univ : Finset Ω).filter
            (fun ω => (U ω).IsClade (Aᶜ.image Sum.inl) ∧
              (U ω).IsClade (B.image Sum.inl) ∧
              ¬ (U ω).IsClade (A.image Sum.inl)), prob ω)
          = Rn N B.card (N - A.card) - pnHatExh N A.card * pn (N - A.card) B.card)
      ∧ (∀ A B : Finset (Fin N), Disjoint A B → A.Nonempty → B.Nonempty →
        A.card + B.card = N →
        (∑ ω ∈ (Finset.univ : Finset Ω).filter (fun ω => IsClanMinusRoot (U ω) A),
            prob ω) = qnExhaustive A.card B.card) := by
  classical
  have hpos : (0 : ℝ) < (Fintype.card Ω : ℝ) := lt_of_le_of_ne (by positivity) (Ne.symm hD)
  have hDpos : (0 : ℝ) < (Fintype.card Ω : ℝ) := hpos
  refine ⟨fun _ => 1 / (Fintype.card Ω : ℝ), fun _ => by positivity,
    sum_uniform_one (D := (Fintype.card Ω : ℝ)) hD rfl, ?_, ?_, ?_, ?_⟩
  · -- ①
    intro A B hd hA hB hlt
    exact (sum_uniform_eq_iff hD _ _).mpr (cA A B hd hA hB hlt)
  · -- ②：首项（Case 2）− 减项（④）
    intro A B hd hA hB hlt
    rw [sum_pair_R_eq_sub (fun _ => 1 / (Fintype.card Ω : ℝ)) U A B]
    rw [(sum_uniform_eq_iff hD _ _).mpr (cR A B hd hA hB hlt),
      (sum_uniform_eq_iff hD _ _).mpr (cT A B hd hA hB hlt)]
  · -- ③：`A ↔ B` 对称（Case 3 是 `clanPairComplCount` 在 `(B, A)` 的实例）
    intro A B hd hA hB hlt
    have hd' : Disjoint B A := hd.symm
    have hR := cR B A hd' hB hA (by omega)
    have hT := cT B A hd' hB hA (by omega)
    have hsub := sum_pair_R_eq_sub (fun _ => 1 / (Fintype.card Ω : ℝ)) U B A
    have e1 := (sum_uniform_eq_iff hD _ _).mpr hR
    have e2 := (sum_uniform_eq_iff hD _ _).mpr hT
    -- 把 `(B, A)` 形态的三支换回 `(A, B)` 形态的滤子
    have hB' : (Finset.univ : Finset Ω).filter
        (fun ω => (U ω).IsClade (Aᶜ.image Sum.inl) ∧
          (U ω).IsClade (B.image Sum.inl) ∧ ¬ (U ω).IsClade (A.image Sum.inl))
        = (Finset.univ : Finset Ω).filter
          (fun ω => (U ω).IsClade (B.image Sum.inl) ∧
            (U ω).IsClade (Aᶜ.image Sum.inl) ∧ ¬ (U ω).IsClade (A.image Sum.inl)) := by
      apply Finset.filter_congr
      intro ω _
      tauto
    rw [hB', hsub, e1, e2]
  · -- 穷尽支
    intro A B hd hA hB heq
    exact (sum_uniform_eq_iff hD _ _).mpr (cE A B hd hA hB heq)

/-! ## 7. ④⑤ 的**条件载体**：`p_{n−b}(a)` 是什么（无条件）

文献把 ④ 读成「先要求 `B | X−B` 是根分裂（概率 `p̂_n(b, n−b)`），再在剩下的
`n−b` 叶子上要求 `A` 成 clade（概率 `p_{n−b}(a)`）」。后一半的载体就是下面这条：
**在 `m` 叶的 ranked 模型上，「`A` 是非单点块」的概率恰是 `pn m a`**（`2 ≤ a ≤ m−2`）。 -/

/-- ★★★ **`pn` 的载体**（无条件）：`#{ω : A 是非单点块} / H m = pn m |A|`。

这就是 `p_{n−b}(a)` 的语义 —— 4 ⑤ 的**条件事件**「在 `n−b` 叶的子树上 `A` 成 clade」
的概率**已经落地**（走 `card_blockHistories_univ`，不需 `blockInterCount`）。 -/
theorem pnEvent_eq_pn (m : ℕ) {A : Finset (Fin m)} (h1 : 2 ≤ A.card) (h2 : A.card ≤ m - 2) :
    ((blockHistories m A).card : ℝ) / RankedGeneTree.H m = pn m A.card := by
  rw [card_blockHistories_univ m h1 h2, div_eq_iff (ne_of_gt (H_pos m))]
  ring

/-! ### 7b. 载体在边界切片上的行为（如实登记）

`pn m a` 只在 `2 ≤ a ≤ m−2` 上等于「非单点块」的条数比。两个**边界**切片：

* `a = 1`：`{x}` 恒是 clan（`isClade_of_trivial`），概率 `= 1 = pn m 1` —— **成立**；
* `a = m−1`：`A` 在**无根**模型上**永不**是非单点块（块基数 `≤ m−2`），条数 `= 0`，
  而 `pn m (m−1) = 2/(m(m−1)) ≠ 0` —— **不成立**（那是有根树的 outgroup 结构，
  本库的无根 `Cladogram` 没有对应物）。 -/

/-- ★★ **`pn m 1 = 1`**（Lemma 4.2 在 `a = 1` 的取值；`{x}` 恒是 clan）。 -/
theorem pn_one {m : ℕ} (hm : 2 ≤ m) : pn m 1 = 1 := by
  unfold pn
  rw [ite_eq_right (by omega : ¬ (1 = 0 ∨ m ≤ 1)), Nat.choose_one_right]
  have hm0 : (m : ℝ) ≠ 0 := by
    have : (0 : ℕ) < m := by omega
    exact_mod_cast this.ne'
  push_cast
  field_simp
  norm_num

/-- ★★ **单点集的 clan 事件集是全集**（`m ≥ 3`）：`{x}` 恒是 clan。 -/
theorem clanHistories_singleton {m : ℕ} (hm : 2 ≤ m) (h3 : 3 ≤ m) (x : Fin m) :
    clanHistories m hm {x} = Finset.univ := by
  classical
  ext ω
  simp only [clanHistories, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
  rw [rankedTreeCladogram_eq_of_three (n := m) hm h3]
  exact isClade_of_trivial h3 ω (Or.inl ⟨x, rfl⟩)

/-- ★★ **`a = 1` 切片的事件概率 `= 1`**（均匀律）。 -/
theorem clanEvent_singleton {m : ℕ} (hm : 2 ≤ m) (h3 : 3 ≤ m) (x : Fin m) :
    clanEvent m hm {x} = 1 := by
  unfold clanEvent
  rw [clanHistories_singleton hm h3 x]
  exact CoalescentHistoryCount.sum_rankedTree_uniform m hm

/-- ★★ **`p_{n−b}(a)` 载体在 `a = 1` 的切片**：`clanEvent m {x} = pn m 1`。
⇒ ④⑤ 的「子树条件概率」在 `|A| = 1` 上**已经落地**（与 `|A| ≥ 2` 的
★★★ `pnEvent_eq_pn` 合起来覆盖 `1 ≤ |A| ≤ m−2`）。 -/
theorem clanEvent_singleton_eq_pn {m : ℕ} (hm : 2 ≤ m) (h3 : 3 ≤ m) (x : Fin m) :
    clanEvent m hm {x} = pn m 1 := by
  rw [clanEvent_singleton hm h3 x, pn_one (by omega)]

/-- ⚠ **边界切片 `|A| = m−1`**：`A` 在无根 ranked 模型上**永不**是非单点块，
故 `#{ω : A ∈ blockFamily} = 0`（而 `pn m (m−1) = 2/(m(m−1)) ≠ 0`）。
⇒ 本库的**无根**载体不覆盖 `p_{n−b}(a)` 的 `a = n−b−1` 切片（那里需要**有根** clade
／outgroup 结构）。★ 这不是文献公式的问题（渲染页 p.12–13 逐字核过），是**载体**的缺口。 -/
theorem card_blockHistories_eq_zero_of_card_compl_one {m : ℕ} {A : Finset (Fin m)}
    (h : Aᶜ.card = 1) : (blockHistories m A).card = 0 := by
  classical
  have h0 : ∀ ω, ω ∉ blockHistories m A := by
    intro ω hω
    rw [mem_blockHistories] at hω
    have h2 := card_le_of_mem_blockFamily hω
    have h2' := two_le_card_of_mem_blockFamily hω
    rw [card_compl_eq m A] at h
    omega
  have hempty : blockHistories m A = ∅ := by
    ext ω
    simp [h0 ω]
  rw [hempty, Finset.card_empty]

/-- ★★ **`pnHatExh` 的组合形态**：`p̂_n(b, n−b) = H b · H (n−b) · C(n−2, b−1) / H n`
（`2 ≤ b ≤ n−2`）。右端分子就是「**根分裂恰为 `B | Bᶜ`** 的条数」的组合式
（两侧内部成树 × 交错），即 N2 的 `blockInterCount` 那条线的货币。 -/
theorem pnHatExh_eq_combinatorial {N b : ℕ} (h1 : 2 ≤ b) (h2 : b ≤ N - 2) :
    pnHatExh N b
      = RankedGeneTree.H b * RankedGeneTree.H (N - b)
          * (((N - 2).choose (b - 1) : ℕ) : ℝ) / RankedGeneTree.H N := by
  rw [eq_div_iff (ne_of_gt (H_pos N)), mul_comm (pnHatExh N b) (RankedGeneTree.H N)]
  exact H_mul_pnHatExh_eq h1 h2

/-- ★★★ **④⑤ 的两种形态等价**（算术桥）：在 `|Ω| = H N` 的模型上，
`p̂_n(b, n−b) · p_{n−b}(a) · |Ω|` ＝ `[H b · C(n−2,b−1)] · [H (n−b) · p_{n−b}(a)]`。

右端第二个因子由 ★★★ `pnEvent_eq_pn` 就是「子树（`n−b` 叶）上 `A` 成块的**条数**」，
故 ④⑤ ＝ 「根分裂 `B | Bᶜ` 的条数」×「子树上 `A` 成块的条数」—— 与 N2 的
`blockInterCount` **同一类**计数（这就是「④⑤ 只等 N2 的律」的精确含义）。 -/
theorem tripleCount_combinatorial {N : ℕ} {Ω : Type*} [Fintype Ω]
    (hDN : (Fintype.card Ω : ℝ) = RankedGeneTree.H N)
    {A B : Finset (Fin N)} (h1 : 2 ≤ B.card) (h2 : B.card ≤ N - 2) :
    pnHatExh N B.card * pn (N - B.card) A.card * (Fintype.card Ω : ℝ)
      = RankedGeneTree.H B.card * (((N - 2).choose (B.card - 1) : ℕ) : ℝ)
          * (RankedGeneTree.H (N - B.card) * pn (N - B.card) A.card) := by
  have hH : RankedGeneTree.H N ≠ 0 := ne_of_gt (H_pos N)
  rw [pnHatExh_eq_combinatorial h1 h2, hDN]
  field_simp

/-! ## 8. `n = 6, a = b = 2` 的五项数值审计（内核核过）

把 Theorem 6.3(ii) 的五个项各自取值核一遍（复核**符号与量级**，也复核 ④⑤ 的系数）：

* `rn 6 2 2 = 17/675`（①，Case 5）；
* `Rn 6 2 4 = 2/225`（②③ 首项，Case 2/3）；
* `p̂_6(2, 4) · p_4(2) = (2/75) · (2/9) = 4/675`（④⑤）；
* 合计 `17/675 + 2·(2/225) − 2·(4/675) = 7/225 = qn 6 2 2`（库内 ★ `qn_six_two_two`）。

★ **独立交叉验证**（★D 的机器留痕）：论文 p.13 另给 `q(2,2,2) = 1/75`、
`q′(2,2,2) = 1/15`，且 `q′ = 3·qn(2,2) − 2q`；库内 `qTriple_two_two_two` 与
`qConvex_two_two_two` 已把这两个数核过 ⇒ 五项系数与论文自洽，**无 ★D 更正**。 -/

/-- ★★ **五项数值审计**（`n = 6, a = b = 2`）。 -/
theorem term_audit_six_two_two :
    rn 6 2 2 = 17 / 675 ∧ Rn 6 2 4 = 2 / 225
      ∧ pnHatExh 6 2 * pn 4 2 = 4 / 675 := by
  refine ⟨?_, ?_, ?_⟩
  · unfold rn Gn
    norm_num [Nat.choose, Nat.factorial]
  · unfold Rn
    norm_num [Nat.choose, Nat.factorial]
  · unfold pnHatExh pn
    norm_num [Nat.choose, Nat.factorial]


/-! ## 9. ★ W33：载体**实例化**与穷尽支（`clanExhaustiveCount` 落地）

### 9.0 为什么必须有这一节（★D 记录）

§5 的 4 条计数 `def` 都是对**任意** `U : Ω → Cladogram (Fin N ⊕ Unit)` 陈述的；
对一般 `U` 它们**为假**：取 `U` 恒为「根叶 ＋ 4 叶星形」（`N = 4`）、`|A| = 2`，
则左端 `#{ω : A 是边的一侧} = 0`，右端 `qnExhaustive 2 2 · |Ω| = |Ω|/3 ≠ 0`。
而库内 `Cladogram (X ⊕ Unit)` **全是消费者、生产者 0 个** ⇒ 先补生产者
（★★★ `Cladogram.attachRoot`，`Phylo/CladogramBuild.lean` §9），本节把它**实例化**成
`RankedTree n` 上的具体载体，并交付 ★★★ `isClanMinusRoot_rootedCarrier_iff`
（把载体的 `IsClanMinusRoot` 与 `rankedTreeCladogram` 的 `IsClade` 对齐 —— 这是 ZDS Lemma 6.1
在两条载体之间的**合流**），随后 `clanExhaustiveCount` 由已收口的 `YHKClanLawGap` 直接兑换。

### 9.1 载体：`cladesOf` 的镶嵌族挂上根叶

★ **为什么用 `cladesOf`（有根 clade 族）而不是 `rankedTreeCladogram` 的 split 族**：
`attachRoot` 把根叶 `Sum.inr ()` 放在**每条** split 的 `sideB`，只有**镶嵌族**才保相容性；
`cladesOf n ω.1` 恰是镶嵌族（★★ `laminarFamily_cladesOf`），而 `rankedTreeCladogram` 的
split 族**含两个朝向**、不镶嵌（反例 `Fin 3` 上 `{1,2}` 与 `{1,3}`）⇒ 推上去不相容。
这一条是 W33 C 步实测出来的**更正**，见 `Phylo/CladogramBuild.lean` §9 的模块注记。 -/

/-- `cladesOf` 的成员**非空**（块是 `univ.filter`，含代表元本身）。 -/
theorem nonempty_of_mem_cladesOf {m : ℕ} {f : Fin (m - 1) → Fin m × Fin m}
    {C : Finset (Fin m)} (h : C ∈ RankedGeneTree.cladesOf m f) : C.Nonempty := by
  rw [RankedGeneTree.cladesOf, Finset.mem_biUnion] at h
  obtain ⟨L, -, hL⟩ := h
  rw [RankedGeneTree.blocksOf, Finset.mem_image] at hL
  obtain ⟨w, -, hw⟩ := hL
  rw [← hw]
  exact ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ w, rfl⟩⟩

/-- 单点集是 `cladesOf` 的成员（第 `0` 层的块 = 单点集）。 -/
theorem singleton_mem_cladesOf {m : ℕ} (f : Fin (m - 1) → Fin m × Fin m) (x : Fin m) :
    ({x} : Finset (Fin m)) ∈ RankedGeneTree.cladesOf m f := by
  have hx : (0 : ℕ) ∈ Finset.range m := Finset.mem_range.mpr (Fin.pos x)
  refine Finset.mem_biUnion.mpr ⟨0, hx, ?_⟩
  refine Finset.mem_image.mpr ⟨x, Finset.mem_univ x, ?_⟩
  have h0 : RankedGeneTree.chainMap m f 0 = id := rfl
  ext z
  rw [h0]
  rw [Finset.mem_filter, Finset.mem_singleton]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

/-- `A.card = m − 1` ⟹ `A` 是某个单点集的补。 -/
theorem exists_compl_singleton_of_card {m : ℕ} {A : Finset (Fin m)} (hm : 0 < m)
    (h : A.card = m - 1) : ∃ x, A = ({x} : Finset (Fin m))ᶜ := by
  have hne : A ≠ Finset.univ := by
    intro hU
    rw [hU, Finset.card_univ, Fintype.card_fin] at h
    omega
  have hx : ∃ x : Fin m, x ∉ A := by
    by_contra hcon
    exact hne (Finset.eq_univ_of_forall fun x => by
      by_contra hxa
      exact hcon ⟨x, hxa⟩)
  obtain ⟨x, hx⟩ := hx
  refine ⟨x, ?_⟩
  have hsub : A ⊆ ({x} : Finset (Fin m))ᶜ := by
    intro z hz
    rw [Finset.mem_compl, Finset.mem_singleton]
    exact fun hzx => hx (hzx ▸ hz)
  have hcard : (({x} : Finset (Fin m))ᶜ).card ≤ A.card := by
    rw [Finset.card_compl, Fintype.card_fin, Finset.card_singleton, h]
  exact Finset.eq_of_subset_of_card_le hsub hcard

/-- ★★ **`cladesOf` 成员的三分**（`A.card < m` 时）：

`C ∈ cladesOf` ∧ `|C| < m` ⟹ `|C| = 1`（平凡）或 `C ∈ blockFamily`（非单点真块）
或 `|C| = m − 1`（根分裂的一侧）。

★ 这是「有根 clade 族」与 `blockFamily`（`[2, m−2]` 档）之间**唯一的**记账差异：
`attachRoot` 的 `IsClade` 认 `cladesOf`，而 `rankedTreeCladogram` 的 `IsClade`
（经 ★★★ `mem_clanHistories_iff`）认 `blockFamily` ＋ 平凡支 —— 两条账在
`|C| = m − 1` 上由「单点集的补恒是 clan」（`isClade_compl`）对齐。 -/
theorem card_eq_one_or_mem_blockFamily_or_card_pred {m : ℕ}
    {ω : RankedGeneTree.RankedTree m} {C : Finset (Fin m)}
    (hC : C ∈ RankedGeneTree.cladesOf m ω.1) (hlt : C.card < m) :
    C.card = 1 ∨ C ∈ blockFamily m ω ∨ C.card = m - 1 := by
  have hne : 1 ≤ C.card := Finset.card_pos.mpr (nonempty_of_mem_cladesOf hC)
  by_cases h1 : C.card = 1
  · exact Or.inl h1
  by_cases h3 : C.card ≤ m - 2
  · refine Or.inr (Or.inl (mem_blockFamily.mpr ⟨hC, ?_, h3⟩))
    omega
  · exact Or.inr (Or.inr (by omega))

/-- ★★ **载体**（`RankedTree m → Cladogram (Fin m ⊕ Unit)`）：`ω` 的有根 clade 族挂上根叶。
这是 §5 那 4 条计数 `def` 的 `U` 槽的**具体**填法。 -/
noncomputable def rootedCarrier (m : ℕ) (h3 : 3 ≤ m)
    (ω : RankedGeneTree.RankedTree m) : Cladogram.{0, 0} (Fin m ⊕ Unit) :=
  Cladogram.attachRoot (RankedGeneTree.cladesOf m ω.1)
    (RankedGeneTree.laminarFamily_cladesOf ω.1)
    (by rw [Fintype.card_sum, Fintype.card_unit, Fintype.card_fin]; omega)

/-- ★★ **载体的 `IsClade` 完全刻画**（★ `attachRoot_isClade` 的实例；三支 = clade / 单点 / 全集）。 -/
theorem rootedCarrier_isClade {m : ℕ} (h3 : 3 ≤ m) (ω : RankedGeneTree.RankedTree m)
    (A : Finset (Fin m)) :
    (rootedCarrier m h3 ω).IsClade (A.image (Sum.inl : Fin m → Fin m ⊕ Unit)) ↔
      A ∈ RankedGeneTree.cladesOf m ω.1 ∨ A.card = 1 ∨ A = Finset.univ :=
  Cladogram.attachRoot_isClade (L := RankedGeneTree.cladesOf m ω.1)
    (RankedGeneTree.laminarFamily_cladesOf ω.1)
    (fun _ h => nonempty_of_mem_cladesOf h)
    (by rw [Fintype.card_sum, Fintype.card_unit, Fintype.card_fin]; omega) A

/-- ★★★ **载体对齐**（W33 的核心一步）：在合法基数域上

  「`A` 是 `rootedCarrier m ω` 的**去根 clan**」**⟺**「`A` 是 `rankedTreeCladogram m ω` 的 **clan**」。

左端 = `IsClanMinusRoot`（`IsClade (A.image inl) ∨ IsClade (Aᶜ.image inl)`，★★ `isClanMinusRoot_iff`），
右端 = ★★★ `mem_clanHistories_iff` 的四支（`blockFamily` 两侧 ＋ 两种平凡支）。

★ 三支的对应关系（这就是「记账」的全部内容）：
`|A| = 1` ↦ 平凡支 `A = {x}`；`|A| = m−1` ↦ 平凡支 `A = {x}ᶜ`；`2 ≤ |A| ≤ m−2` ↦ `blockFamily`。 -/
theorem isClanMinusRoot_rootedCarrier_iff {m : ℕ} (hm : 2 ≤ m) (h3 : 3 ≤ m)
    (ω : RankedGeneTree.RankedTree m) {A : Finset (Fin m)}
    (hA : A.Nonempty) (hlt : A.card < m) :
    IsClanMinusRoot (rootedCarrier m h3 ω) A ↔ (rankedTreeCladogram m hm ω).IsClade A := by
  have hpos : 1 ≤ A.card := Finset.card_pos.mpr hA
  have hcompl : Aᶜ.card = m - A.card := card_compl_eq m A
  have hcompl_pos : 1 ≤ Aᶜ.card := by rw [hcompl]; omega
  have hcompl_lt : Aᶜ.card < m := by rw [hcompl]; omega
  rw [isClanMinusRoot_iff, rootedCarrier_isClade h3 ω A, rootedCarrier_isClade h3 ω Aᶜ]
  have hR : (rankedTreeCladogram m hm ω).IsClade A ↔
      A ∈ blockFamily m ω ∨ Aᶜ ∈ blockFamily m ω ∨
        (∃ x : Fin m, A = {x}) ∨ (∃ x : Fin m, A = {x}ᶜ) := by
    have h := mem_clanHistories_iff (n := m) hm h3 A ω
    rw [clanHistories_eq_filter] at h
    simpa using h
  rw [hR]
  -- 把「`C ∈ cladesOf`」按基数三分（对 `A` 与 `Aᶜ` 各一次）
  have hsplit : ∀ C : Finset (Fin m), C ∈ RankedGeneTree.cladesOf m ω.1 → C.card < m →
      (C.card = 1 ∨ C ∈ blockFamily m ω ∨ C.card = m - 1) :=
    fun C hC hlt => card_eq_one_or_mem_blockFamily_or_card_pred hC hlt
  constructor
  · rintro (hLeft | hRight)
    · rcases hLeft with hAc | hA1 | hAu
      · -- `A ∈ cladesOf`
        rcases (hsplit A hAc hlt) with h1 | h2 | h3'
        · obtain ⟨x, hx⟩ := Finset.card_eq_one.mp h1
          subst hx
          exact Or.inr (Or.inr (Or.inl ⟨x, rfl⟩))
        · exact Or.inl h2
        · obtain ⟨x, hx⟩ := exists_compl_singleton_of_card (by omega : 0 < m) h3'
          exact Or.inr (Or.inr (Or.inr ⟨x, hx⟩))
      · -- `A.card = 1`
        obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hA1
        subst hx
        exact Or.inr (Or.inr (Or.inl ⟨x, rfl⟩))
      · -- `A = univ` 与 `A.card < m` 矛盾
        exfalso
        rw [hAu, Finset.card_univ, Fintype.card_fin] at hlt
        omega
    · rcases hRight with hAcc | hAc1 | hAcu
      · -- `Aᶜ ∈ cladesOf`
        rcases (hsplit Aᶜ hAcc hcompl_lt) with h1 | h2 | h3'
        · obtain ⟨x, hx⟩ := Finset.card_eq_one.mp h1
          refine Or.inr (Or.inr (Or.inr ⟨x, ?_⟩))
          rw [← hx, compl_compl]
        · exact Or.inr (Or.inl h2)
        · obtain ⟨x, hx⟩ := exists_compl_singleton_of_card (by omega : 0 < m) h3'
          refine Or.inr (Or.inr (Or.inl ⟨x, ?_⟩))
          simpa using congrArg (fun S : Finset (Fin m) => Sᶜ) hx
      · -- `Aᶜ.card = 1`
        obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hAc1
        refine Or.inr (Or.inr (Or.inr ⟨x, ?_⟩))
        rw [← hx, compl_compl]
      · -- `Aᶜ = univ` 与 `Aᶜ.card < m` 矛盾
        exfalso
        rw [hAcu, Finset.card_univ, Fintype.card_fin] at hcompl_lt
        omega
  · rintro (hAb | hAbc | hS1 | hS2)
    · exact Or.inl (Or.inl (mem_cladesOf_of_mem_blockFamily hAb))
    · exact Or.inr (Or.inl (mem_cladesOf_of_mem_blockFamily hAbc))
    · obtain ⟨x, hx⟩ := hS1
      subst hx
      exact Or.inl (Or.inr (Or.inl (by simp)))
    · obtain ⟨x, hx⟩ := hS2
      refine Or.inr (Or.inr (Or.inl ?_))
      rw [hx]
      simp

/-- ★★ **`Fintype.card (RankedTree m) = H m`**（`H` 就是合并史的条数）。 -/
theorem card_rankedTree_eq_H (m : ℕ) (hm : 2 ≤ m) :
    ((Fintype.card (RankedGeneTree.RankedTree m) : ℕ) : ℝ) = RankedGeneTree.H m := by
  have h1 : Fintype.card (RankedGeneTree.RankedTree m)
      = (RankedGeneTree.mergeHistories m).card := by
    rw [RankedGeneTree.mergeHistories]
    exact Fintype.card_subtype _
  rw [h1]
  exact Phylo.Stat.CoalescentHistoryCount.card_mergeHistories_eq_H m (by omega)

/-- ★★★ **`A` 成 clan 的概率 = `clanProb m |A|`**（点态版，`|A| < m`、`A` 非空）。

★ 这是 ★★★ `yhkClanLawGap_holds` 的**逐点**形态（那里只给了 `∃ Ω, prob, tree`）：
本定理把见证**定死**成 `Ω = RankedTree m`、`prob ≡ 1/H m`、`tree = rankedTreeCladogram m hm`，
故可直接喂给 §5 的计数槽。三档与 `yhkClanLawGap_of_blockInterCount` 完全一致
（`|A| = 1` / `|A| = m−1` 走平凡切片，其余走块计数）。 -/
theorem clanEvent_eq_clanProb {m : ℕ} (hm : 2 ≤ m) {A : Finset (Fin m)}
    (hA : A.Nonempty) (hlt : A.card < m) :
    clanEvent m hm A = clanProb m A.card := by
  have hsum : (∑ _ω : RankedGeneTree.RankedTree m, (1 / RankedGeneTree.H m)) = 1 :=
    Phylo.Stat.CoalescentHistoryCount.sum_rankedTree_uniform m hm
  have hpos : 1 ≤ A.card := Finset.card_pos.mpr hA
  by_cases hcard1 : A.card = 1
  · unfold clanEvent
    rw [clanHistories_eq_filter]
    exact yhkClanLawGap_trivial_card_slice hm (fun _ => 1 / RankedGeneTree.H m) hsum
      (fun ω => rankedTreeCladogram m hm ω) hA (Or.inl hcard1)
  · by_cases hcardn : A.card = m - 1
    · unfold clanEvent
      rw [clanHistories_eq_filter]
      exact yhkClanLawGap_trivial_card_slice hm (fun _ => 1 / RankedGeneTree.H m) hsum
        (fun ω => rankedTreeCladogram m hm ω) hA (Or.inr hcardn)
    · have h1 : 2 ≤ A.card := by omega
      have h2 : A.card ≤ m - 2 := by omega
      have h3 : 3 ≤ m := by omega
      unfold clanEvent
      rw [clanHistories_eq_filter]
      exact clanEvent_eq_clanProb_of_blockCount hm h3 h1 h2 (blockInterCount_holds m A h1 h2)

/-- ★★★ **穷尽支的计数化落地**（`a + b = m`）：`#{ω : A 是去根 clan} = qnExhaustive a b · |Ω|`。

三条兑换各就各位：
1. 滤子对齐：★★★ `isClanMinusRoot_rootedCarrier_iff`（载体 ↔ `rankedTreeCladogram`）；
2. 概率对齐：★★★ `clanEvent_eq_clanProb`（YHK 律，点态版）；
3. 闭形式对齐：★★★ `qnExhaustive_eq_clanProb`（Theorem 6.3(i) ⟸ Lemma 6.2，`a + b = m`）。 -/
theorem clanExhaustiveCount_rootedCarrier {m : ℕ} (hm : 2 ≤ m) (h3 : 3 ≤ m) :
    clanExhaustiveCount m (RankedGeneTree.RankedTree m) (fun ω => rootedCarrier m h3 ω) := by
  intro A B hd hA hB heq
  have hbpos : 0 < B.card := Finset.card_pos.mpr hB
  have hlt : A.card < m := by omega
  have hfilter : (Finset.univ.filter (fun ω => IsClanMinusRoot (rootedCarrier m h3 ω) A))
      = clanHistories m hm A := by
    rw [clanHistories_eq_filter]
    refine Finset.filter_congr (fun ω _ => ?_)
    exact isClanMinusRoot_rootedCarrier_iff hm h3 ω hA hlt
  have hE : clanEvent m hm A
      = ((clanHistories m hm A).card : ℝ) * (1 / RankedGeneTree.H m) := by
    unfold clanEvent
    rw [Finset.sum_const, nsmul_eq_mul]
  have hclan := clanEvent_eq_clanProb hm hA hlt
  rw [hE] at hclan
  have hcard := card_rankedTree_eq_H m hm
  have hqa := qnExhaustive_eq_clanProb (a := A.card) (b := B.card)
    (Finset.card_pos.mpr hA) (Finset.card_pos.mpr hB)
  rw [heq] at hqa
  rw [hfilter, hqa, hcard]
  have hH : RankedGeneTree.H m ≠ 0 := ne_of_gt (H_pos m)
  rw [← hclan]
  field_simp

open Phylo.Stat.CladeCount
open Phylo.Stat.CoalescentHistoryCount

/-! ## §10.0 桥：`cladesOf` ↔ `IsCladeH`，`RankedTree` ↔ `mhFinset` -/

/-- `chainMap n f L` 与 `gchain (n−1) f L` 是同一个项。 -/
theorem chainMap_eq_gchain {n : ℕ} (f : Fin (n - 1) → Fin n × Fin n) (L : ℕ) :
    RankedGeneTree.chainMap n f L = gchain (n - 1) f L := rfl

/-- ★★ **`cladesOf` 与 `IsCladeH` 是同一个概念**（`univ`、`n−1` 步，`n ≥ 1`）。 -/
theorem mem_cladesOf_iff_isCladeH {n : ℕ} (hn : 1 ≤ n)
    (f : Fin (n - 1) → Fin n × Fin n) (A : Finset (Fin n)) :
    A ∈ RankedGeneTree.cladesOf n f
      ↔ IsCladeH (Finset.univ : Finset (Fin n)) (n - 1) f A := by
  rw [isCladeH_iff]
  constructor
  · intro h
    rw [RankedGeneTree.cladesOf, Finset.mem_biUnion] at h
    obtain ⟨L, hL, hb⟩ := h
    rw [Finset.mem_range] at hL
    rw [RankedGeneTree.blocksOf, Finset.mem_image] at hb
    obtain ⟨w, -, hw⟩ := hb
    refine ⟨L, by omega, w, ?_, ?_⟩
    · rw [← hw]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ w, rfl⟩
    · rw [← chainMap_eq_gchain]
      exact hw.symm
  · rintro ⟨L, hL, w, hw, hA⟩
    rw [RankedGeneTree.cladesOf, Finset.mem_biUnion]
    refine ⟨L, Finset.mem_range.mpr (by omega), ?_⟩
    rw [RankedGeneTree.blocksOf, Finset.mem_image]
    refine ⟨w, Finset.mem_univ w, ?_⟩
    rw [chainMap_eq_gchain, hA]
    rfl

/-- ★★ **载体对齐（`iff` 形态）**：在合法基数域上，`A` 的像 `A.image inl` 是
`rootedCarrier m ω` 的 clade ⟺ `A` 是 `ω` 的有根 clade。 -/
theorem rootedCarrier_isClade_iff {m : ℕ} (h3 : 3 ≤ m) (ω : RankedGeneTree.RankedTree m)
    {A : Finset (Fin m)} (hA : A.Nonempty) (hlt : A.card < m) :
    (rootedCarrier m h3 ω).IsClade (A.image (Sum.inl : Fin m → Fin m ⊕ Unit))
      ↔ A ∈ RankedGeneTree.cladesOf m ω.1 := by
  classical
  rw [rootedCarrier_isClade h3 ω A]
  constructor
  · rintro (h | h | h)
    · exact h
    · obtain ⟨x, rfl⟩ := Finset.card_eq_one.mp h
      exact singleton_mem_cladesOf ω.1 x
    · exfalso
      rw [h, Finset.card_univ, Fintype.card_fin] at hlt
      omega
  · exact Or.inl

/-- ★★ **`RankedTree` 的滤子计数 = `mhFinset` 的滤子计数**（双射 `ω ↦ ω.1`）。 -/
theorem card_rankedTree_filter_eq_mhFinset {m : ℕ}
    (P : (Fin (m - 1) → Fin m × Fin m) → Prop) [DecidablePred P] :
    ((Finset.univ : Finset (RankedGeneTree.RankedTree m)).filter (fun ω => P ω.1)).card
      = ((mhFinset m (m - 1) (Finset.univ : Finset (Fin m))).filter P).card := by
  classical
  refine Finset.card_bij (fun ω _ => ω.1) ?_ ?_ ?_
  · intro ω hω
    rw [Finset.mem_filter] at hω ⊢
    exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (isMH_univ_iff m ω.1).mpr ω.2⟩, hω.2⟩
  · intro ω₁ _ ω₂ _ h
    exact Subtype.ext h
  · intro f hf
    rw [Finset.mem_filter] at hf
    obtain ⟨hf1, hfP⟩ := hf
    rw [mhFinset, Finset.mem_filter] at hf1
    exact ⟨⟨f, (isMH_univ_iff m f).mp hf1.2⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hfP⟩, rfl⟩

/-- ★★★ **单 clade 计数（`cladesOf` 货币）**：`1 ≤ |A| ≤ m−1` 时
`#{ω : A 是 ω 的有根 clade} = H m · pn m |A|`。 -/
theorem card_cladesOf_eq_H_mul_pn {m : ℕ} {A : Finset (Fin m)}
    (h1 : 1 ≤ A.card) (h2 : A.card ≤ m - 1) :
    ((↑((Finset.univ : Finset (RankedGeneTree.RankedTree m)).filter
      (fun ω => A ∈ RankedGeneTree.cladesOf m ω.1)).card : ℝ))
      = RankedGeneTree.H m * pn m A.card := by
  classical
  have hmh := card_rankedTree_filter_eq_mhFinset
    (P := fun f => A ∈ RankedGeneTree.cladesOf m f)
  rw [show ((Finset.univ : Finset (RankedGeneTree.RankedTree m)).filter
        (fun ω => A ∈ RankedGeneTree.cladesOf m ω.1)).card
      = ((mhFinset m (m - 1) (Finset.univ : Finset (Fin m))).filter
          (fun f => A ∈ RankedGeneTree.cladesOf m f)).card from hmh]
  have hEq : ((mhFinset m (m - 1) (Finset.univ : Finset (Fin m))).filter
        (fun f => A ∈ RankedGeneTree.cladesOf m f))
      = (mhFinset m (m - 1) (Finset.univ : Finset (Fin m))).filter
          (fun f => IsCladeH (Finset.univ : Finset (Fin m)) (m - 1) f A) :=
    Finset.filter_congr (fun f _ => mem_cladesOf_iff_isCladeH (by omega) f A)
  rw [hEq]
  have h := cladeCountS_eq_H_mul_pn (m - 1) m (Finset.univ : Finset (Fin m)) A
    (by rw [Finset.card_univ, Fintype.card_fin]; omega)
    (Finset.subset_univ _) h1 (by omega)
  rw [show m - 1 + 1 = m from by omega] at h
  exact h

/-! ## §10.1 嵌套两 clade 的联合计数：定义与头分解 -/

/-- 嵌套两 clade 的**联合计数**：`s` 上 `m` 步合并史中 `A`、`C` **同时**是 clade 的条数
（`A ⊆ C`）。 -/
def nestCount (N m : ℕ) (s A C : Finset (Fin N)) : ℕ :=
  ((mhFinset N m s).filter (fun f => IsCladeH s m f A ∧ IsCladeH s m f C)).card

/-- `nestCount` 的头分解（照 `cladeCountS_succ_eq_sum` 的写法）。 -/
theorem nestCount_succ_eq_sum {N m : ℕ} (s A C : Finset (Fin N)) :
    nestCount N (m + 1) s A C
      = ∑ p : PairIn N s,
          ((headFiber (m := m) s p).filter
            (fun f => IsCladeH s (m + 1) f A ∧ IsCladeH s (m + 1) f C)).card := by
  unfold nestCount
  rw [mhFinset_succ_eq_biUnion (m := m) s]
  have hunion : ((Finset.univ : Finset (PairIn N s)).biUnion (headFiber (m := m) s)).filter
        (fun f => IsCladeH s (m + 1) f A ∧ IsCladeH s (m + 1) f C)
      = (Finset.univ : Finset (PairIn N s)).biUnion
          (fun p => (headFiber (m := m) s p).filter
            (fun f => IsCladeH s (m + 1) f A ∧ IsCladeH s (m + 1) f C)) := by
    ext f
    simp only [Finset.mem_filter, Finset.mem_biUnion, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨p, hp⟩, hP⟩
      exact ⟨p, hp, hP⟩
    · rintro ⟨p, hp, hP⟩
      exact ⟨⟨p, hp⟩, hP⟩
  rw [hunion]
  have hdisj : Set.PairwiseDisjoint (↑(Finset.univ : Finset (PairIn N s)))
      (fun p => (headFiber (m := m) s p).filter
        (fun f => IsCladeH s (m + 1) f A ∧ IsCladeH s (m + 1) f C)) := by
    intro p _ q _ hpq
    exact Finset.disjoint_of_subset_left (Finset.filter_subset _ _)
      (Finset.disjoint_of_subset_right (Finset.filter_subset _ _) (headFiber_disjoint hpq))
  rw [Finset.card_biUnion hdisj]

/-! ## §10.2 四种第一步情形的搬运 -/

/-- 情形一：第一步的两端都在 `A` 里。 -/
theorem card_headFiber_nest_both {N m : ℕ} (s A C : Finset (Fin N)) (hAC : A ⊆ C)
    (hCs : C ⊆ s) (hA2 : 2 ≤ A.card) (hC2 : 2 ≤ C.card) (p : PairIn N s)
    (hx : p.1.1 ∈ A) (hy : p.1.2 ∈ A) :
    ((headFiber (m := m) s p).filter
        (fun f => IsCladeH s (m + 1) f A ∧ IsCladeH s (m + 1) f C)).card
      = nestCount N m (s.erase p.1.2) (A.erase p.1.2) (C.erase p.1.2) := by
  classical
  have hAs : A ⊆ s := fun z hz => hCs (hAC hz)
  refine (card_headFiber_filter s p
    (fun f => IsCladeH s (m + 1) f A ∧ IsCladeH s (m + 1) f C)
    (fun g => IsCladeH (s.erase p.1.2) m g (A.erase p.1.2) ∧
      IsCladeH (s.erase p.1.2) m g (C.erase p.1.2)) ?_).trans rfl
  intro f h0 _
  rw [isCladeH_tail_both (x := p.1.1) (y := p.1.2) h0 p.2.2.2 p.2.2.1 hAs hx hy hA2,
    isCladeH_tail_both (x := p.1.1) (y := p.1.2) h0 p.2.2.2 p.2.2.1 hCs
      (hAC hx) (hAC hy) hC2]

/-- 情形二：第一步的两端都在 `C \ A` 里（`A` 不动，`C` 缩 `y`）。 -/
theorem card_headFiber_nest_mid {N m : ℕ} (s A C : Finset (Fin N)) (hAC : A ⊆ C)
    (hCs : C ⊆ s) (hA2 : 2 ≤ A.card) (hC2 : 2 ≤ C.card) (p : PairIn N s)
    (hx : p.1.1 ∉ A) (hy : p.1.2 ∉ A) (hxc : p.1.1 ∈ C) (hyc : p.1.2 ∈ C) :
    ((headFiber (m := m) s p).filter
        (fun f => IsCladeH s (m + 1) f A ∧ IsCladeH s (m + 1) f C)).card
      = nestCount N m (s.erase p.1.2) A (C.erase p.1.2) := by
  classical
  have hAs : A ⊆ s := fun z hz => hCs (hAC hz)
  refine (card_headFiber_filter s p
    (fun f => IsCladeH s (m + 1) f A ∧ IsCladeH s (m + 1) f C)
    (fun g => IsCladeH (s.erase p.1.2) m g A ∧
      IsCladeH (s.erase p.1.2) m g (C.erase p.1.2)) ?_).trans rfl
  intro f h0 _
  rw [isCladeH_tail_none (x := p.1.1) (y := p.1.2) h0 p.2.2.2 p.2.1 p.2.2.1 hAs hx hy hA2,
    isCladeH_tail_both (x := p.1.1) (y := p.1.2) h0 p.2.2.2 p.2.2.1 hCs hxc hyc hC2]

/-- 情形三：第一步的两端都在 `C` 外（两者都不动）。 -/
theorem card_headFiber_nest_out {N m : ℕ} (s A C : Finset (Fin N)) (hAC : A ⊆ C)
    (hCs : C ⊆ s) (hA2 : 2 ≤ A.card) (hC2 : 2 ≤ C.card) (p : PairIn N s)
    (hx : p.1.1 ∉ C) (hy : p.1.2 ∉ C) :
    ((headFiber (m := m) s p).filter
        (fun f => IsCladeH s (m + 1) f A ∧ IsCladeH s (m + 1) f C)).card
      = nestCount N m (s.erase p.1.2) A C := by
  classical
  have hAs : A ⊆ s := fun z hz => hCs (hAC hz)
  have hxA : p.1.1 ∉ A := fun hz => hx (hAC hz)
  have hyA : p.1.2 ∉ A := fun hz => hy (hAC hz)
  refine (card_headFiber_filter s p
    (fun f => IsCladeH s (m + 1) f A ∧ IsCladeH s (m + 1) f C)
    (fun g => IsCladeH (s.erase p.1.2) m g A ∧
      IsCladeH (s.erase p.1.2) m g C) ?_).trans rfl
  intro f h0 _
  rw [isCladeH_tail_none (x := p.1.1) (y := p.1.2) h0 p.2.2.2 p.2.1 p.2.2.1 hAs hxA hyA hA2,
    isCladeH_tail_none (x := p.1.1) (y := p.1.2) h0 p.2.2.2 p.2.1 p.2.2.1 hCs hx hy hC2]

/-- 情形四（其余）：第一步跨过 `A` 或 `C` 的边界 ⇒ 至少一个不是 clade ⇒ 贡献 `0`。 -/
theorem card_headFiber_nest_zero {N m : ℕ} (s A C : Finset (Fin N)) (hAC : A ⊆ C)
    (hCs : C ⊆ s) (hA2 : 2 ≤ A.card) (hC2 : 2 ≤ C.card) (p : PairIn N s)
    (h : ¬ ((p.1.1 ∈ A ∧ p.1.2 ∈ A)
          ∨ (p.1.1 ∉ A ∧ p.1.2 ∉ A ∧ p.1.1 ∈ C ∧ p.1.2 ∈ C)
          ∨ (p.1.1 ∉ C ∧ p.1.2 ∉ C))) :
    ((headFiber (m := m) s p).filter
        (fun f => IsCladeH s (m + 1) f A ∧ IsCladeH s (m + 1) f C)).card = 0 := by
  classical
  have hAs : A ⊆ s := fun z hz => hCs (hAC hz)
  rw [Finset.card_eq_zero, ← Finset.not_nonempty_iff_eq_empty]
  rintro ⟨f, hf⟩
  rw [Finset.mem_filter] at hf
  obtain ⟨hfhead, hfP⟩ := hf
  simp only [headFiber, Finset.mem_filter, Finset.mem_univ, true_and] at hfhead
  have hkill : (p.1.1 ∈ A ∧ p.1.2 ∉ A) ∨ (p.1.1 ∉ A ∧ p.1.2 ∈ A)
      ∨ (p.1.1 ∈ C ∧ p.1.2 ∉ C) ∨ (p.1.1 ∉ C ∧ p.1.2 ∈ C) := by
    by_cases hx : p.1.1 ∈ A
    · by_cases hy : p.1.2 ∈ A
      · exact absurd (Or.inl ⟨hx, hy⟩) h
      · exact Or.inl ⟨hx, hy⟩
    · by_cases hy : p.1.2 ∈ A
      · exact Or.inr (Or.inl ⟨hx, hy⟩)
      · by_cases hxc : p.1.1 ∈ C
        · by_cases hyc : p.1.2 ∈ C
          · exact absurd (Or.inr (Or.inl ⟨hx, hy, hxc, hyc⟩)) h
          · exact Or.inr (Or.inr (Or.inl ⟨hxc, hyc⟩))
        · by_cases hyc : p.1.2 ∈ C
          · exact Or.inr (Or.inr (Or.inr ⟨hxc, hyc⟩))
          · exact absurd (Or.inr (Or.inr ⟨hxc, hyc⟩)) h
  rcases hkill with ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩
  · exact (not_isCladeH_mixed (x := p.1.1) (y := p.1.2) hfhead.1 p.2.1 p.2.2.1 hAs hA2
      (Or.inl ⟨hx, hy⟩)) hfP.1
  · exact (not_isCladeH_mixed (x := p.1.1) (y := p.1.2) hfhead.1 p.2.1 p.2.2.1 hAs hA2
      (Or.inr ⟨hx, hy⟩)) hfP.1
  · exact (not_isCladeH_mixed (x := p.1.1) (y := p.1.2) hfhead.1 p.2.1 p.2.2.1 hCs hC2
      (Or.inl ⟨hx, hy⟩)) hfP.2
  · exact (not_isCladeH_mixed (x := p.1.1) (y := p.1.2) hfhead.1 p.2.1 p.2.2.1 hCs hC2
      (Or.inr ⟨hx, hy⟩)) hfP.2

/-- ★★★ **按第一步的四分情形拆和**：只有三种情形有贡献。 -/
theorem sum_headFiber_split_nest {N m : ℕ} (s A C : Finset (Fin N)) (hAC : A ⊆ C)
    (hCs : C ⊆ s) (hA2 : 2 ≤ A.card) (hC2 : 2 ≤ C.card) :
    (∑ p : PairIn N s,
        ((headFiber (m := m) s p).filter
          (fun f => IsCladeH s (m + 1) f A ∧ IsCladeH s (m + 1) f C)).card)
      = (∑ p ∈ (Finset.univ : Finset (PairIn N s)).filter (fun p => p.1.1 ∈ A ∧ p.1.2 ∈ A),
            nestCount N m (s.erase p.1.2) (A.erase p.1.2) (C.erase p.1.2))
        + (∑ p ∈ (Finset.univ : Finset (PairIn N s)).filter
              (fun p => p.1.1 ∉ A ∧ p.1.2 ∉ A ∧ p.1.1 ∈ C ∧ p.1.2 ∈ C),
            nestCount N m (s.erase p.1.2) A (C.erase p.1.2))
        + (∑ p ∈ (Finset.univ : Finset (PairIn N s)).filter (fun p => p.1.1 ∉ C ∧ p.1.2 ∉ C),
            nestCount N m (s.erase p.1.2) A C) := by
  classical
  have hterm : ∀ p : PairIn N s,
      ((headFiber (m := m) s p).filter
          (fun f => IsCladeH s (m + 1) f A ∧ IsCladeH s (m + 1) f C)).card
        = ((if p.1.1 ∈ A ∧ p.1.2 ∈ A then
              nestCount N m (s.erase p.1.2) (A.erase p.1.2) (C.erase p.1.2) else 0)
            + (if p.1.1 ∉ A ∧ p.1.2 ∉ A ∧ p.1.1 ∈ C ∧ p.1.2 ∈ C then
                nestCount N m (s.erase p.1.2) A (C.erase p.1.2) else 0))
          + (if p.1.1 ∉ C ∧ p.1.2 ∉ C then nestCount N m (s.erase p.1.2) A C else 0) := by
    intro p
    by_cases h1 : p.1.1 ∈ A ∧ p.1.2 ∈ A
    · have h2 : ¬ (p.1.1 ∉ A ∧ p.1.2 ∉ A ∧ p.1.1 ∈ C ∧ p.1.2 ∈ C) := by tauto
      have h3 : ¬ (p.1.1 ∉ C ∧ p.1.2 ∉ C) := by tauto
      rw [ite_eq_left h1, ite_eq_right h2, ite_eq_right h3]
      simpa using card_headFiber_nest_both (m := m) s A C hAC hCs hA2 hC2 p h1.1 h1.2
    · by_cases h2 : p.1.1 ∉ A ∧ p.1.2 ∉ A ∧ p.1.1 ∈ C ∧ p.1.2 ∈ C
      · have h3 : ¬ (p.1.1 ∉ C ∧ p.1.2 ∉ C) := by tauto
        rw [ite_eq_right h1, ite_eq_left h2, ite_eq_right h3]
        simpa using card_headFiber_nest_mid (m := m) s A C hAC hCs hA2 hC2 p h2.1 h2.2.1 h2.2.2.1 h2.2.2.2
      · by_cases h3 : p.1.1 ∉ C ∧ p.1.2 ∉ C
        · rw [ite_eq_right h1, ite_eq_right h2, ite_eq_left h3]
          simpa using card_headFiber_nest_out (m := m) s A C hAC hCs hA2 hC2 p h3.1 h3.2
        · rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h3]
          simpa using card_headFiber_nest_zero (m := m) s A C hAC hCs hA2 hC2 p (by tauto)
  calc (∑ p : PairIn N s,
        ((headFiber (m := m) s p).filter
          (fun f => IsCladeH s (m + 1) f A ∧ IsCladeH s (m + 1) f C)).card)
      = ∑ p : PairIn N s,
          (((if p.1.1 ∈ A ∧ p.1.2 ∈ A then
              nestCount N m (s.erase p.1.2) (A.erase p.1.2) (C.erase p.1.2) else 0)
            + (if p.1.1 ∉ A ∧ p.1.2 ∉ A ∧ p.1.1 ∈ C ∧ p.1.2 ∈ C then
                nestCount N m (s.erase p.1.2) A (C.erase p.1.2) else 0))
          + (if p.1.1 ∉ C ∧ p.1.2 ∉ C then nestCount N m (s.erase p.1.2) A C else 0)) :=
        Finset.sum_congr rfl (fun p _ => hterm p)
    _ = (∑ p ∈ (Finset.univ : Finset (PairIn N s)).filter (fun p => p.1.1 ∈ A ∧ p.1.2 ∈ A),
            nestCount N m (s.erase p.1.2) (A.erase p.1.2) (C.erase p.1.2))
        + (∑ p ∈ (Finset.univ : Finset (PairIn N s)).filter
              (fun p => p.1.1 ∉ A ∧ p.1.2 ∉ A ∧ p.1.1 ∈ C ∧ p.1.2 ∈ C),
            nestCount N m (s.erase p.1.2) A (C.erase p.1.2))
        + (∑ p ∈ (Finset.univ : Finset (PairIn N s)).filter (fun p => p.1.1 ∉ C ∧ p.1.2 ∉ C),
            nestCount N m (s.erase p.1.2) A C) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_filter,
          ← Finset.sum_filter, ← Finset.sum_filter]

/-! ## §10.3 递推（ℕ 值）与闭式 -/

/-- `nestCount` 的**递推**（按第一步的四分情形）。 -/
theorem nestCount_succ_rec {N m : ℕ} (s A C : Finset (Fin N)) (hAC : A ⊆ C)
    (hCs : C ⊆ s) (hA2 : 2 ≤ A.card) (hC2 : 2 ≤ C.card) :
    nestCount N (m + 1) s A C
      = (∑ p ∈ (Finset.univ : Finset (PairIn N s)).filter (fun p => p.1.1 ∈ A ∧ p.1.2 ∈ A),
            nestCount N m (s.erase p.1.2) (A.erase p.1.2) (C.erase p.1.2))
        + (∑ p ∈ (Finset.univ : Finset (PairIn N s)).filter
              (fun p => p.1.1 ∉ A ∧ p.1.2 ∉ A ∧ p.1.1 ∈ C ∧ p.1.2 ∈ C),
            nestCount N m (s.erase p.1.2) A (C.erase p.1.2))
        + (∑ p ∈ (Finset.univ : Finset (PairIn N s)).filter (fun p => p.1.1 ∉ C ∧ p.1.2 ∉ C),
            nestCount N m (s.erase p.1.2) A C) := by
  rw [nestCount_succ_eq_sum, sum_headFiber_split_nest s A C hAC hCs hA2 hC2]

/-- 算术核（嵌套情形）：递推在闭式 `H · Rn` 上的展开。 -/
def ArithStepRn : Prop :=
  ∀ m a c : ℕ, 2 ≤ a → a < c → c ≤ m + 1 →
    ((a.choose 2 : ℕ) : ℝ) * (RankedGeneTree.H (m + 1) * Rn (m + 1) (a - 1) (c - 1))
      + (((c - a).choose 2 : ℕ) : ℝ) * (RankedGeneTree.H (m + 1) * Rn (m + 1) a (c - 1))
      + (((m + 2 - c).choose 2 : ℕ) : ℝ) * (RankedGeneTree.H (m + 1) * Rn (m + 1) a c)
      = RankedGeneTree.H (m + 2) * Rn (m + 2) a c

/-- ★ `Rn n 1 c = pn n c`（`a = 1` 端点，`1 ≤ c < n`）。 -/
theorem Rn_one_left {n c : ℕ} (h1 : 1 ≤ c) (h2 : c < n) : Rn n 1 c = pn n c := by
  rw [pn_of_range (n := n) (a := c) h1 h2]
  unfold Rn
  have hc : ((c.choose 1 : ℕ) : ℝ) = (c : ℝ) := by rw [Nat.choose_one_right]
  rw [hc]
  field_simp
  ring

/-- 情形二/三的配对数（`C \ A` 的两两配对）。 -/
theorem card_pairs_sdiff {N : ℕ} (s A C : Finset (Fin N)) (hAC : A ⊆ C) (hCs : C ⊆ s) :
    ((Finset.univ : Finset (PairIn N s)).filter
        (fun p => p.1.1 ∉ A ∧ p.1.2 ∉ A ∧ p.1.1 ∈ C ∧ p.1.2 ∈ C)).card
      = (C.card - A.card).choose 2 := by
  classical
  have hset : ((Finset.univ : Finset (PairIn N s)).filter
      (fun p => p.1.1 ∉ A ∧ p.1.2 ∉ A ∧ p.1.1 ∈ C ∧ p.1.2 ∈ C))
      = ((Finset.univ : Finset (PairIn N s)).filter
          (fun p => p.1.1 ∈ C \ A ∧ p.1.2 ∈ C \ A)) := by
    refine Finset.filter_congr (fun p _ => ?_)
    rw [Finset.mem_sdiff, Finset.mem_sdiff]
    tauto
  rw [hset, card_pairs_both s (C \ A) (fun z hz => hCs (Finset.mem_sdiff.mp hz).1),
    Finset.card_sdiff, Finset.inter_eq_left.mpr hAC]

/-- ★★★ **嵌套两 clade 的联合计数**（条件形态）：递推 ＋ 算术核 ⇒
`#{A、C 同时是 clade} = H (m+1) · Rn (m+1) |A| |C|`（`A ⊊ C ⊆ s`、`|s| = m+1`）。 -/
theorem nestCount_eq_H_mul_Rn_of_arith (harith : ArithStepRn) (m : ℕ) :
    ∀ (N : ℕ) (s A C : Finset (Fin N)), s.card = m + 1 → A ⊆ C → C ⊆ s →
      1 ≤ A.card → A.card < C.card → C.card ≤ m →
      (nestCount N m s A C : ℝ) = RankedGeneTree.H (m + 1) * Rn (m + 1) A.card C.card := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro N s A C hs hAC hCs hA1 hAc hCm
    rcases Nat.lt_or_ge m 2 with hlt | hge
    · exfalso
      omega
    · obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      have hsk : s.card = k + 1 + 1 := hs
      have hsk2 : s.card = k + 2 := by omega
      have hAs : A ⊆ s := fun z hz => hCs (hAC hz)
      rcases eq_or_lt_of_le hA1 with ha1 | ha2
      · -- `|A| = 1`：单点集恒是 clade，退化成单 clade 计数
        obtain ⟨w, rfl⟩ := Finset.card_eq_one.mp ha1.symm
        have hws : w ∈ s := hAs (Finset.mem_singleton_self w)
        have hfilter : ((mhFinset N (k + 1) s).filter
              (fun f => IsCladeH s (k + 1) f ({w} : Finset (Fin N)) ∧ IsCladeH s (k + 1) f C))
            = (mhFinset N (k + 1) s).filter (fun f => IsCladeH s (k + 1) f C) := by
          refine Finset.filter_congr (fun f _ => ?_)
          exact ⟨fun h => h.2, fun h => ⟨isCladeH_singleton s (k + 1) f hws, h⟩⟩
        have hC1 : 1 ≤ C.card := by omega
        have hCn : C.card ≤ k + 1 := by omega
        have hcl := cladeCountS_eq_H_mul_pn (k + 1) N s C hsk hCs hC1 hCn
        unfold nestCount
        rw [hfilter]
        rw [show ((mhFinset N (k + 1) s).filter (fun f => IsCladeH s (k + 1) f C)).card
            = cladeCountS (k + 1) s C from rfl]
        rw [hcl, Finset.card_singleton, Rn_one_left hC1 (by omega)]
      · -- `2 ≤ |A|`：递推
        have hA2 : 2 ≤ A.card := ha2
        have hC2 : 2 ≤ C.card := by omega
        rw [nestCount_succ_rec s A C hAC hCs hA2 hC2]
        push_cast
        have hS1 : (∑ p ∈ (Finset.univ : Finset (PairIn N s)).filter
              (fun p => p.1.1 ∈ A ∧ p.1.2 ∈ A),
              (nestCount N k (s.erase p.1.2) (A.erase p.1.2) (C.erase p.1.2) : ℝ))
            = ((A.card.choose 2 : ℕ) : ℝ)
              * (RankedGeneTree.H (k + 1) * Rn (k + 1) (A.card - 1) (C.card - 1)) := by
          have hc : ∀ p ∈ (Finset.univ : Finset (PairIn N s)).filter
              (fun p => p.1.1 ∈ A ∧ p.1.2 ∈ A),
              (nestCount N k (s.erase p.1.2) (A.erase p.1.2) (C.erase p.1.2) : ℝ)
                = RankedGeneTree.H (k + 1) * Rn (k + 1) (A.card - 1) (C.card - 1) := by
            intro p hp
            rw [Finset.mem_filter] at hp
            obtain ⟨-, hpx, hpy⟩ := hp
            rw [ih k (by omega) N (s.erase p.1.2) (A.erase p.1.2) (C.erase p.1.2) ?_ ?_ ?_ ?_ ?_ ?_,
              Finset.card_erase_of_mem hpy, Finset.card_erase_of_mem (hAC hpy)]
            · rw [Finset.card_erase_of_mem p.2.2.1]; omega
            · intro z hz
              rw [Finset.mem_erase] at hz ⊢
              exact ⟨hz.1, hAC hz.2⟩
            · intro z hz
              rw [Finset.mem_erase] at hz ⊢
              exact ⟨hz.1, hCs hz.2⟩
            · rw [Finset.card_erase_of_mem hpy]; omega
            · rw [Finset.card_erase_of_mem hpy, Finset.card_erase_of_mem (hAC hpy)]; omega
            · rw [Finset.card_erase_of_mem (hAC hpy)]; omega
          rw [Finset.sum_congr rfl hc, Finset.sum_const, nsmul_eq_mul,
            card_pairs_both s A hAs]
        have hS2 : (∑ p ∈ (Finset.univ : Finset (PairIn N s)).filter
              (fun p => p.1.1 ∉ A ∧ p.1.2 ∉ A ∧ p.1.1 ∈ C ∧ p.1.2 ∈ C),
              (nestCount N k (s.erase p.1.2) A (C.erase p.1.2) : ℝ))
            = (((C.card - A.card).choose 2 : ℕ) : ℝ)
              * (RankedGeneTree.H (k + 1) * Rn (k + 1) A.card (C.card - 1)) := by
          by_cases hca : A.card = C.card - 1
          · have hempty : ((Finset.univ : Finset (PairIn N s)).filter
                (fun p => p.1.1 ∉ A ∧ p.1.2 ∉ A ∧ p.1.1 ∈ C ∧ p.1.2 ∈ C)) = ∅ := by
              have h1 : C.card - (C.card - 1) = 1 := by omega
              rw [← Finset.card_eq_zero, card_pairs_sdiff s A C hAC hCs, hca, h1,
                show (1 : ℕ).choose 2 = 0 from Nat.choose_eq_zero_of_lt (by omega)]
            rw [hempty, Finset.sum_empty]
            have h1 : C.card - (C.card - 1) = 1 := by omega
            rw [hca, h1, show (1 : ℕ).choose 2 = 0 from Nat.choose_eq_zero_of_lt (by omega)]
            ring
          · have hc : ∀ p ∈ (Finset.univ : Finset (PairIn N s)).filter
                (fun p => p.1.1 ∉ A ∧ p.1.2 ∉ A ∧ p.1.1 ∈ C ∧ p.1.2 ∈ C),
                (nestCount N k (s.erase p.1.2) A (C.erase p.1.2) : ℝ)
                  = RankedGeneTree.H (k + 1) * Rn (k + 1) A.card (C.card - 1) := by
              intro p hp
              rw [Finset.mem_filter] at hp
              obtain ⟨-, hpx, hpy, hpxc, hpyc⟩ := hp
              rw [ih k (by omega) N (s.erase p.1.2) A (C.erase p.1.2) ?_ ?_ ?_ ?_ ?_ ?_,
                Finset.card_erase_of_mem hpyc]
              · rw [Finset.card_erase_of_mem p.2.2.1]; omega
              · intro z hz
                rw [Finset.mem_erase]
                exact ⟨fun h => hpy (h ▸ hz), hAC hz⟩
              · intro z hz
                rw [Finset.mem_erase] at hz ⊢
                exact ⟨hz.1, hCs hz.2⟩
              · omega
              · rw [Finset.card_erase_of_mem hpyc]; omega
              · rw [Finset.card_erase_of_mem hpyc]; omega
            rw [Finset.sum_congr rfl hc, Finset.sum_const, nsmul_eq_mul,
              card_pairs_sdiff s A C hAC hCs]
        have hS3 : (∑ p ∈ (Finset.univ : Finset (PairIn N s)).filter
              (fun p => p.1.1 ∉ C ∧ p.1.2 ∉ C),
              (nestCount N k (s.erase p.1.2) A C : ℝ))
            = ((((k + 2) - C.card).choose 2 : ℕ) : ℝ)
              * (RankedGeneTree.H (k + 1) * Rn (k + 1) A.card C.card) := by
          by_cases hck : C.card ≤ k
          · have hc : ∀ p ∈ (Finset.univ : Finset (PairIn N s)).filter
                (fun p => p.1.1 ∉ C ∧ p.1.2 ∉ C),
                (nestCount N k (s.erase p.1.2) A C : ℝ)
                  = RankedGeneTree.H (k + 1) * Rn (k + 1) A.card C.card := by
              intro p hp
              rw [Finset.mem_filter] at hp
              obtain ⟨-, hpx, hpy⟩ := hp
              rw [ih k (by omega) N (s.erase p.1.2) A C ?_ ?_ ?_ ?_ ?_ ?_]
              · rw [Finset.card_erase_of_mem p.2.2.1]; omega
              · exact hAC
              · intro z hz
                rw [Finset.mem_erase]
                exact ⟨fun h => hpy (h ▸ hz), hCs hz⟩
              · omega
              · omega
              · omega
            rw [Finset.sum_congr rfl hc, Finset.sum_const, nsmul_eq_mul,
              card_pairs_none, Finset.card_sdiff, Finset.inter_eq_left.mpr hCs, hsk]
          · have hcc : C.card = k + 1 := by omega
            have hempty : ((Finset.univ : Finset (PairIn N s)).filter
                (fun p => p.1.1 ∉ C ∧ p.1.2 ∉ C)) = ∅ := by
              have h1 : (k + 2) - (k + 1) = 1 := by omega
              rw [← Finset.card_eq_zero, card_pairs_none, Finset.card_sdiff,
                Finset.inter_eq_left.mpr hCs, hsk2, hcc, h1,
                show (1 : ℕ).choose 2 = 0 from Nat.choose_eq_zero_of_lt (by omega)]
            rw [hempty, Finset.sum_empty]
            have h1 : (k + 2) - (k + 1) = 1 := by omega
            rw [hcc, h1, show (1 : ℕ).choose 2 = 0 from Nat.choose_eq_zero_of_lt (by omega)]
            ring
        rw [hS1, hS2, hS3]
        exact harith k A.card C.card hA2 hAc hCm

/-! ## §10.4 算术核 `ArithStepRn`：用 `ArithStep`（单 clade 的核）两次兑换 -/

/-- ★ **嵌套情形的乘积形态**：`Rn n x y = pn n y · pn y x`（`1 ≤ x < y < n`）。

这正是「`B` 成 clade（概率 `pn n y`）× 给定 `B` 后 `A` 在 `B` 的子树里成 clade
（概率 `pn y x`）」的**乘法公式**，也是 `Rn` 与 `pn` 的唯一桥梁。 -/
theorem Rn_eq_mul_pn {n x y : ℕ} (hx : 1 ≤ x) (hxy : x < y) (hyn : y < n) :
    Rn n x y = pn n y * pn y x := by
  rw [pn_of_range (n := n) (a := y) (by omega) hyn,
    pn_of_range (n := y) (a := x) hx hxy]
  unfold Rn
  have hx0 : ((x : ℝ)) ≠ 0 := by
    have h : x ≠ 0 := by omega
    exact_mod_cast h
  have hy0 : ((y : ℝ)) ≠ 0 := by
    have h : y ≠ 0 := by omega
    exact_mod_cast h
  have hnp : (((n.choose y : ℕ)) : ℝ) ≠ 0 := by
    have h : 0 < n.choose y := Nat.choose_pos (le_of_lt hyn)
    exact_mod_cast ne_of_gt h
  have hxp : (((y.choose x : ℕ)) : ℝ) ≠ 0 := by
    have h : 0 < y.choose x := Nat.choose_pos (le_of_lt hxy)
    exact_mod_cast ne_of_gt h
  field_simp
  ring

/-- ★ `H c = H (c−1) · C(c,2)`（`2 ≤ c`）—— 把 `H` 的比值写成 `C(c,2)`（ℕ 值），
供 `ArithStep` 的对齐使用。 -/
theorem H_eq_H_pred_mul_choose (c : ℕ) (hc : 2 ≤ c) :
    RankedGeneTree.H c = RankedGeneTree.H (c - 1) * ((c.choose 2 : ℕ) : ℝ) := by
  have h := RankedGeneTree.H_succ_eq (c - 1) (by omega)
  rw [show c - 1 + 1 = c from by omega] at h
  rw [h, cast_choose_two_eq]
  have hkr : Coalescent.kingmanRate c = (c : ℝ) * ((c : ℝ) - 1) / 2 := rfl
  rw [hkr]

/-- ★★★ **算术核成立**（`ArithStepRn`）。

证明只用**两次**已收口的 ★★★ `ArithStep`（单 clade 的算术核）：
1. `ArithStep (c−2) a`：`C(a,2)p_{c−1}(a−1) + C(c−a,2)p_{c−1}(a) = C(c,2)p_c(a)`（除掉 `H(c−1)`）；
2. `ArithStep m c`：`C(c,2)H(m+1)p_{m+1}(c−1) + C(m+2−c,2)H(m+1)p_{m+1}(c) = H(m+2)p_{m+2}(c)`；
再把 `Rn = pn·pn` 代进去、整体乘 `H(c−1)` 消去分母即可。 -/
theorem arithStepRn_holds : ArithStepRn := by
  intro m a c ha2 hac hcm
  have hc2 : 2 ≤ c := by omega
  -- 三个 `Rn` 拆成 `pn · pn`
  have hR1 : Rn (m + 1) (a - 1) (c - 1) = pn (m + 1) (c - 1) * pn (c - 1) (a - 1) :=
    Rn_eq_mul_pn (by omega) (by omega) (by omega)
  have hR3 : (((m + 2 - c).choose 2 : ℕ) : ℝ)
        * (RankedGeneTree.H (m + 1) * Rn (m + 1) a c)
      = (((m + 2 - c).choose 2 : ℕ) : ℝ)
        * (RankedGeneTree.H (m + 1) * (pn (m + 1) c * pn c a)) := by
    by_cases h : c < m + 1
    · rw [Rn_eq_mul_pn (n := m + 1) (x := a) (y := c) (by omega) hac h]
    · have h1 : m + 2 - c = 1 := by omega
      rw [h1, show (1 : ℕ).choose 2 = 0 from Nat.choose_eq_zero_of_lt (by omega)]
      ring
  have hR3' : Rn (m + 2) a c = pn (m + 2) c * pn c a :=
    Rn_eq_mul_pn (by omega) hac (by omega)
  -- 中间项：`a = c−1` 时系数为 `0`，故无须拆 `Rn`
  have hR2 : (((c - a).choose 2 : ℕ) : ℝ)
        * (RankedGeneTree.H (m + 1) * Rn (m + 1) a (c - 1))
      = (((c - a).choose 2 : ℕ) : ℝ)
        * (RankedGeneTree.H (m + 1) * (pn (m + 1) (c - 1) * pn (c - 1) a)) := by
    by_cases h : a < c - 1
    · rw [Rn_eq_mul_pn (n := m + 1) (x := a) (y := c - 1) (by omega) h (by omega)]
    · have h1 : c - a = 1 := by omega
      rw [h1, show (1 : ℕ).choose 2 = 0 from Nat.choose_eq_zero_of_lt (by omega)]
      ring
  -- ① 除掉 `H(c−1)` 的单 clade 核
  have hA1 := arithStep_holds (c - 2) a ha2 (by omega)
  rw [show c - 2 + 1 = c - 1 from by omega, show c - 2 + 2 = c from by omega] at hA1
  have hHc : RankedGeneTree.H c = RankedGeneTree.H (c - 1) * ((c.choose 2 : ℕ) : ℝ) :=
    H_eq_H_pred_mul_choose c hc2
  have hAs1 : (((a.choose 2 : ℕ) : ℝ) * (RankedGeneTree.H (c - 1) * pn (c - 1) (a - 1))
        + (((c - a).choose 2 : ℕ) : ℝ) * (RankedGeneTree.H (c - 1) * pn (c - 1) a))
      = RankedGeneTree.H (c - 1) * (((c.choose 2 : ℕ) : ℝ) * pn c a) := by
    rw [hHc] at hA1
    exact hA1.trans (by ring)
  -- ② 单 clade 核本身
  have hAs2 : (((c.choose 2 : ℕ) : ℝ) * (RankedGeneTree.H (m + 1) * pn (m + 1) (c - 1))
        + (((m + 2 - c).choose 2 : ℕ) : ℝ) * (RankedGeneTree.H (m + 1) * pn (m + 1) c))
      = RankedGeneTree.H (m + 2) * pn (m + 2) c :=
    arithStep_holds m c hc2 hcm
  -- 装配：整体乘 `H(c−1)` 后是三次 `ring` ＋ 两次 `rw`
  rw [hR1, hR2, hR3, hR3']
  refine mul_left_cancel₀ (ne_of_gt (H_pos (c - 1))) ?_
  calc RankedGeneTree.H (c - 1)
        * ((((a.choose 2 : ℕ) : ℝ)
              * (RankedGeneTree.H (m + 1) * (pn (m + 1) (c - 1) * pn (c - 1) (a - 1)))
            + (((c - a).choose 2 : ℕ) : ℝ)
              * (RankedGeneTree.H (m + 1) * (pn (m + 1) (c - 1) * pn (c - 1) a)))
          + (((m + 2 - c).choose 2 : ℕ) : ℝ)
              * (RankedGeneTree.H (m + 1) * (pn (m + 1) c * pn c a)))
      = ((((a.choose 2 : ℕ) : ℝ) * (RankedGeneTree.H (c - 1) * pn (c - 1) (a - 1))
            + (((c - a).choose 2 : ℕ) : ℝ) * (RankedGeneTree.H (c - 1) * pn (c - 1) a)))
          * (RankedGeneTree.H (m + 1) * pn (m + 1) (c - 1))
        + (((m + 2 - c).choose 2 : ℕ) : ℝ)
            * (RankedGeneTree.H (m + 1) * pn (m + 1) c) * (RankedGeneTree.H (c - 1) * pn c a) := by
        ring
    _ = (RankedGeneTree.H (c - 1) * (((c.choose 2 : ℕ) : ℝ) * pn c a))
          * (RankedGeneTree.H (m + 1) * pn (m + 1) (c - 1))
        + (((m + 2 - c).choose 2 : ℕ) : ℝ)
            * (RankedGeneTree.H (m + 1) * pn (m + 1) c) * (RankedGeneTree.H (c - 1) * pn c a) := by
        rw [hAs1]
    _ = RankedGeneTree.H (c - 1)
          * (pn c a * ((((c.choose 2 : ℕ) : ℝ) * (RankedGeneTree.H (m + 1) * pn (m + 1) (c - 1))
            + (((m + 2 - c).choose 2 : ℕ) : ℝ)
                * (RankedGeneTree.H (m + 1) * pn (m + 1) c)))) := by
        ring
    _ = RankedGeneTree.H (c - 1) * (pn c a * (RankedGeneTree.H (m + 2) * pn (m + 2) c)) := by
        rw [hAs2]
    _ = RankedGeneTree.H (c - 1)
          * (RankedGeneTree.H (m + 2) * (pn (m + 2) c * pn c a)) := by
        ring

/-- ★★★ **嵌套两 clade 的联合计数（无条件版）**。 -/
theorem nestCount_eq_H_mul_Rn (m : ℕ) :
    ∀ (N : ℕ) (s A C : Finset (Fin N)), s.card = m + 1 → A ⊆ C → C ⊆ s →
      1 ≤ A.card → A.card < C.card → C.card ≤ m →
      (nestCount N m s A C : ℝ) = RankedGeneTree.H (m + 1) * Rn (m + 1) A.card C.card :=
  nestCount_eq_H_mul_Rn_of_arith arithStepRn_holds m

/-! ## §10.5 ② 的落地：`clanPairComplCount` 在 `rootedCarrier` 上成立 -/

/-- ★★★ **② 落地**：`#{ω : A 与 Bᶜ 同为 clade} = Rn m |A| (m−|B|) · |RankedTree m|`
（`Disjoint A B`、两侧非空、`|A| + |B| < m`）。

三步：载体对齐（★★ `rootedCarrier_isClade_iff`）· 货币兑换
（★★ `card_rankedTree_filter_eq_mhFinset` ＋ ★★ `mem_cladesOf_iff_isCladeH`）·
嵌套计数（★★★ `nestCount_eq_H_mul_Rn`）。 -/
theorem clanPairComplCount_rootedCarrier {m : ℕ} (h3 : 3 ≤ m) :
    clanPairComplCount m (RankedGeneTree.RankedTree m) (fun ω => rootedCarrier m h3 ω) := by
  intro A B hd hA hB hlt
  have hm : 2 ≤ m := by omega
  have hapos : 1 ≤ A.card := Finset.card_pos.mpr hA
  have hbpos : 1 ≤ B.card := Finset.card_pos.mpr hB
  have halt : A.card < m := by omega
  have hbcn : (Bᶜ).card = m - B.card := card_compl_eq m B
  have hbcpos : (Bᶜ).Nonempty := by
    refine Finset.card_pos.mp ?_
    rw [hbcn]
    omega
  have hbclt : (Bᶜ).card < m := by rw [hbcn]; omega
  have hsub : A ⊆ Bᶜ := by
    intro z hz
    rw [Finset.mem_compl]
    exact fun h => Finset.disjoint_left.mp hd hz h
  -- ① 载体对齐：把 `IsClade (·.image inl)` 换成 `cladesOf`
  have hfilter : ((Finset.univ : Finset (RankedGeneTree.RankedTree m)).filter
        (fun ω => (rootedCarrier m h3 ω).IsClade (A.image (Sum.inl : Fin m → Fin m ⊕ Unit))
          ∧ (rootedCarrier m h3 ω).IsClade ((Bᶜ).image (Sum.inl : Fin m → Fin m ⊕ Unit))))
      = (Finset.univ : Finset (RankedGeneTree.RankedTree m)).filter
          (fun ω => A ∈ RankedGeneTree.cladesOf m ω.1
            ∧ (Bᶜ) ∈ RankedGeneTree.cladesOf m ω.1) := by
    refine Finset.filter_congr (fun ω _ => ?_)
    rw [rootedCarrier_isClade_iff h3 ω hA halt,
      rootedCarrier_isClade_iff h3 ω hbcpos hbclt]
  rw [hfilter]
  -- ② 货币兑换：`RankedTree` 滤子 → `mhFinset` 滤子 → `IsCladeH`
  have hmh := card_rankedTree_filter_eq_mhFinset (m := m)
    (P := fun f => A ∈ RankedGeneTree.cladesOf m f ∧ (Bᶜ) ∈ RankedGeneTree.cladesOf m f)
  rw [show ((Finset.univ : Finset (RankedGeneTree.RankedTree m)).filter
        (fun ω => A ∈ RankedGeneTree.cladesOf m ω.1
          ∧ (Bᶜ) ∈ RankedGeneTree.cladesOf m ω.1)).card
      = ((mhFinset m (m - 1) (Finset.univ : Finset (Fin m))).filter
          (fun f => A ∈ RankedGeneTree.cladesOf m f
            ∧ (Bᶜ) ∈ RankedGeneTree.cladesOf m f)).card from hmh]
  have hEq : ((mhFinset m (m - 1) (Finset.univ : Finset (Fin m))).filter
        (fun f => A ∈ RankedGeneTree.cladesOf m f ∧ (Bᶜ) ∈ RankedGeneTree.cladesOf m f))
      = (mhFinset m (m - 1) (Finset.univ : Finset (Fin m))).filter
          (fun f => IsCladeH (Finset.univ : Finset (Fin m)) (m - 1) f A
            ∧ IsCladeH (Finset.univ : Finset (Fin m)) (m - 1) f (Bᶜ)) := by
    refine Finset.filter_congr (fun f _ => ?_)
    rw [mem_cladesOf_iff_isCladeH (by omega) f A,
      mem_cladesOf_iff_isCladeH (by omega) f (Bᶜ)]
  rw [hEq]
  rw [show ((mhFinset m (m - 1) (Finset.univ : Finset (Fin m))).filter
        (fun f => IsCladeH (Finset.univ : Finset (Fin m)) (m - 1) f A
          ∧ IsCladeH (Finset.univ : Finset (Fin m)) (m - 1) f (Bᶜ))).card
      = nestCount m (m - 1) (Finset.univ : Finset (Fin m)) A (Bᶜ) from rfl]
  -- ③ 嵌套计数
  have hnest := nestCount_eq_H_mul_Rn (m - 1) m (Finset.univ : Finset (Fin m)) A (Bᶜ)
    (by rw [Finset.card_univ, Fintype.card_fin]; omega) hsub (Finset.subset_univ _)
    hapos (by rw [hbcn]; omega) (by rw [hbcn]; omega)
  rw [hnest, show m - 1 + 1 = m from by omega, hbcn,
    card_rankedTree_eq_H m hm]
  ring

end Phylo.Stat.ClanPairLaw
