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
`= rn n a b · |Ω|`（`A ∩ B = ∅`、`A ∪ B ⊊ X`）。 -/
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
`= Rn n b (n−a)`。 -/
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
and `B` are clades" —— 它是 ②③ 的**减项**。 -/
def tripleClanCount (N : ℕ) (Ω : Type*) [Fintype Ω]
    (U : Ω → Cladogram.{0, 0} (Fin N ⊕ Unit)) : Prop :=
  ∀ A B : Finset (Fin N), Disjoint A B → A.Nonempty → B.Nonempty → A.card + B.card < N →
    (((Finset.univ : Finset Ω).filter
        (fun ω => (U ω).IsClade (A.image Sum.inl) ∧ (U ω).IsClade (Bᶜ.image Sum.inl)
          ∧ (U ω).IsClade (B.image Sum.inl))).card : ℝ)
      = (pnHatExh N B.card * pn (N - B.card) A.card) * (Fintype.card Ω : ℝ)

/-- **穷尽支的计数化**（`a + b = n`，Theorem 6.3(i) ＝ Lemma 6.2 的概率层；
**不**在本文件证明，只为装配 `H` 的第四组）。 -/
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

end Phylo.Stat.ClanPairLaw
