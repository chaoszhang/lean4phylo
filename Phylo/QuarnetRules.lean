/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.Quartet
import Phylo.Binary

/-!
# `Phylo.QuarnetLevel1` —— level-1 网络的 quarnet 推理规则（W11g · N3）

## 0. 文献（在手，行号即 `references/md/Huber2018_QuarnetRules_Level1Networks.md` 的行号）

Huber, K. T., Moulton, V., Semple, C. & Wu, T. (2018).
*Quarnet Inference Rules for Level-1 Networks.* Bull. Math. Biol. **80**(8):2137–2153.

* **unrooted network**（`:227–231`）：连通图，顶点度 1 或 ≥ 3，度 1 顶点集 = `X`；
  **binary** = 度 1 或 3；**interior** = 非叶。
* **level-1**（`:244–246`）：每个**无 cut-edge 的极大子图**是「一个顶点」或「一个圈」；
  **cycle type**（`:246–248`）= 唯一圈长度 `|X|` 且顶点数 `2|X|`。
* **quarnet / qnet**（`:446–448`）：4 叶的 binary level-1 network；**support** `L(F)`（`:499`）；
  **四型**（`:496–502`）：Type I 无圈（= quartet tree）、Type II 一圈 + 一非平凡 cut-edge、
  Type III 两圈、Type IV cycle type；记号 `a ⊖ b|c ⊖ d` / `a ⊕ b|c ⊖ d` / `a ⊕ b|c ⊕ d` /
  `a ⊕ b ⊕ c ⊕ d`（`:497`）。
* **展示 / 展出**（`:505–507`, `:571`）：`F(N) = {N|A : |A| = 4}`；
  `Q(N)` = **displayed** quartets，`Σ(N)` = **exhibited** quartets（`:426`），且 `Σ(N) ⊆ Q(N)`，
  **反向不成立**（Fig. 4(iv) 的反例，`:429–432`）。
* **规则**（`:509–560`）：`consistent`（三元素限制一致）、`minimally dense`、
  **`cyclative`**（`{a⊕b⊕c⊕d, x⊕a⊕c⊕d} ⊆ F ⟹ a⊕b⊕d⊕x ∈ F`，`:532–542`）、
  **`saturated`**（S1/S2/S3，`:551–568`）。
* **Theorem 2**（`:605`）：minimally dense 的 qnet 系统 `F` 恰是某（唯一）binary level-1 network
  的 qnet 系统 ⟺ `F` **consistent + cyclative + saturated**。
* **Theorem 3**（`:864–880`）：四元组的 (D1)–(D3) 刻画。

## 1. ★A 扫描结论（本文件开工前的实测）

　　`grep -rn -i 'quarnet|level1|level-1|pauplin|nniDistance|nniGraph' Phylo/`

* `quarnet` —— **0 命中**（本文件是库内**唯一**出处）；
* `level1` / `level-1` —— **0 命中**（无 `Network` / `Level1` / 圈载体）；
* `pauplin` —— 15 命中，**全部**在 `Phylo/BMELeastSquares.lean`（W11g · D3 的域，本文件不碰）。

⇒ **level-1 网络这一载体在库内不可陈述**：`Phylo/Core.lean` 的 `Cladogram.graph` 带字段
`isTree : graph.IsTree`，`Phylogram` 继承它 —— 载体被**锁死为树**。
故本文件：

1. 把**真正缺的载体**写成显式缺口 `quarnetRules_level1_gap`（**不**硬编一个「看起来像」的
   level-1 定义 —— 那会把 Theorem 2 偷渡成定义）；
2. 把**能在树上做的**部分（= Type I 那一层的规则）证成定理：
   split 层 `Exhibits`（文献 `:426` 的字面转写）、
   ★★★ split 层 **Colonius–Schulze 规则**（Theorem 1 与规则 (S1) 的组合核心）、
   ★★ **thin**（Lemma 2(i) 的树层核，`:574–588`）、
   ★★ **(S1) 饱和性**、以及 ★B **反例检查**（(S1) 的析取**不可**收缩为单支）。

## 2. ⚠️ 诚实的边界

本文件**没有**、也**不可能**在本库内证 Theorem 2 / Theorem 3 的 level-1 部分：它们要的
「网络载体 + 删边抑制算子 + quarnet 类型学」三件器材都不存在（见缺口定义处的逐条说明）。
本文件证的全是**树侧**（Type I）内容 —— 这恰好是 Theorem 2 证明里「Type I 那一段」
（`:800–812`）以及 Theorem 1 的规则部分。
-/

namespace Split

variable {α : Type*} [Fintype α] [DecidableEq α]

/-! ## 1. `Exhibits`：split 展出的 quartet（文献 `:426` 的字面转写） -/

/-- ★★ **split `s` 展出 quartet `ab|cd`**（Huber et al. 2018 `:426` 的定义，逐字转写）：

> A quartet `ab|cd` is **exhibited** by a network `N` if there exists a split `A|B` induced by `N`
> such that `{a,b} ⊆ A` and `{c,d} ⊆ B`.

文献里的 `A|B` 是**网络的一条 cut-edge** 诱导的 split；在 split 层只需 `s.sideA`/`s.sideB`。
⚠️ 与库内 `Cladogram.DisplaysQuartet`（`Phylo/Quartet.lean:202`，用 `IsSplitOf` 要求
「是树的一条边」）相比，本条**只谈 split 本身** —— 正是「displayed vs exhibited」
（`:429–432`）在 split 层的分界线。 -/
def Exhibits (s : Split α) (a b c d : α) : Prop :=
  ({a, b} : Finset α) ⊆ s.sideA ∧ ({c, d} : Finset α) ⊆ s.sideB

/-- 展出不依赖第一侧内部的次序（`ab|cd ⟺ ba|cd`）。 -/
theorem exhibits_comm_ab (s : Split α) (a b c d : α) :
    s.Exhibits a b c d ↔ s.Exhibits b a c d := by
  have h : ({a, b} : Finset α) = {b, a} := Finset.pair_comm a b
  unfold Exhibits
  rw [h]

/-- 展出不依赖第二侧内部的次序（`ab|cd ⟺ ab|dc`）。 -/
theorem exhibits_comm_cd (s : Split α) (a b c d : α) :
    s.Exhibits a b c d ↔ s.Exhibits a b d c := by
  have h : ({c, d} : Finset α) = {d, c} := Finset.pair_comm c d
  unfold Exhibits
  rw [h]

/-- 展出不依赖两侧互换（`ab|cd ⟺ cd|ab`）。 -/
theorem exhibits_swap (s : Split α) (a b c d : α) :
    s.Exhibits a b c d ↔ s.swap.Exhibits c d a b := by
  unfold Exhibits
  rw [Split.swap_sideA, Split.swap_sideB]
  exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

/-- 展出的两侧都非空（故 `a ≠ c` 等退化情形自动被排除）。 -/
theorem exhibits_nonempty_sides {s : Split α} {a b c d : α} (h : s.Exhibits a b c d) :
    s.sideA.Nonempty ∧ s.sideB.Nonempty :=
  ⟨⟨a, h.1 (by simp)⟩, ⟨c, h.2 (by simp)⟩⟩

/-! ## 2. ★★★ split 层 Colonius–Schulze 规则

文献 Theorem 1（`:412`）的规则 `ab|cx` + `ab|xd ⟹ ab|cd` 在**树**层的库内形态是
`Cladogram.displaysQuartet_of_displaysQuartet_common`（`Phylo/Quartet.lean:257`）。
这里给出**更强**的 split 层形态：只需**两个见证 split 相容**，不需要先有树。

**证明思路**（文献 Theorem 1 的规则证明的纯组合核）：`{a,b} ⊆ s.A ∩ t.A`、`{e} ⊆ s.B ∩ t.B`
⇒ 四交中 `s.A∩t.A`、`s.B∩t.B` **非空** ⇒ 相容性迫使 `s.A ∩ t.B = ∅` 或 `s.B ∩ t.A = ∅`：

* 前者 ⟹ `d ∉ s.A`（否则 `d ∈ s.A∩t.B`）⟹ `d ∈ s.B` ⟹ **`s` 展出 `ab|cd`**；
* 后者 ⟹ `c ∉ t.A` ⟹ `c ∈ t.B` ⟹ **`t` 展出 `ab|cd`**。 -/
theorem exhibits_common {s t : Split α} {a b c d e : α} (hst : Compatible s t)
    (h1 : s.Exhibits a b c e) (h2 : t.Exhibits a b d e) :
    s.Exhibits a b c d ∨ t.Exhibits a b c d := by
  obtain ⟨hab_s, hce_s⟩ := h1
  obtain ⟨hab_t, hde_t⟩ := h2
  have ha_s : a ∈ s.sideA := hab_s (by simp)
  have hb_s : b ∈ s.sideA := hab_s (by simp)
  have hc_s : c ∈ s.sideB := hce_s (by simp)
  have he_s : e ∈ s.sideB := hce_s (by simp)
  have ha_t : a ∈ t.sideA := hab_t (by simp)
  have hd_t : d ∈ t.sideB := hde_t (by simp)
  have he_t : e ∈ t.sideB := hde_t (by simp)
  rcases hst with h | h | h | h
  · exact absurd (Finset.disjoint_left.mp h ha_s ha_t) (by simp)
  · -- `s.A ⊥ t.B`：`d ∉ s.A`
    refine Or.inl ⟨hab_s, fun x hx => ?_⟩
    rw [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with hxc | hxd
    · rw [hxc]; exact hc_s
    · rw [hxd]
      exact s.mem_sideB_of_not_mem_sideA fun hdA =>
        (Finset.disjoint_left.mp h) hdA hd_t
  · -- `s.B ⊥ t.A`：`c ∉ t.A`
    refine Or.inr ⟨hab_t, fun x hx => ?_⟩
    rw [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with hxc | hxd
    · rw [hxc]
      exact t.mem_sideB_of_not_mem_sideA fun hcA =>
        (Finset.disjoint_left.mp h) hc_s hcA
    · rw [hxd]; exact hd_t
  · exact absurd (Finset.disjoint_left.mp h he_s he_t) (by simp)

/-! ## 3. ★★★ thin：两个相容 split 不能在同一个 4-元集上给出不同配对

文献 Lemma 2(i)（`:574–588`）说的是「minimally dense ⟹ thin」；其**组合核**是
「同一棵树的任意两个 split 相容」（`Split.pairwiseCompatible`，`Phylo/Split.lean:894`）
加上下面的四交论证（与 `Phylo/Quartet.lean:298` 的 `not_displaysQuartet_swap` 同源，
但此处**只**用两个 split 的相容性，并覆盖三种配对的**全部**）。 -/

/-- ★★★ **四交核**：若 `x₁,x₂ ∈ s.A`、`y₁,y₂ ∈ s.B`、`x₁,y₁ ∈ t.A`、`x₂,y₂ ∈ t.B`，
则 `s` 与 `t` **不相容**（四个交分别含 `x₁,x₂,y₁,y₂`，全非空）。 -/
theorem incompatible_of_cross_members {s t : Split α} {x₁ x₂ y₁ y₂ : α}
    (h1 : x₁ ∈ s.sideA) (h2 : x₂ ∈ s.sideA) (h3 : y₁ ∈ s.sideB) (h4 : y₂ ∈ s.sideB)
    (h5 : x₁ ∈ t.sideA) (h6 : y₁ ∈ t.sideA) (h7 : x₂ ∈ t.sideB) (h8 : y₂ ∈ t.sideB) :
    Incompatible s t := by
  rw [Incompatible, Compatible]
  rintro (h | h | h | h)
  · exact (Finset.disjoint_left.mp h) h1 h5
  · exact (Finset.disjoint_left.mp h) h2 h7
  · exact (Finset.disjoint_left.mp h) h3 h6
  · exact (Finset.disjoint_left.mp h) h4 h8

/-- ★★★ **同支撑集上不能有两个不同的 2|2 配对**（四个叶互异）：
`s.Exhibits a b c d` 与 `t.Exhibits a c b d` 蕴含 `s ⊥ t`。 -/
theorem incompatible_of_exhibits_ab_cd_ac_bd {s t : Split α} {a b c d : α}
    (h1 : s.Exhibits a b c d) (h2 : t.Exhibits a c b d) : Incompatible s t :=
  incompatible_of_cross_members (s := s) (t := t) (x₁ := a) (x₂ := b) (y₁ := c) (y₂ := d)
    (h1.1 (by simp)) (h1.1 (by simp)) (h1.2 (by simp)) (h1.2 (by simp))
    (h2.1 (by simp)) (h2.1 (by simp)) (h2.2 (by simp)) (h2.2 (by simp))

/-- ★★★ 同上，配对 `ab|cd` vs `ad|bc`。 -/
theorem incompatible_of_exhibits_ab_cd_ad_bc {s t : Split α} {a b c d : α}
    (h1 : s.Exhibits a b c d) (h2 : t.Exhibits a d b c) : Incompatible s t :=
  incompatible_of_cross_members (s := s) (t := t) (x₁ := a) (x₂ := b) (y₁ := d) (y₂ := c)
    (h1.1 (by simp)) (h1.1 (by simp)) (h1.2 (by simp)) (h1.2 (by simp))
    (h2.1 (by simp)) (h2.1 (by simp)) (h2.2 (by simp)) (h2.2 (by simp))

/-- ★★★ 同上，配对 `ac|bd` vs `ad|bc`。 -/
theorem incompatible_of_exhibits_ac_bd_ad_bc {s t : Split α} {a b c d : α}
    (h1 : s.Exhibits a c b d) (h2 : t.Exhibits a d b c) : Incompatible s t :=
  incompatible_of_cross_members (s := s) (t := t) (x₁ := a) (x₂ := c) (y₁ := d) (y₂ := b)
    (h1.1 (by simp)) (h1.1 (by simp)) (h1.2 (by simp)) (h1.2 (by simp))
    (h2.1 (by simp)) (h2.1 (by simp)) (h2.2 (by simp)) (h2.2 (by simp))

/-! ## 4. ★★ (S1) 饱和性（split 层的替换性质）

文献 (S1)（`:551–556`）在**qnet 层**说的是：`F ∋ a ⊖ b|c ⊖ d` 时，五个元素
`{a,b,c,d,x}` 上的四条 qnet 中至少有一条在 `F` 里（`:553`）。
其**树层**（Type I）核就是「替换性质」：
`ab|cd` 展出 + 第五点 `x` ⟹ `ab|cx` 或 `ax|cd` 展出（Bandelt–Dress 1986 Prop 2(b)；
库内树层版本见 `Phylo/InternalEdge.lean:661` 的 `displaysQuartet_substitution`）。

本条的 split 层形态更强（只需一个 split）： -/

/-- ★★ **(S1) 饱和性（split 层替换性质）**：`s` 展出 `ab|cd` ⟹
对任意 `x`，`s` 展出 `ab|cx` 或 `s` 展出 `ax|cd`。 -/
theorem exhibits_substitution {s : Split α} {a b c d x : α} (h : s.Exhibits a b c d) :
    s.Exhibits a b c x ∨ s.Exhibits a x c d := by
  obtain ⟨hab, hcd⟩ := h
  have hx : x ∈ s.sideA ∪ s.sideB := by
    rw [s.union_sides]; exact Finset.mem_univ x
  rcases Finset.mem_union.mp hx with hx | hx
  · refine Or.inr ⟨?_, hcd⟩
    rw [Finset.insert_subset_iff, Finset.singleton_subset_iff]
    exact ⟨hab (by simp), hx⟩
  · refine Or.inl ⟨hab, ?_⟩
    rw [Finset.insert_subset_iff, Finset.singleton_subset_iff]
    exact ⟨hcd (by simp), hx⟩

/-! ## 5. 树层推论（把 §2–§4 的 split 层结论搬到树上） -/

end Split

namespace Cladogram

open Phylo

variable {X : Type*} [Fintype X] [DecidableEq X]

variable (T : Cladogram X)

/-- 树 `T` 展出的 quartet 就是「某个 split 展出它」（`DisplaysQuartet` 的定义重述），
这里显式记录 `Exhibits` 版本的桥。 -/
theorem displaysQuartet_iff_exists_exhibits (a b c d : X) :
    T.DisplaysQuartet a b c d ↔
      ∃ s : Split X, T.IsSplitOf s ∧ s.Exhibits a b c d := Iff.rfl

/-- ★★★ **thin（树层）**：同一棵树**不能**在同一个 4-元集上展出**两个不同**的 2|2 配对
（`a,b,c,d` 互异）—— 文献 Lemma 2(i)（`:574–588`）的组合核。

三个配对两两互斥：

* `ab|cd` vs `ac|bd`：`Phylo/Quartet.lean:298` 的 `not_displaysQuartet_swap`；
* `ab|cd` vs `ad|bc`、`ac|bd` vs `ad|bc`：本文件 §3 的四交核
  （`not_displaysQuartet_swap` 只覆盖第一对）。 -/
theorem displaysQuartet_thin {a b c d : X} :
    ¬ (T.DisplaysQuartet a b c d ∧ T.DisplaysQuartet a c b d) ∧
    ¬ (T.DisplaysQuartet a b c d ∧ T.DisplaysQuartet a d b c) ∧
    ¬ (T.DisplaysQuartet a c b d ∧ T.DisplaysQuartet a d b c) := by
  refine ⟨fun h => not_displaysQuartet_swap T h.1 h.2, ?_, ?_⟩
  · rintro ⟨h1, h2⟩
    obtain ⟨s, hs, h1'⟩ := h1
    obtain ⟨t, ht, h2'⟩ := h2
    exact (Split.incompatible_of_exhibits_ab_cd_ad_bc h1' h2')
      (pairwiseCompatible T s hs t ht)
  · rintro ⟨h1, h2⟩
    obtain ⟨s, hs, h1'⟩ := h1
    obtain ⟨t, ht, h2'⟩ := h2
    exact (Split.incompatible_of_exhibits_ac_bd_ad_bc h1' h2')
      (pairwiseCompatible T s hs t ht)

/-- ★★★ **saturated（树层，(S1) 形态）**：若 `T` 展出 `ab|cd`，则对**任意**第五点 `x`，
`T` 展出 `ab|cx` 或 `T` 展出 `ax|cd`（文献 (S1) `:553` 的树层核）。

（⚠️ 与 `Phylo/InternalEdge.lean:661` 的 `displaysQuartet_substitution` 同内容；
此处给出**经 split 层**的证明，以便与 §4 的规则配套。） -/
theorem displaysQuartet_saturated {a b c d x : X} (h : T.DisplaysQuartet a b c d) :
    T.DisplaysQuartet a b c x ∨ T.DisplaysQuartet a x c d := by
  obtain ⟨s, hs, hex⟩ := h
  rcases Split.exhibits_substitution hex with h' | h'
  · exact Or.inl ⟨s, hs, h'⟩
  · exact Or.inr ⟨s, hs, h'⟩

end Cladogram

/-! ## 6. ★B 反例检查：(S1) 的析取**不可**收缩为单支 -/

namespace Split

/-- ★B 具体 split（`Fin 5`）：`{0,1} | {2,3,4}`。 -/
def exN₁ : Split (Fin 5) where
  parts i := if i = 0 then {0, 1} else {2, 3, 4}
  pairwise_disjoint := by decide
  union_eq_univ := by decide
  nonempty := by decide

/-- ★B 具体 split（`Fin 5`）：`{0,1,4} | {2,3}`。 -/
def exN₂ : Split (Fin 5) where
  parts i := if i = 0 then {0, 1, 4} else {2, 3}
  pairwise_disjoint := by decide
  union_eq_univ := by decide
  nonempty := by decide

@[simp] theorem exN₁_sideA : exN₁.sideA = {0, 1} := rfl

@[simp] theorem exN₁_sideB : exN₁.sideB = {2, 3, 4} := rfl

@[simp] theorem exN₂_sideA : exN₂.sideA = {0, 1, 4} := rfl

@[simp] theorem exN₂_sideB : exN₂.sideB = {2, 3} := rfl

/-- ★B：两个 split 都展出 `01|23`。 -/
theorem exN_both_exhibit : exN₁.Exhibits 0 1 2 3 ∧ exN₂.Exhibits 0 1 2 3 := by
  constructor <;> (rw [Exhibits]; decide)

/-- ★B ★★★ **反例**：第五点 `x = 4` 时，(S1) 的析取**两支都可能单独成立**，故
「`ab|cd` ⟹ 总有 `ab|cx`」与「⟹ 总有 `ax|cd`」**都是假命题**：

* `exN₁ = {0,1}|{2,3,4}`：只有 `ab|cx`（`01|24`）成立，`ax|cd`（`04|23`）**不**成立；
* `exN₂ = {0,1,4}|{2,3}`：只有 `ax|cd`（`04|23`）成立，`ab|cx`（`01|24`）**不**成立。

⇒ (S1) 必须是**析取**（这正是文献把 4 个 qnet 选项写成并集的原因，`:553`）。 -/
theorem exhibits_substitution_sharp :
    (exN₁.Exhibits 0 1 2 4 ∧ ¬ exN₁.Exhibits 0 4 2 3) ∧
    (exN₂.Exhibits 0 4 2 3 ∧ ¬ exN₂.Exhibits 0 1 2 4) := by
  constructor
  · constructor <;> (rw [Exhibits]; decide)
  · constructor <;> (rw [Exhibits]; decide)

/-- ★B 反空真：反例里的两个 split **相容**（`{0,1} ⊆ {0,1,4}`），故它们可以共存于同一棵树 ——
即「两支都可能出现」不是空真。 -/
theorem exN_compatible : Compatible exN₁ exN₂ := by
  refine compatible_of_subset_left ?_
  decide

end Split

/-! ## 7. ⬜ 缺口：level-1 载体不存在 -/

namespace Split

/-- ⬜ ★★★ **缺口 N3：level-1 网络载体（Huber et al. 2018 的全部陈述都缺它）**。

本 `def` 是一条**可引用的命题**，它把「Theorem 2 需要什么」写成一条陈述：

> **存在**一套 quarnet/network 载体数据，使得
> (a) **Theorem 2**（`:605`）的规则系统在它上面**可陈述**；
> (b) 该载体上 **cyclative** 规则**非空真** —— 即存在一个 consistent + cyclative + saturated
>     的系统，它**不是**任何该载体的展示系统，且其中**没有**一个 qnet 是「树型」的。

（(b) 就是「quarnet 严格强于 quartet」这一 level-1 内容的**可陈述形式**。）

**为什么在本库不可证（= 缺口的内容，逐条）**：

1. **没有网络载体**。`Phylo/Core.lean:43` 的 `Cladogram.isTree : graph.IsTree` 把载体锁死为
   **树**；`Phylogram`（`:157`）继承之。库内**没有**允许环的图载体，
   故 `level-1`（`:244–246`，判据是「无 cut-edge 的极大子图是顶点或圈」）**无从陈述**。
2. **没有「删边-抑制」限制算子**。文献 `N|A`（`:436–441`）需要「删去不在 `A` 对间路径上的边 →
   删孤立点 → 反复抑制度 2 顶点 → 抑制平行边」；而 `Cladogram` 的 `no_degree_two`
   （`:46`）意味着**库内根本没有度 2 顶点可抑制**，算子无对象。
3. **没有 quarnet 类型学**。Type I–IV（`:496–502`）、记号 `⊕`/`⊖`（`:497`）、
   `L(F)`、`F(N)`（`:505–507`）、三元素限制的 tree/cycle type（`:445–448`）都无载体，
   `cyclative`（`:532–542`）与 (S2)/(S3)（`:557–568`）因此**不可陈述**。
4. **`Σ(N) ⊆ Q(N)` 严格性的反例**（Fig. 4(iv)，`:429–432`）—— 库里也没有 Fig. 4(iv) 的载体。

**本文件给出的**是缺口 (a) 的**树侧（Type I）部分**：
`exhibits_common`（规则 `ab|cx + ab|xd ⟹ ab|cd`）、`displaysQuartet_thin`（Lemma 2(i) 的核）、
`displaysQuartet_saturated`（(S1) 的核）。 -/
def quarnetRules_level1_gap : Prop :=
  ∃ (Qnet Net : Type) (_ : Fintype Qnet) (_ : Fintype Net)
    (displayedBy : Qnet → Net → Prop)
    (minimallyDense consistent cyclative saturated : Finset Qnet → Prop)
    (isTypeI : Qnet → Prop),
    -- (a) Theorem 2（`:605`）的规则系统在该载体上**可陈述**
    (∀ F : Finset Qnet, minimallyDense F → consistent F → cyclative F → saturated F →
      ∃ N : Net, ∀ q : Qnet, q ∈ F ↔ displayedBy q N) ∧
    -- (b) cyclative 规则**非空真**：存在一个非树型、非展示的系统
    (∃ F : Finset Qnet, consistent F ∧ cyclative F ∧ saturated F ∧
      (∀ N : Net, ¬ ∀ q : Qnet, q ∈ F ↔ displayedBy q N) ∧
      ∀ q ∈ F, ¬ isTypeI q)

/-- ⬜ **缺口 N3 的另一半：Theorem 3 的 (D1)–(D3) 刻画**（`:864–880`）。

(D1) 每个 4-元集上展出的 quartet 数为 1 或 2、(D2) `{ab|cd, ad|bc, ax|cd, ac|xd} ⊆ Q ⟹
{ab|dx, bd|ax} ⊆ Q`、(D3) distinguished quartet 的「传播」。这需要**网络层**的
`Q(N)`（displayed，而非 exhibited）—— 与 `quarnetRules_level1_gap` 同一缺载体。
⚠️ 注意 (D1) 允许 `m_Q(Y) = 2`：**树**的 `Q(T)` 恒有 `m = 1`（这正是 `T` 是树的原因），
故 (D1) 的 `m = 2` 分支**不可能**在库内陈述。 -/
def level1QuartetSystem_gap : Prop :=
  ∃ (QuartetSystem : Type) (_ : Fintype QuartetSystem)
    (multiplicity : QuartetSystem → Finset (Fin 5) → ℕ),
    (∀ Q : QuartetSystem, ∀ Y : Finset (Fin 5), Y.card = 4 → multiplicity Q Y = 1 ∨ multiplicity Q Y = 2) ∧
    (∃ (Q : QuartetSystem) (Y : Finset (Fin 5)), Y.card = 4 ∧ multiplicity Q Y = 2)

end Split
