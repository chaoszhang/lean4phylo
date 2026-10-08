/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.Supertree

/-!
# `Phylo.Compatibility` —— **字符相容性定理**（两两相容 ⟹ 全局相容）

**文献**：G. F. Estabrook, C. S. Johnson, F. R. McMorris,
*Foundation of a mathematical analysis of cladistic character compatibility*,
Math. Biosci. **29** (1976) 181–187
（`references/md/EstabrookJohnsonMcMorris1976_FoundationCladisticCharacterCompatibility.md`）。

## 0. 库内**已有**的（本文件**不重复造**）

「两两相容 ⟹ 存在树展示全体」在 **split 层**库内已证，且证了两次：

* `Phylo.Aho.compatible_exists_rootedTree`（`Phylo/Aho.lean:67`）：
  两两相容的非平凡 split 族 ⟹ 存在 `RootedTree` 展示全体（允许换向）；
* ★ `Phylo.Supertree.supertree_displays_of_pairwiseCompatible`（`Phylo/Supertree.lean:411`）：
  两两相容的**任意** split 族 ⟹ 存在 `Cladogram` **定向**展示全体（`IsSplitOf`，不换向），
  只需 `3 ≤ |X|`。

故本文件**不再造第二遍 split 层定理**，转而做 F1 的**字符层加细**：
把「字符」按 EJM 的 **二元因子**（Definition 6）拆成状态类集，在字符层证「两两相容 ⟹ 全局相容」，
**经由**上面这条 split 层定理落地（见 §5 的 `exists_cladogram_of_pairwise_binaryCompatible`）。

## 1. 形式化的边界（诚实声明）

**已形式化**（本文件，均为定理而非公理）：

| EJM 1976 | 内容 | 本文件对应 |
|---|---|---|
| Definition 1 | 树偏序（tree poset） | `IsTreePoset` |
| Definition 5 | 二元字符 | `BinaryCompatible`（判据式）+ `binaryCompatible_iff_no_pattern` |
| Definition 6 | 字符的**二元因子** `K_p = {x \| p ≤ K x}` | `binaryFactor` |
| Lemma 3 | 一个字符的二元因子两两相容 | `binaryFactor_binaryCompatible` |
| Theorem 1 | 两二元字符相容 ⟺ `Im(K₁×K₂)` 是树偏序 | `binaryCompatible_iff_no_pattern`（**集合形式**，见下） |
| Theorem 2（判据） | `K, L` 相容 ⟺ 全部二元因子对相容 | `CharCompatible`（定义即该判据） |
| Conclusion | 两两检查足以判定整体相容 | ★ `pairwise_compatible_characters_have_tree` |

**未形式化**（文献结论，本文件不含）：

* EJM **Definition 2–4 的树半格语义**：字符 `K : S → P`（`P` 树半格）、
  「真字符 = 半格同态」（**Lemma 1**）、「相容 = 存在公共树半格扩张 `S*`」（Definition 4）。
  本文件用其**等价的可操作形式**：字符被树实现 ⟺ 每个二元因子是树的一条边侧
  （`RealizesChar`）；该等价**未**在库内证明。
* **Lemma 2**（二元因子分解的嵌入 `P ↪ T₁ × … × Tₙ`）。
* **Theorem 1 的原文形式**：`Im(K₁ × K₂)` 在 `P₁ × P₂` 中是树偏序（乘积偏序）。
  本文件给出与之等价的集合形式 `binaryCompatible_iff_no_pattern`
  （「`A∩B`、`A∖B`、`B∖A` 三者不全非空」——正是原文证明里用的 `(1,1),(0,1),(1,0)` 三点型）。
* **Theorem 2 的 ⟹ 方向**（相容 ⟹ 因子两两相容）：本文件只证「因子两两相容 ⟹ 相容」。
* **「两两 ⟹ 全局」这一条本身**：EJM 1976 是**引用**它（文中明言由 **Theorem 4 of [4]** 给出，
  即 Estabrook–Johnson–McMorris 1975, *Math. Biosci.* **23**, 263–272 —— **该篇不在 `references/md/`**）。
  本文件对它给出**构造性证明**（经库内 split 层定理），故不依赖那篇文献。

## 2. 两点说明

* 本文件只用状态树的**树偏序**性质（`IsTreePoset`），**不用** `⊓`（树半格的下确界）：
  EJM 的 Lemma 3 与全局结论都只用到「有共同上界 ⟹ 可比」。故假设比原文**更弱**。
* 「存在一个划分使二者的状态类都能被细化」若按**划分格**的字面读法是平凡的
  （两个划分在划分格中的交 —— 即共同细化 —— 恒存在）。EJM 的实质内容是
  **共同的有根树 / 层级**：各状态类必须同时是**同一棵树**的 clade。
  本文件的 `CharCompatible` · `laminarFamily_allBinaryFactors` ·
  `pairwise_compatible_characters_have_tree` 正是这一实质内容。

## 3. 结论一览

* `pairwise_compatible_characters_have_tree` ★：一族两两相容的字符 ⟹
  存在 `Cladogram`，使每个字符的每个非平凡二元因子都是它的一条**边侧**（clade）；
* `pairwise_compatible_characters_have_rootedTree` ★：同上的**有根**版本
  （直接走镶嵌簇族 + `Phylo.toRootedTreeOfCard`，**不经** split 层，只需 `2 ≤ |X|`）；
* `laminarFamily_allBinaryFactors` ★：一族两两相容字符的**全体**二元因子构成**镶嵌族**
  （= EJM 意义下「同时可分化」的组合内容）。
-/

open Phylo
open SimpleGraph

universe u v w

/-! ## §1 字符状态树：树偏序（EJM Definition 1） -/

/-- **树偏序**（EJM 1976, Definition 1）：任意两个有**共同上界**的元素可比。

EJM 原文写作严格序 `a < c ∧ b < c → a < b ∨ b < a`；此处改在 `≤` 上表述 —— 两者等价：
`a = c`（或 `b = c`）时 `≤` 版自动成立（取第二个析取项），反之 `≤` 版直接给出严格版。

字符的**状态树** `P` 就是树半格；树偏序是其被用到的组合性质（不需要 `⊓`）。 -/
def IsTreePoset (P : Type*) [PartialOrder P] : Prop :=
  ∀ a b c : P, a ≤ c → b ≤ c → a ≤ b ∨ b ≤ a

/-! ## §2 二元因子（EJM Definition 6） -/

/-- **二元因子**（EJM Definition 6）：`K_p = {x | p ≤ K x}` —— 把状态 `≥ p` 的类集记为 1、其余记为 0
所得的二元字符。

（EJM 只取 `P` 的非零元 `p₁,…,pₙ`；本库对**所有** `p` 量化 —— 底元的因子恒为 `univ`，
不影响任何相容性判定，省去这一枝节。） -/
noncomputable def binaryFactor {X : Type*} [Fintype X] [DecidableEq X] {P : Type*}
    [PartialOrder P] (K : X → P) (p : P) : Finset X := by
  classical
  exact Finset.univ.filter fun x => p ≤ K x

/-- 二元因子的成员判定（定义展开）。 -/
theorem mem_binaryFactor {X : Type*} [Fintype X] [DecidableEq X] {P : Type*} [PartialOrder P]
    {K : X → P} {p : P} {x : X} : x ∈ binaryFactor K p ↔ p ≤ K x := by
  classical
  simp [binaryFactor]

/-- **因子对状态单增**：`p ≤ q ⟹ K_q ⊆ K_p`。 -/
theorem binaryFactor_mono {X : Type*} [Fintype X] [DecidableEq X] {P : Type*} [PartialOrder P]
    {p q : P} (h : p ≤ q) (K : X → P) : binaryFactor K q ⊆ binaryFactor K p := by
  intro x hx
  rw [mem_binaryFactor] at hx ⊢
  exact le_trans h hx

/-! ## §3 二元字符的相容性（EJM Definition 5 + Theorem 1） -/

/-- **二元字符相容**（EJM Theorem 1 的判据形式）：状态 1 的两类集 `A`、`B` 满足
`A ⊆ B`、`B ⊆ A`、`A ∩ B = ∅` 之一。

⚠️ 与库内 `SidesCompatible`（`Phylo/Split.lean:40`）的差别：后者多一项 `A ∪ B = univ`。
多出的这一项是**无根** split 相容性所需（`A` 与 `B` 可以「各占一边」）；
EJM 的字符相容性是**有根**的（状态树有祖先方向），只有这三项 ——
这正是 EJM Theorem 1「`Im(K₁×K₂)` 是树偏序」的内容。 -/
def BinaryCompatible {X : Type*} [DecidableEq X] (A B : Finset X) : Prop :=
  A ⊆ B ∨ B ⊆ A ∨ Disjoint A B

/-- 二元相容对称。 -/
theorem binaryCompatible_comm {X : Type*} [DecidableEq X] {A B : Finset X} :
    BinaryCompatible A B ↔ BinaryCompatible B A := by
  constructor <;> intro h <;> rcases h with h | h | h
  · exact Or.inr (Or.inl h)
  · exact Or.inl h
  · exact Or.inr (Or.inr (disjoint_comm.mpr h))
  · exact Or.inr (Or.inl h)
  · exact Or.inl h
  · exact Or.inr (Or.inr (disjoint_comm.mpr h))

/-- 空集与任何集合二元相容。 -/
theorem binaryCompatible_empty_left {X : Type*} [DecidableEq X] (B : Finset X) :
    BinaryCompatible ∅ B :=
  Or.inl (Finset.empty_subset B)

/-- 全集与任何集合二元相容。 -/
theorem binaryCompatible_univ_right {X : Type*} [Fintype X] [DecidableEq X] (A : Finset X) :
    BinaryCompatible A Finset.univ :=
  Or.inl (Finset.subset_univ A)

/-- ★ **EJM Theorem 1（集合形式）**：二元字符 `A`、`B` 相容 ⟺
`K₁ × K₂` 的像中**不含** `(1,1)`、`(0,1)`、`(1,0)` 三个值对同时出现，
即 `A ∩ B`、`B ∖ A`、`A ∖ B` 三者**不全非空**。

（原文的「像在 `P₁ × P₂` 中是树偏序」：`(0,0)` 是底元、与一切可比，故唯一可能的
不可比 `(1,0) ≠ (0,1)` 带共同上界 `(1,1)` 的反例恰是这三点型。） -/
theorem binaryCompatible_iff_no_pattern {X : Type*} [DecidableEq X] {A B : Finset X} :
    BinaryCompatible A B ↔ ¬ ∃ x y z : X, x ∈ A ∩ B ∧ y ∈ B \ A ∧ z ∈ A \ B := by
  constructor
  · rintro (h | h | h) ⟨x, y, z, hx, hy, hz⟩
    · exact (Finset.mem_sdiff.mp hz).2 (h (Finset.mem_sdiff.mp hz).1)
    · exact (Finset.mem_sdiff.mp hy).2 (h (Finset.mem_sdiff.mp hy).1)
    · exact (Finset.disjoint_left.mp h) (Finset.mem_inter.mp hx).1 (Finset.mem_inter.mp hx).2
  · intro h
    by_cases hAB : A ⊆ B
    · exact Or.inl hAB
    · by_cases hBA : B ⊆ A
      · exact Or.inr (Or.inl hBA)
      · refine Or.inr (Or.inr ?_)
        rw [Finset.disjoint_iff_inter_eq_empty]
        by_contra hne
        obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hne
        rw [Finset.mem_inter] at hx
        have h1 : ∃ z, z ∈ A ∧ z ∉ B := by
          by_contra hc
          exact hAB fun w hw => by
            by_contra hwB
            exact hc ⟨w, hw, hwB⟩
        have h2 : ∃ y, y ∈ B ∧ y ∉ A := by
          by_contra hc
          exact hBA fun w hw => by
            by_contra hwA
            exact hc ⟨w, hw, hwA⟩
        obtain ⟨z, hzA, hzB⟩ := h1
        obtain ⟨y, hyB, hyA⟩ := h2
        exact h ⟨x, y, z, Finset.mem_inter.mpr hx,
          Finset.mem_sdiff.mpr ⟨hyB, hyA⟩, Finset.mem_sdiff.mpr ⟨hzA, hzB⟩⟩

/-- 「二元因子族镶嵌」与「族成员两两二元相容」是同一件事（定义层面）。 -/
theorem laminarFamily_iff_pairwise_binaryCompatible {X : Type*} [DecidableEq X]
    (F : Finset (Finset X)) :
    LaminarFamily F ↔ ∀ A ∈ F, ∀ B ∈ F, BinaryCompatible A B :=
  ⟨fun h A hA B hB => h A hA B hB, fun h A hA B hB => h A hA B hB⟩

/-! ## §4 单字符：二元因子两两相容（EJM Lemma 3） -/

/-- ★ **EJM Lemma 3**：以树偏序 `P` 为状态树的字符 `K`，其**二元因子两两二元相容**
（事实上两两镶嵌：`p ≤ q` 给 `K_q ⊆ K_p`，`p`、`q` 不可比给 `K_p ∩ K_q = ∅`）。 -/
theorem binaryFactor_binaryCompatible {X : Type*} [Fintype X] [DecidableEq X] {P : Type*}
    [PartialOrder P] (htree : IsTreePoset P) (K : X → P) (p q : P) :
    BinaryCompatible (binaryFactor K p) (binaryFactor K q) := by
  by_cases hpq : p ≤ q
  · exact Or.inr (Or.inl (binaryFactor_mono hpq K))
  · by_cases hqp : q ≤ p
    · exact Or.inl (binaryFactor_mono hqp K)
    · refine Or.inr (Or.inr ?_)
      rw [Finset.disjoint_left]
      intro x hx hx'
      rw [mem_binaryFactor] at hx hx'
      rcases htree p q (K x) hx hx' with h | h
      · exact hpq h
      · exact hqp h

/-! ## §5 二元情形：经由库内 split 层定理的全局结论

EJM 的「两两 ⟹ 全局」的**入口**是二元字符：把二元字符看成 split `A | Aᶜ` 即可接上库内设施。 -/

namespace Cladogram

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- `B` 是 `T` 的一条**边侧**（= `B | Bᶜ` 是 `T` 的某条边给出的 split）。

直接由 `IsSplitOf` 取出 split 的 `sideA`：`B` 是删去某条边 `⟦a,b⟧` 后 `u` 一侧的叶集。
`B = univ`（根簇）与 `B = ∅` 都不是边侧，故本谓词只在**非空真子集**上使用。 -/
def IsSideOf (T : Cladogram X) (B : Finset X) : Prop :=
  ∃ (a b : T.V) (_ : T.graph.Adj a b) (u : T.V), B = T.sideLeaves s(a, b) u

/-- `IsSplitOf s` 就是 `IsSideOf s.sideA`（定义相等）。 -/
theorem isSideOf_of_isSplitOf {T : Cladogram X} {s : Split X} (h : T.IsSplitOf s) :
    T.IsSideOf s.sideA := h

/-- 换一侧改写：`s.sideA = B` 时 `IsSplitOf s` 给出 `IsSideOf B`。 -/
theorem isSideOf_of_isSplitOf_sideA {T : Cladogram X} {s : Split X} {B : Finset X}
    (h : T.IsSplitOf s) (hs : s.sideA = B) : T.IsSideOf B := by
  rw [← hs]; exact h

end Cladogram

/-- 二元相容 ⟹ 对应的两个 split 相容（三个析取项分别走库内的
`compatible_of_subset_left` / `compatible_of_subset_right` / `compatible_of_disjoint`）。 -/
theorem splitOf_compatible_of_binaryCompatible {X : Type*} [Fintype X] [DecidableEq X]
    {A B : Finset X} (h : BinaryCompatible A B)
    (hA : A.Nonempty) (hAc : Aᶜ.Nonempty) (hB : B.Nonempty) (hBc : Bᶜ.Nonempty) :
    Split.Compatible (splitOf A hA hAc) (splitOf B hB hBc) := by
  rcases h with h | h | h
  · exact Split.compatible_of_subset_left (by rw [splitOf_sideA, splitOf_sideA]; exact h)
  · exact Split.compatible_of_subset_right (by rw [splitOf_sideA, splitOf_sideA]; exact h)
  · exact Split.compatible_of_disjoint (by rw [splitOf_sideA, splitOf_sideA]; exact h)

/-- ★★ **二元字符的全局定理**：一族**两两二元相容**的类集 ⟹
存在 `Cladogram`，使每个**非空真**成员都是它的一条**边侧**。

**证明**：非空真成员 ↦ split `A | Aᶜ`；两两相容（`splitOf_compatible_of_binaryCompatible`）；
再用库内 ★★★ `supertree_displays_of_pairwiseCompatible`（`Phylo/Supertree.lean:411`）
—— 这条正是 F1 在 split 层的形态。 -/
theorem exists_cladogram_of_pairwise_binaryCompatible {X : Type u} [Fintype X] [DecidableEq X]
    (F : Finset (Finset X)) (hpair : ∀ A ∈ F, ∀ B ∈ F, BinaryCompatible A B)
    (h3 : 3 ≤ Fintype.card X) :
    ∃ T : Cladogram.{u, u} X, ∀ B ∈ F, B.Nonempty → B ≠ Finset.univ → T.IsSideOf B := by
  classical
  obtain ⟨x₀, -⟩ : (Finset.univ : Finset X).Nonempty :=
    Finset.card_pos.mp (by rw [Finset.card_univ]; omega)
  -- 剥掉空集与全集（它们不可能是边侧，也无需展示）
  set Fn : Finset (Finset X) := F.filter fun B => B.Nonempty ∧ B ≠ Finset.univ with hFn
  set fam : Finset (Split X) := Fn.attach.image fun B : ↥Fn =>
    splitOf B.1 (Finset.mem_filter.mp B.2).2.1
      (compl_nonempty_of_ne_univ (Finset.mem_filter.mp B.2).2.2) with hfam
  have hcomp : ∀ s ∈ fam, ∀ t ∈ fam, Split.Compatible s t := by
    intro s hs t ht
    rw [hfam, Finset.mem_image] at hs ht
    obtain ⟨A, -, rfl⟩ := hs
    obtain ⟨B, -, rfl⟩ := ht
    exact splitOf_compatible_of_binaryCompatible
      (hpair A.1 (Finset.mem_filter.mp A.2).1 B.1 (Finset.mem_filter.mp B.2).1) _ _ _ _
  obtain ⟨T, hT⟩ := supertree_displays_of_pairwiseCompatible fam x₀ hcomp h3
  refine ⟨T, fun B hBF hBne hBuniv => ?_⟩
  have hBmem : B ∈ Fn := Finset.mem_filter.mpr ⟨hBF, hBne, hBuniv⟩
  have hmem : splitOf B (Finset.mem_filter.mp hBmem).2.1
      (compl_nonempty_of_ne_univ (Finset.mem_filter.mp hBmem).2.2) ∈ fam := by
    rw [hfam, Finset.mem_image]
    exact ⟨⟨B, hBmem⟩, Finset.mem_attach _ _, rfl⟩
  exact Cladogram.isSideOf_of_isSplitOf_sideA (hT _ hmem) (splitOf_sideA B _ _)

/-! ## §6 字符层的相容性（EJM Theorem 2 的判据） -/

/-- **两个字符相容**（EJM Theorem 2 的判据形式）：**全部**二元因子对二元相容。

（EJM 的原始定义（Definition 4）是「存在公共树半格扩张使二者皆真」，
Theorem 2 把它化归为二元因子的两两检查 —— 这正是本定义。
「⟸」方向的实现见 `pairwise_compatible_characters_have_tree`。） -/
def CharCompatible {X : Type*} [Fintype X] [DecidableEq X] {P : Type*} [PartialOrder P]
    {Q : Type*} [PartialOrder Q] (K : X → P) (L : X → Q) : Prop :=
  ∀ p : P, ∀ q : Q, BinaryCompatible (binaryFactor K p) (binaryFactor L q)

/-- 字符相容对称。 -/
theorem charCompatible_comm {X : Type*} [Fintype X] [DecidableEq X] {P : Type*}
    [PartialOrder P] {Q : Type*} [PartialOrder Q] {K : X → P} {L : X → Q} :
    CharCompatible K L ↔ CharCompatible L K := by
  constructor <;> intro h p q
  · exact binaryCompatible_comm.mp (h q p)
  · exact binaryCompatible_comm.mp (h q p)

/-- 字符与**自身**相容（EJM Lemma 3 的推论）—— 「两两相容」只需检查**不同**的两个字符。 -/
theorem charCompatible_self {X : Type*} [Fintype X] [DecidableEq X] {P : Type*} [PartialOrder P]
    (htree : IsTreePoset P) (K : X → P) : CharCompatible K K :=
  fun p q => binaryFactor_binaryCompatible htree K p q

/-! ## §7 全局定理（F1）：两两相容 ⟹ 全局相容 -/

variable {X : Type u}

/-- 一族字符的**全体二元因子**（EJM Definition 6 对整族的并）。 -/
noncomputable def allBinaryFactors {X : Type u} [Fintype X] [DecidableEq X]
    {ι : Type v} [Fintype ι] {P : ι → Type w} [∀ i, PartialOrder (P i)]
    [∀ i, Fintype (P i)] [∀ i, DecidableEq (P i)] (K : ∀ i, X → P i) : Finset (Finset X) :=
  (Finset.univ : Finset ι).biUnion fun i =>
    (Finset.univ : Finset (P i)).image (binaryFactor (K i))

/-- `allBinaryFactors` 的成员判定。 -/
theorem mem_allBinaryFactors {X : Type u} [Fintype X] [DecidableEq X]
    {ι : Type v} [Fintype ι] {P : ι → Type w} [∀ i, PartialOrder (P i)]
    [∀ i, Fintype (P i)] [∀ i, DecidableEq (P i)] {K : ∀ i, X → P i} {B : Finset X} :
    B ∈ allBinaryFactors K ↔ ∃ (i : ι) (p : P i), binaryFactor (K i) p = B := by
  classical
  rw [allBinaryFactors, Finset.mem_biUnion]
  constructor
  · rintro ⟨i, -, hB⟩
    rw [Finset.mem_image] at hB
    obtain ⟨p, -, rfl⟩ := hB
    exact ⟨i, p, rfl⟩
  · rintro ⟨i, p, rfl⟩
    exact ⟨i, Finset.mem_univ i, Finset.mem_image.mpr ⟨p, Finset.mem_univ p, rfl⟩⟩

/-- ★ **EJM Lemma 3 + Theorem 2 判据的合流**：若任意两个**不同**字符相容
（同一字符由 Lemma 3 / `charCompatible_self` 处理），则**全体**二元因子两两二元相容。

这就是「两两检查只需在字符层做一次，它就自动升级为因子层的两两相容」。 -/
theorem pairwise_binaryCompatible_allBinaryFactors {X : Type u} [Fintype X] [DecidableEq X]
    {ι : Type v} [Fintype ι] {P : ι → Type w} [∀ i, PartialOrder (P i)]
    [∀ i, Fintype (P i)] [∀ i, DecidableEq (P i)] (K : ∀ i, X → P i)
    (htree : ∀ i, IsTreePoset (P i))
    (hpair : ∀ i j, i ≠ j → CharCompatible (K i) (K j)) :
    ∀ A ∈ allBinaryFactors K, ∀ B ∈ allBinaryFactors K, BinaryCompatible A B := by
  intro A hA B hB
  obtain ⟨i, p, rfl⟩ := mem_allBinaryFactors.mp hA
  obtain ⟨j, q, rfl⟩ := mem_allBinaryFactors.mp hB
  by_cases hij : i = j
  · subst j
    exact charCompatible_self (htree i) (K i) p q
  · exact hpair i j hij p q

/-- ★★ **全局内容的组合形态**：一族两两相容字符的全体二元因子构成**镶嵌簇族**
（= 库内「相容 ⟹ 存在树」的输入形态）。 -/
theorem laminarFamily_allBinaryFactors {X : Type u} [Fintype X] [DecidableEq X]
    {ι : Type v} [Fintype ι] {P : ι → Type w} [∀ i, PartialOrder (P i)]
    [∀ i, Fintype (P i)] [∀ i, DecidableEq (P i)] (K : ∀ i, X → P i)
    (htree : ∀ i, IsTreePoset (P i))
    (hpair : ∀ i j, i ≠ j → CharCompatible (K i) (K j)) :
    LaminarFamily (allBinaryFactors K) :=
  fun A hA B hB => pairwise_binaryCompatible_allBinaryFactors K htree hpair A hA B hB

/-- **字符 `K` 被树 `T` 实现**：每个非空真二元因子都是 `T` 的一条边侧。

（= EJM Definition 3「真字符」在库内语言下的可操作形式：因子 `K_p` 是 `T` 的 clade
⟺ 状态树沿 `T` 的扩张保持半格同态 —— 该等价未在库内证明，见文件头 §1。） -/
def RealizesChar {X : Type u} [Fintype X] [DecidableEq X] {P : Type*} [PartialOrder P]
    (T : Cladogram X) (K : X → P) : Prop :=
  ∀ p : P, (binaryFactor K p).Nonempty → binaryFactor K p ≠ Finset.univ →
    T.IsSideOf (binaryFactor K p)

/-- `RealizesChar` 的「空集/全集无关紧要」形式（用起来方便）。 -/
theorem realizesChar_iff {X : Type u} [Fintype X] [DecidableEq X] {P : Type*} [PartialOrder P]
    (T : Cladogram X) (K : X → P) :
    RealizesChar T K ↔ ∀ p : P,
      binaryFactor K p = ∅ ∨ binaryFactor K p = Finset.univ ∨ T.IsSideOf (binaryFactor K p) := by
  constructor
  · intro h p
    by_cases hp : (binaryFactor K p).Nonempty
    · by_cases hu : binaryFactor K p = Finset.univ
      · exact Or.inr (Or.inl hu)
      · exact Or.inr (Or.inr (h p hp hu))
    · exact Or.inl (by simpa using hp)
  · rintro h p hp hu
    rcases h p with h | h | h
    · rw [h] at hp; exact absurd hp (by simp)
    · exact absurd h hu
    · exact h

/-- ★★★ **字符相容性定理（F1）**：一族**两两相容**的字符 ⟹
存在一棵 `Cladogram` **同时实现**它们全体。

* `K : ∀ i, X → P i` —— 第 `i` 个字符（状态集 `P i`）；
* `htree` —— 每个状态集是**树偏序**（EJM Definition 1，即状态树）；
* `hpair` —— **任意两个不同**字符相容（同一字符由 `charCompatible_self` 自动相容）；
* `h3` —— `3 ≤ |X|`（库内 split 层定理的退化条件，见 `Phylo/Supertree.lean`）。

**证明路线**：`allBinaryFactors` 两两二元相容（`pairwise_binaryCompatible_allBinaryFactors`）
⟹ 经 `exists_cladogram_of_pairwise_binaryCompatible`
⟹ 库内 `supertree_displays_of_pairwiseCompatible`。 -/
theorem pairwise_compatible_characters_have_tree {X : Type u} [Fintype X] [DecidableEq X]
    {ι : Type v} [Fintype ι] {P : ι → Type w} [∀ i, PartialOrder (P i)]
    [∀ i, Fintype (P i)] [∀ i, DecidableEq (P i)] (K : ∀ i, X → P i)
    (htree : ∀ i, IsTreePoset (P i))
    (hpair : ∀ i j, i ≠ j → CharCompatible (K i) (K j)) (h3 : 3 ≤ Fintype.card X) :
    ∃ T : Cladogram.{u, u} X, ∀ i, RealizesChar T (K i) := by
  obtain ⟨T, hT⟩ := exists_cladogram_of_pairwise_binaryCompatible (allBinaryFactors K)
    (pairwise_binaryCompatible_allBinaryFactors K htree hpair) h3
  exact ⟨T, fun i p hne hnu =>
    hT (binaryFactor (K i) p) (mem_allBinaryFactors.mpr ⟨i, p, rfl⟩) hne hnu⟩

/-! ## §8 有根形式：直接走镶嵌簇族（不经 split 层，只需 `2 ≤ |X|`）

`Phylo.toRootedTreeOfCard`（`Phylo/Laminar.lean:1794`）把**镶嵌簇族**变成 `RootedTree`，
且族成员恰为边侧（`leafSide_parentEdge_of_card`）。于是上一条的组合内容
（`laminarFamily_allBinaryFactors`）可以直接落地为**有根树** —— 这正是 EJM 的 `S*`
（有根树半格）的库内对应物。 -/

namespace RootedTree

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- `B` 是 `RootedTree` `T` 的一条**边侧**（边的叶侧 = clade）。 -/
def IsSideOf (T : RootedTree X) (B : Finset X) : Prop :=
  ∃ (a b : T.V) (_ : T.graph.Adj a b) (u : T.V), B = T.sideLeaves s(a, b) u

end RootedTree

/-- **单点集总是边侧**（叶边的叶侧）。 -/
theorem RootedTree.isSideOf_singleton {X : Type*} [Fintype X] (T : RootedTree X) (x : X) :
    T.IsSideOf {x} := by
  classical
  have hdeg : T.graph.degree (T.leaf x) = 1 :=
    (T.leaf_iff_degree_one (T.leaf x)).mp ⟨x, rfl⟩
  obtain ⟨b, hb, huniq⟩ := degree_eq_one_iff_existsUnique_adj.mp hdeg
  have hiso : (T.graph.deleteEdges {s(T.leaf x, b)}).IsIsolated (T.leaf x) := by
    intro w hw
    rw [SimpleGraph.deleteEdges_adj] at hw
    exact hw.2 (by rw [huniq w hw.1]; simp)
  refine ⟨T.leaf x, b, hb, T.leaf x, ?_⟩
  ext y
  simp only [RootedTree.sideLeaves, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_singleton]
  constructor
  · rintro rfl
    exact SimpleGraph.Walk.nil.reachable
  · intro hy
    exact T.leaf.injective (reachable_eq_of_isIsolated hiso (reachable_comm.mpr hy))

set_option maxHeartbeats 800000 in
/-- ★★★ **字符相容性定理（有根形式）**：一族两两相容的字符 ⟹
存在一棵**有根树**，使每个字符的每个非平凡二元因子都是它的一条**边侧**（clade）。

与 `pairwise_compatible_characters_have_tree` 相比：
* 结论是 `RootedTree`（EJM 的 `S*` 是有根树半格）；
* 证明**不经** split 层，直接 `laminarFamily_allBinaryFactors` + `toRootedTreeOfCard`；
* 只需 `2 ≤ |X|`（无根版需要 `3 ≤ |X|`，那是 `toCladogram` 的根非退化条件）。 -/
theorem pairwise_compatible_characters_have_rootedTree {X : Type u} [Fintype X] [DecidableEq X]
    {ι : Type v} [Fintype ι] {P : ι → Type w} [∀ i, PartialOrder (P i)]
    [∀ i, Fintype (P i)] [∀ i, DecidableEq (P i)] (K : ∀ i, X → P i)
    (htree : ∀ i, IsTreePoset (P i))
    (hpair : ∀ i j, i ≠ j → CharCompatible (K i) (K j)) (h2 : 2 ≤ Fintype.card X) :
    ∃ T : RootedTree.{u, u} X, ∀ i (p : P i), (binaryFactor (K i) p).Nonempty →
      binaryFactor (K i) p ≠ Finset.univ → T.IsSideOf (binaryFactor (K i) p) := by
  classical
  set F : Finset (Finset X) := allBinaryFactors K with hF
  have hl : LaminarFamily F := by
    rw [hF]; exact laminarFamily_allBinaryFactors K htree hpair
  set F' : Finset (Finset X) := normFinset F with hF'
  have hmemF' : ∀ B : Finset X, B ∈ F' ↔ B = Finset.univ ∨ (B ∈ F ∧ 2 ≤ B.card) := by
    intro B; rw [hF']; exact mem_normFinset
  have hl' : LaminarFamily F' := by rw [hF']; exact laminarFamily_normFinset hl
  have huniv' : (Finset.univ : Finset X) ∈ F' := by rw [hF']; exact univ_mem_normFinset
  have hcard' : ∀ B ∈ F', B = Finset.univ ∨ 2 ≤ B.card := by
    intro B hB
    rcases (hmemF' B).mp hB with h | h
    · exact Or.inl h
    · exact Or.inr h.2
  have hne' : ∀ B ∈ F', B.Nonempty := nonempty_of_mem_of_hcard hcard' h2
  refine ⟨toRootedTreeOfCard hl' huniv' hcard' h2, fun i p hne hnu => ?_⟩
  have hBF : binaryFactor (K i) p ∈ F := by
    rw [hF]; exact mem_allBinaryFactors.mpr ⟨i, p, rfl⟩
  by_cases hcard : 2 ≤ (binaryFactor (K i) p).card
  · have hBmem' : binaryFactor (K i) p ∈ F' := (hmemF' _).mpr (Or.inr ⟨hBF, hcard⟩)
    have hleaf : leafSide F'
        (parentEdge hl' hne' huniv' (binaryFactor (K i) p) hBmem' hnu)
        (Sum.inl (⟨binaryFactor (K i) p, hBmem'⟩ : ↥F')) = binaryFactor (K i) p :=
      leafSide_parentEdge_of_card hl' huniv' hcard' h2 hBmem' hnu
    have hadj : (treeGraph F').Adj
        (Sum.inl (⟨binaryFactor (K i) p, hBmem'⟩ : ↥F'))
        (Sum.inl (parentV hl' hne' huniv' (⟨binaryFactor (K i) p, hBmem'⟩ : ↥F') hnu)) :=
      (treeGraph_adj_inl_inl F' ⟨binaryFactor (K i) p, hBmem'⟩
        (parentV hl' hne' huniv' ⟨binaryFactor (K i) p, hBmem'⟩ hnu)).mpr
        (Or.inl (isParentOf_parentOf (A := binaryFactor (K i) p) hl' hne' huniv' hBmem' hnu))
    refine ⟨Sum.inl (⟨binaryFactor (K i) p, hBmem'⟩ : ↥F'),
      Sum.inl (parentV hl' hne' huniv' (⟨binaryFactor (K i) p, hBmem'⟩ : ↥F') hnu),
      hadj, Sum.inl (⟨binaryFactor (K i) p, hBmem'⟩ : ↥F'), ?_⟩
    show binaryFactor (K i) p = leafSide F'
      s(Sum.inl (⟨binaryFactor (K i) p, hBmem'⟩ : ↥F'),
        Sum.inl (parentV hl' hne' huniv' (⟨binaryFactor (K i) p, hBmem'⟩ : ↥F') hnu))
      (Sum.inl (⟨binaryFactor (K i) p, hBmem'⟩ : ↥F'))
    exact hleaf.symm
  · have hcard1 : (binaryFactor (K i) p).card = 1 := by
      have := Finset.card_pos.mpr hne
      omega
    obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hcard1
    rw [hx]
    exact RootedTree.isSideOf_singleton _ x
