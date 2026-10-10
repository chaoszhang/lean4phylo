/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.Compatibility

/-!
# `Phylo.PerfectPhylogeny` —— **完美系统发生（perfect phylogeny）与 Four Gamete 条件**

**任务**：W11d / X2（Gusfield 1991 完美系统发生）。

## 0. 文献（**逐字核读 + 行号**）

⚠️ **来源边界（诚实声明）**：派单点名的两篇**都不在库内** ——

* **Gusfield 1991**, *Efficient algorithms for inferring evolutionary trees*,
  *Networks* **21**:257–269 —— 见 `W11_MISSING_LITERATURE.md:50`：
  「**Gusfield 1991**（→ X2 完美系统发生算法）｜*Networks* **21**:257–269｜
  `10.1002/net.3230210104`（⚠️ **不是** `…304`）｜`LamGusfieldSridhar2009`（已入库）」。
  ⇒ 该篇属本库**已知缺失、非阻塞**的原始出处；**指定替代**（已入库、Gusfield 本人为作者）：
  `references/md/LamGusfieldSridhar2009_PerfectPhylogenyThreeStateCharactersarXiv0905.1417.md`。
  （⚠️ 派单里的出处「*Networks* **1**(2):133–151」与已联网核实的 **21**:257–269 **不符** —— 见上文。）
* **Semple & Steel 2003**, *Phylogenetics*（第 4 章）—— 库内 `references/` **只有**该书的
  `SempleSteel2000_MinCutSupertree` 与 `SempleSteel2002_TreeReconstructionMultiStateCharacters`
  两篇**论文**，**教科书本体不在库内**。故本文件**不**引用该书页码/行号。

以下定理陈述**逐字**引自替代文献（行号为该 `.md` 文件行号）：

* **完美系统发生的定义**（193–205 行）：

  > The perfect phylogeny problem is to determine whether an input set S can be
  > displayed on a tree such that
  > (1) each sequence in input set S labels exactly one leaf in T
  > (2) each vertex of T is labeled by a species
  > (3) for every character χi and for every state χi_j of character χi, the set of all
  > vertices in T such that the state of character χi is χi_j forms a connected
  > subtree of T .

* ★★★ **Theorem 1.1（Splits Equivalence Theorem / Four Gamete Condition）**（104–106 行）：

  > **Theorem 1.1 (Splits Equivalence Theorem, Four Gamete Condition
  > [11, 15, 27]).** A perfect phylogeny exists for binary input sequences if and only if no
  > pair of characters contains all four possible binary pairs 00, 01, 10, 11.

* ★ **Theorem 2.4**（276–278 行）—— 为什么 two-state 特殊：

  > **Theorem 2.4.** Given an input set S on m characters with at most three states per
  > character (r ≤ 3), S admits a perfect phylogeny if and only if every subset of three
  > characters of S admits a perfect phylogeny.

* ★★ **两两相容对多状态不充分**（131–140 行）：

  > In 1975, Fitch gave an example of input S over three states such that every pair
  > of characters in S allows a perfect phylogeny while the entire set of characters S
  > does not [12, 13, 14, 30]. …
  > “The Fitch examples show that any algorithm to determine whether
  > a set of characters is compatible must consider the set as a whole
  > and cannot take the shortcut of only checking pairs of characters.” [27]

* ★★ **Theorem 7.1（Fitch–Meacham `F_r`）**（1290–1292 行）：

  > **Theorem 7.1.** [27] For every r ≥ 2, Fr is a set of input sequences over r state
  > characters such that every r −1 subset of characters allows a perfect phylogeny while
  > the entire set Fr does not allow a perfect phylogeny.

## 1. 本文件的定位（**不重复造库内已有的**）

「两两相容 ⟹ 存在树展示全体」在库内的 **split 层**已证：
`supertree_displays_of_pairwiseCompatible`（`Phylo/Supertree.lean:411`）；
**字符层**（EJM 树偏序 / `CharCompatible`）在 `Phylo/Compatibility.lean` 已证
（`pairwise_compatible_characters_have_tree`）。

本文件补的是 **Gusfield Theorem 1.1 的那一层**：**二元字符**的完美系统发生，
其判据是 **`SidesCompatible`**（`Phylo/Split.lean:40`）——
**不是** EJM 的 `BinaryCompatible`（`Phylo/Compatibility.lean:129`）。

### ★B 为什么必须是 `SidesCompatible` 而不是 `BinaryCompatible`（反例检查）

「两两相容是否**充分**？首先，『相容』用哪个谓词？」

库内 `BinaryCompatible A B := A ⊆ B ∨ B ⊆ A ∨ Disjoint A B`（有根 / 祖先态固定的 EJM 判据），
而 Gusfield 条件 (3) 允许**任一侧**作为状态类 ⟹ 正确的相容谓词是
`SidesCompatible A B := A ⊆ B ∨ B ⊆ A ∨ Disjoint A B ∨ A ∪ B = univ`（多出的第 4 项
`A ∪ B = univ` 正是「根的状态为 1」的那一支）。

**最小反例**：`X = {0,1,2}`、`A = {0,1}`、`B = {0,2}`。
**完美系统发生存在**（★C，见 `perfectPhylogeny_pair_witness`：三叶星形树，
中心标 `(1,1)`、叶 `0` 标 `(1,1)`、叶 `1` 标 `(1,0)`、叶 `2` 标 `(0,1)`），
但 `BinaryCompatible A B` **为假**（`not_binaryCompatible_witness`）。
⇒ **`BinaryCompatible` 过强，用它会漏掉真正的完美系统发生** ✗；
`CharCompatible`（由 `BinaryCompatible` 定义）因此在 two-state 下**严格强于** Theorem 1.1 的判据
（`charCompatible_imp_sidesCompatible` 是一个方向，另一个方向有反例）。

**多状态呢？不充分** ✗ —— 但那要换**语义**：Gusfield 条件 (3) 用的是**连通子树**，
而库内 `Cladogram.IsSideOf`（`Phylo/Compatibility.lean:228`）只给出「**边侧**」。
对 **2 个状态**两者一致（两状态类都连通 ⟹ 恰换一次 ⟹ 1-类是边侧）；
对 **≥3 个状态**「连通」**严格更弱**（例：毛虫树 `a—v₁—v₂—v₃—v₄—d`、`b@v₂`、`c@v₃`，
`{b,c}` 连通但**不是任何边的侧**），于是 `F₃` 反例（`MultiStatePairwiseInsufficiencyGap`）。
⚠️ 注意：在**边侧**语义下两两 ⟹ 全局**仍成立**（走 `supertree_displays_of_pairwiseCompatible`），
所以多状态的不充分**不可能**在边侧语义里看到 —— 这正是缺口的实质。

## 2. 结论一览

* `sidesCompatible_iff_no_four_gametes` ★★：`SidesCompatible A B` ⟺ 不含四个 gamete
  （`00,01,10,11` 全出现）—— Theorem 1.1 里那个「pairwise test」的组合内核（`O(nm²)` 那一层）；
* `exists_cladogram_displays_of_pairwise_sidesCompatible` ★★：两两 `SidesCompatible` ⟹
  存在 `Cladogram` 展示全体（二元字符）；
* `pairwise_sidesCompatible_of_exists_cladogram_displays` ★★：**反向**（完美系统发生 ⟹ 两两相容）；
* `exists_cladogram_displays_iff_pairwise_sidesCompatible` ★★★：**等价刻画**（`3 ≤ |X|`）；
* `hasPerfectPhylogeny_iff_matrixPairwiseCompatible` ★★★：**字符矩阵**版本（Theorem 1.1 本体的形态）。

## 3. 缺口（显式 `def … : Prop`，**未证**，不得当作已证）

* `BinaryConnectedEqualsSideGap` —— Gusfield 条件 (3) 的「连通子树」语义与库内「边侧」的等价（r = 2）；
* `MultiStatePairwiseInsufficiencyGap` —— `F₃`（5 taxa × 3 字符 × 3 状态）两两相容但全局不相容。
-/

open Phylo
open SimpleGraph

universe u v w

variable {X : Type u} [Fintype X] [DecidableEq X]

/-! ## §1 Four Gamete 条件的组合内核（`O(nm²)` 那一层）

文献：`LamGusfieldSridhar2009` 104–106 行（Theorem 1.1）。
`SidesCompatible` 的定义在 `Phylo/Split.lean:40`（本库现成，**不重复造**）。 -/

/-- ★★ **Four Gamete 判据（`Phylo/Split.lean:40` 的 `SidesCompatible` 的显式形态）**：
`A`、`B` 两侧相容 ⟺ **不存在**同时出现的四个 gamete
`A∩B`（`11`）、`A∖B`（`10`）、`B∖A`（`01`）、`(A∪B)ᶜ`（`00`）。

文献（逐字，`LamGusfieldSridhar2009` 104–106 行）：
"A perfect phylogeny exists for binary input sequences if and only if no pair of characters
contains all four possible binary pairs 00, 01, 10, 11."

这就是 Theorem 1.1 里那个**逐对检查**的组合内核；配 `binaryFactor` 后即 `O(nm²)` 的判据。 -/
theorem sidesCompatible_iff_no_four_gametes {A B : Finset X} :
    SidesCompatible A B ↔
      ¬ ∃ w x y z : X,
        w ∈ A ∩ B ∧ x ∈ A \ B ∧ y ∈ B \ A ∧ z ∈ (A ∪ B)ᶜ := by
  constructor
  · rintro (h | h | h | h) ⟨w, x, y, z, hw, hx, hy, hz⟩
    · exact (Finset.mem_sdiff.mp hx).2 (h (Finset.mem_sdiff.mp hx).1)
    · exact (Finset.mem_sdiff.mp hy).2 (h (Finset.mem_sdiff.mp hy).1)
    · exact (Finset.disjoint_left.mp h) (Finset.mem_inter.mp hw).1 (Finset.mem_inter.mp hw).2
    · exact (Finset.mem_compl.mp hz) (by rw [h]; exact Finset.mem_univ z)
  · intro h
    by_cases hAB : A ⊆ B
    · exact Or.inl hAB
    · by_cases hBA : B ⊆ A
      · exact Or.inr (Or.inl hBA)
      · by_cases hd : Disjoint A B
        · exact Or.inr (Or.inr (Or.inl hd))
        · refine Or.inr (Or.inr (Or.inr ?_))
          have hx : ∃ x, x ∈ A ∧ x ∉ B := by
            by_contra hc
            exact hAB fun a ha => by
              by_contra h'
              exact hc ⟨a, ha, h'⟩
          have hy : ∃ y, y ∈ B ∧ y ∉ A := by
            by_contra hc
            exact hBA fun a ha => by
              by_contra h'
              exact hc ⟨a, ha, h'⟩
          have hw : ∃ w, w ∈ A ∧ w ∈ B := by
            by_contra hc
            exact hd (Finset.disjoint_left.mpr fun x hxA hxB => hc ⟨x, hxA, hxB⟩)
          by_contra hne
          obtain ⟨z, hz⟩ := compl_nonempty_of_ne_univ hne
          obtain ⟨x, hxA, hxB⟩ := hx
          obtain ⟨y, hyB, hyA⟩ := hy
          obtain ⟨w, hwA, hwB⟩ := hw
          exact h ⟨w, x, y, z, Finset.mem_inter.mpr ⟨hwA, hwB⟩,
            Finset.mem_sdiff.mpr ⟨hxA, hxB⟩, Finset.mem_sdiff.mpr ⟨hyB, hyA⟩, hz⟩

/-! `SidesCompatible` 的**对称性**、**补侧不变**、以及 `Split.Compatible ⟺ SidesCompatible`
**库内现成**，本文件不重复造：

* `sidesCompatible_comm`（`Phylo/Split.lean:106`）；
* `sidesCompatible_compl_left` / `sidesCompatible_compl_right`（`Phylo/Split.lean:47/119`）；
* ★ `Split.compatible_iff_sides`（`Phylo/Split.lean:338`）：
  `Compatible s t ↔ SidesCompatible s.sideA t.sideA`。 -/

/-- ★ **`BinaryCompatible` ⟹ `SidesCompatible`**（EJM 判据 ⟹ Four Gamete 判据）。
前三个析取项逐字相同；`SidesCompatible` 多出的第 4 项 `A ∪ B = univ`
对应「根的状态为 1」这一支 —— 即**允许任一侧**作状态类。 -/
theorem binaryCompatible_imp_sidesCompatible {A B : Finset X}
    (h : BinaryCompatible A B) : SidesCompatible A B := by
  unfold BinaryCompatible at h
  unfold SidesCompatible
  rcases h with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))

/-- 二态字符若只有一个状态（`A = ∅` 或 `A = univ`），则它与任何字符相容（**非空真**辅助）。 -/
theorem sidesCompatible_of_eq_empty_or_univ {A B : Finset X}
    (hA : A = ∅ ∨ A = Finset.univ) : SidesCompatible A B := by
  rcases hA with h | h
  · rw [h]; exact Or.inl (Finset.empty_subset B)
  · rw [h]; exact Or.inr (Or.inl (Finset.subset_univ B))

/-- 同上，作用于右侧。 -/
theorem sidesCompatible_of_eq_empty_or_univ_right {A B : Finset X}
    (hB : B = ∅ ∨ B = Finset.univ) : SidesCompatible A B := by
  rcases hB with h | h
  · rw [h]; exact Or.inr (Or.inl (Finset.empty_subset A))
  · rw [h]; exact Or.inl (Finset.subset_univ A)

/-! ## §2 二元字符的「展示」关系与完美系统发生

文献（`LamGusfieldSridhar2009` 193–205 行）：条件 (3) 要求每个状态类
「forms a connected subtree of T」。本库 `Cladogram.IsSideOf`（`Phylo/Compatibility.lean:228`）
给出「是某条边的**叶侧**」——对**二元**字符两者一致（见 §3 缺口声明），故此处以 `IsSideOf` 为定义。 -/

/-- `T` **展示**二元字符（以 1-类 `A ⊆ X` 表示）。单态字符（`A = ∅` 或 `A = univ`）
无信息量、恒被展示，故走前两个析取项。 -/
def DisplaysBinary (T : Cladogram X) (A : Finset X) : Prop :=
  A = ∅ ∨ A = Finset.univ ∨ T.IsSideOf A

omit [DecidableEq X] in
/-- 所有非平凡二元字符都是「单次替换」（**非空真**辅助）。 -/
theorem displaysBinary_of_isSideOf {T : Cladogram X} {A : Finset X} (h : T.IsSideOf A) :
    DisplaysBinary T A :=
  Or.inr (Or.inr h)

/-- **二元字符矩阵的 1-类**：`{x | M i x = true}`（EJM Definition 6 的 `binaryFactor` 在 `Bool` 的特例）。 -/
noncomputable def charOneClass {ι : Type v} (M : ι → X → Bool) (i : ι) : Finset X :=
  binaryFactor (M i) true

/-- ★★ **二元字符矩阵的完美系统发生**（Gusfield 193–205 行条件 (1)(2)(3) 的二元形态）：
存在一棵 `Cladogram`，使每个字符的 1-类是它的一条边侧（⟺ 每个字符**至多改变一次**，无同塑性）。 -/
def HasPerfectPhylogeny {ι : Type v} (M : ι → X → Bool) : Prop :=
  ∃ T : Cladogram.{u, u} X, ∀ i : ι, DisplaysBinary T (charOneClass M i)

/-- ★★ **矩阵两两相容**（Four Gamete 条件的否定形式，逐对检查）。 -/
def MatrixPairwiseCompatible {ι : Type v} (M : ι → X → Bool) : Prop :=
  ∀ i j : ι, i ≠ j → SidesCompatible (charOneClass M i) (charOneClass M j)

/-- **相容性无需比较字符自身**（自反性）：同一字符的两个 1-类相同 ⟹ 相容。 -/
theorem sidesCompatible_self (A : Finset X) : SidesCompatible A A :=
  Or.inl (Finset.Subset.refl A)

/-- **库内 `CharCompatible`（EJM 判据）⟹ 本文件的 two-state 判据**。
反向**不成立**（`not_binaryCompatible_witness`）⟹ EJM 的 `CharCompatible` **严格强于**
Gusfield Theorem 1.1 的判据。 -/
theorem charCompatible_imp_sidesCompatible {K L : X → Bool}
    (h : CharCompatible K L) :
    SidesCompatible (binaryFactor K true) (binaryFactor L true) :=
  binaryCompatible_imp_sidesCompatible (h true true)

/-- **库内 `RealizesChar` 是一类完美系统发生**：`RealizesChar T K` ⟹ `T` 展示 `K` 的 1-类。
（把 `Phylo/Compatibility.lean` 的树偏序层与本文件的 two-state 层接起来。） -/
theorem displaysBinary_of_realizesChar {T : Cladogram X} {K : X → Bool}
    (h : RealizesChar T K) : DisplaysBinary T (binaryFactor K true) := by
  by_cases hne : (binaryFactor K true).Nonempty
  · by_cases hun : binaryFactor K true = Finset.univ
    · exact Or.inr (Or.inl hun)
    · exact Or.inr (Or.inr (h true hne hun))
  · exact Or.inl (Finset.not_nonempty_iff_eq_empty.mp hne)

/-! ## §3 ★★ 充分性：两两 `SidesCompatible` ⟹ 存在 `Cladogram` 展示全体

**证明路线**：非平凡 1-类 ↦ split `A | Aᶜ`（`splitOf`）；
`SidesCompatible` ⟹ `Split.Compatible`（`Split.compatible_of_sides`，`Phylo/Split.lean:293`）；
再用库内 ★★★ `supertree_displays_of_pairwiseCompatible`（`Phylo/Supertree.lean:411`）。
这与 `Phylo/Compatibility.lean` 的 `exists_cladogram_of_pairwise_binaryCompatible` 同构，
但**输入谓词是较弱的 `SidesCompatible`**，故**不能**由它代劳。 -/

theorem exists_cladogram_displays_of_pairwise_sidesCompatible
    {ι : Type v} [Fintype ι] [DecidableEq ι] (A : ι → Finset X)
    (hpair : ∀ i j, i ≠ j → SidesCompatible (A i) (A j)) (h3 : 3 ≤ Fintype.card X) :
    ∃ T : Cladogram.{u, u} X, ∀ i, DisplaysBinary T (A i) := by
  classical
  obtain ⟨ρ, -⟩ : (Finset.univ : Finset X).Nonempty :=
    Finset.card_pos.mp (by rw [Finset.card_univ]; omega)
  -- 剥掉单态字符（`∅` / `univ` 都不可能是边侧，也无需展示）
  set G : Finset ι := Finset.univ.filter fun i => (A i).Nonempty ∧ A i ≠ Finset.univ with hG
  set fam : Finset (Split X) := G.attach.image fun i : ↥G =>
    splitOf (A i.1) (Finset.mem_filter.mp i.2).2.1
      (compl_nonempty_of_ne_univ (Finset.mem_filter.mp i.2).2.2) with hfam
  have hcomp : ∀ s ∈ fam, ∀ t ∈ fam, Split.Compatible s t := by
    intro s hs t ht
    rw [hfam, Finset.mem_image] at hs ht
    obtain ⟨i, -, rfl⟩ := hs
    obtain ⟨j, -, rfl⟩ := ht
    by_cases hij : i.1 = j.1
    · have hsub : i = j := Subtype.ext hij
      subst hsub
      exact Split.compatible_of_subset_left (Finset.Subset.refl _)
    · exact Split.compatible_of_sides (hpair i.1 j.1 hij)
  obtain ⟨M, hM⟩ := supertree_displays_of_pairwiseCompatible fam ρ hcomp h3
  refine ⟨M, fun i => ?_⟩
  by_cases hne : (A i).Nonempty
  · by_cases hun : A i = Finset.univ
    · exact Or.inr (Or.inl hun)
    · refine Or.inr (Or.inr ?_)
      have hiG : i ∈ G := by
        rw [hG]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hne, hun⟩
      have hmem : splitOf (A i) hne (compl_nonempty_of_ne_univ hun) ∈ fam := by
        rw [hfam, Finset.mem_image]
        exact ⟨⟨i, hiG⟩, Finset.mem_attach _ _, rfl⟩
      exact Cladogram.isSideOf_of_isSplitOf_sideA (hM _ hmem) (splitOf_sideA (A i) _ _)
  · exact Or.inl (Finset.not_nonempty_iff_eq_empty.mp hne)

/-- ★★ **必要性（反向）**：完美系统发生 ⟹ 两两相容。

「两条边侧必 `SidesCompatible`」是库内现成的
`Cladogram.sidesCompatible_sideLeaves`（`Phylo/Split.lean:780`）——
**这正是 `SidesCompatible` 第 4 项 `A ∪ B = univ` 不可省的原因**：
取任意根后「向下的 clade」才镶嵌，而 `IsSideOf` 允许**两侧**任取。 -/
theorem pairwise_sidesCompatible_of_exists_cladogram_displays
    {ι : Type v} (A : ι → Finset X)
    (h : ∃ T : Cladogram.{u, u} X, ∀ i, DisplaysBinary T (A i)) :
    ∀ i j, i ≠ j → SidesCompatible (A i) (A j) := by
  intro i j _
  obtain ⟨T, hT⟩ := h
  rcases hT i with hAi | hAi | hAi
  · exact sidesCompatible_of_eq_empty_or_univ (Or.inl hAi)
  · exact sidesCompatible_of_eq_empty_or_univ (Or.inr hAi)
  · rcases hT j with hAj | hAj | hAj
    · exact sidesCompatible_of_eq_empty_or_univ_right (Or.inl hAj)
    · exact sidesCompatible_of_eq_empty_or_univ_right (Or.inr hAj)
    · obtain ⟨a, b, hab, u, hu⟩ := hAi
      obtain ⟨c, d, hcd, w, hw⟩ := hAj
      rw [hu, hw]
      exact Cladogram.sidesCompatible_sideLeaves T hab hcd u w

/-- ★★★ **完美系统发生的等价刻画（two-state / 二元字符）**：

> 存在展示给定二元字符矩阵的完美系统发生 ⟺ 字符两两相容。

文献依据：`LamGusfieldSridhar2009` **Theorem 1.1**（104–106 行，Four Gamete Condition）。
「相容」取 Gusfield 的形态 = 本库 `SidesCompatible`（第 4 项 `A ∪ B = univ` 不可省，见 §B）。
⚠️ `3 ≤ |X|` 是库内 split 层定理的退化条件（`Phylo/Supertree.lean`）。 -/
theorem exists_cladogram_displays_iff_pairwise_sidesCompatible
    {ι : Type v} [Fintype ι] [DecidableEq ι] (A : ι → Finset X)
    (h3 : 3 ≤ Fintype.card X) :
    (∃ T : Cladogram.{u, u} X, ∀ i, DisplaysBinary T (A i)) ↔
      (∀ i j, i ≠ j → SidesCompatible (A i) (A j)) :=
  ⟨fun h => pairwise_sidesCompatible_of_exists_cladogram_displays A h,
   fun h => exists_cladogram_displays_of_pairwise_sidesCompatible A h h3⟩

/-- ★★★ **Theorem 1.1 的字符矩阵形态**：二元字符矩阵有完美系统发生 ⟺ 逐对无四个 gamete
（`MatrixPairwiseCompatible` 经 `sidesCompatible_iff_no_four_gametes` 即「无 00/01/10/11」）。 -/
theorem hasPerfectPhylogeny_iff_matrixPairwiseCompatible
    {ι : Type v} [Fintype ι] [DecidableEq ι] (M : ι → X → Bool)
    (h3 : 3 ≤ Fintype.card X) :
    HasPerfectPhylogeny M ↔ MatrixPairwiseCompatible M :=
  exists_cladogram_displays_iff_pairwise_sidesCompatible (charOneClass M) h3

/-! ## §4 ★C 最小例子（3 taxa / 2 字符）端到端

`X = Fin 3`、字符 1-类 `A = {0,1}`、`B = {0,2}`（即「根的状态为 1」那一支）。
`BinaryCompatible A B` **为假**，但完美系统发生**存在**。
（穷举核验：`scripts/msc/w11d_x2_perfect_phylogeny.py`。） -/

/-- ★B **反例**：`A = {0,1}`、`B = {0,2}`（`X = Fin 3`）**不** `BinaryCompatible`
（`1 ∈ A∖B`、`2 ∈ B∖A`、`0 ∈ A∩B` 三者俱全）——
故 EJM 的 `BinaryCompatible` 对 two-state 完美系统发生**过强** ✗。 -/
theorem not_binaryCompatible_witness :
    ¬ BinaryCompatible ({0, 1} : Finset (Fin 3)) {0, 2} := by
  unfold BinaryCompatible
  decide

/-- ★B/★C 同一对**确实** `SidesCompatible`（第 4 项 `A ∪ B = univ`：`{0,1} ∪ {0,2} = univ`）。 -/
theorem sidesCompatible_witness :
    SidesCompatible ({0, 1} : Finset (Fin 3)) {0, 2} :=
  Or.inr (Or.inr (Or.inr (by decide)))

/-- ★C **端到端**：这 2 个字符的完美系统发生**存在**（3 叶星形树，中心标 `(1,1)`）。 -/
theorem exists_cladogram_displays_pair {A B : Finset X}
    (h : SidesCompatible A B) (h3 : 3 ≤ Fintype.card X) :
    ∃ T : Cladogram.{u, u} X, DisplaysBinary T A ∧ DisplaysBinary T B := by
  classical
  have hpair : ∀ i j : Fin 2, i ≠ j →
      SidesCompatible (if i = 0 then A else B) (if j = 0 then A else B) := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact h
    · exact sidesCompatible_comm.mp h
    · exact absurd rfl hij
  obtain ⟨T, hT⟩ := exists_cladogram_displays_of_pairwise_sidesCompatible
    (fun i : Fin 2 => if i = 0 then A else B) hpair h3
  have h10 : ¬ ((1 : Fin 2) = 0) := by decide
  exact ⟨T, by simpa using hT 0, by simpa [h10] using hT 1⟩

/-- ★C 最小例子的实例：`Fin 3` 上的 `{0,1}` 与 `{0,2}` 由同一棵树展示。 -/
theorem perfectPhylogeny_pair_witness :
    ∃ T : Cladogram.{0, 0} (Fin 3),
      DisplaysBinary T ({0, 1} : Finset (Fin 3)) ∧
        DisplaysBinary T ({0, 2} : Finset (Fin 3)) :=
  exists_cladogram_displays_pair sidesCompatible_witness (by decide)

/-- ★B **二元最小障碍（四个 gamete 本体）**：4 个 taxon `Fin 4` ≙ `00,01,10,11`，
字符 `a` 的 1-类 `{2,3}`（`10,11`）、`b` 的 1-类 `{1,3}`（`01,11`）——
`SidesCompatible` **为假**，即 Theorem 1.1 中的四 gamete 反例（`F₂`，`LamGusfieldSridhar2009` 1275–1280 行）。 -/
theorem fourGametes_obstruction :
    ¬ SidesCompatible ({2, 3} : Finset (Fin 4)) {1, 3} := by
  unfold SidesCompatible
  decide

/-- 上面那对字符**确实**含全部四个 gamete：`w=3`(`11`)、`x=2`(`10`)、`y=1`(`01`)、`z=0`(`00`)。 -/
example : ∃ w x y z : Fin 4,
    w ∈ ({2, 3} : Finset (Fin 4)) ∩ {1, 3} ∧
      x ∈ ({2, 3} : Finset (Fin 4)) \ {1, 3} ∧
      y ∈ ({1, 3} : Finset (Fin 4)) \ {2, 3} ∧
      z ∈ (({2, 3} : Finset (Fin 4)) ∪ {1, 3})ᶜ :=
  ⟨3, 2, 1, 0, by decide, by decide, by decide, by decide⟩

/-- **非空真**：相容性不是空话 —— `SidesCompatible` 在具体集合上成立与不成立各有实例。 -/
example : SidesCompatible (∅ : Finset (Fin 3)) {0} :=
  sidesCompatible_of_eq_empty_or_univ (Or.inl rfl)

/-- **非空真**：`HasPerfectPhylogeny` 不是空话 —— 上面那个 2 字符矩阵确实有完美系统发生。 -/
theorem hasPerfectPhylogeny_pair_witness :
    HasPerfectPhylogeny (fun i : Fin 2 => fun x : Fin 3 =>
      if i = 0 then (x ≠ 2) else (x ≠ 1)) := by
  have h0 : charOneClass (fun i : Fin 2 => fun x : Fin 3 =>
      if i = 0 then (x ≠ 2) else (x ≠ 1)) 0 = ({0, 1} : Finset (Fin 3)) := by
    ext x
    simp only [charOneClass, mem_binaryFactor, Fin.isValue]
    fin_cases x <;> decide
  have h1 : charOneClass (fun i : Fin 2 => fun x : Fin 3 =>
      if i = 0 then (x ≠ 2) else (x ≠ 1)) 1 = ({0, 2} : Finset (Fin 3)) := by
    ext x
    simp only [charOneClass, mem_binaryFactor, Fin.isValue]
    fin_cases x <;> decide
  obtain ⟨T, hTA, hTB⟩ := perfectPhylogeny_pair_witness
  refine ⟨T, fun i => ?_⟩
  fin_cases i
  · show DisplaysBinary T (charOneClass (fun i : Fin 2 => fun x : Fin 3 =>
      if i = 0 then (x ≠ 2) else (x ≠ 1)) 0)
    rw [h0]; exact hTA
  · show DisplaysBinary T (charOneClass (fun i : Fin 2 => fun x : Fin 3 =>
      if i = 0 then (x ≠ 2) else (x ≠ 1)) 1)
    rw [h1]; exact hTB

/-! ## §5 与 `Phylo/Compatibility.lean`（EJM 树偏序层）的接口 -/

/-- `Bool`（两态）是**树偏序**（全序），故 EJM 的树偏序器材适用于 two-state 字符。 -/
theorem isTreePoset_bool : IsTreePoset Bool := by
  intro a b c _ _
  exact le_total a b

/-! ## §6 缺口（显式 `def … : Prop`，**未证**）

⚠️ 以下两条**只是把目标陈述写清楚**（`def … : Prop`，非 `theorem`，**不引入任何公理**），
以便后续批次对着它们做；**不得**把它们当作已证结论引用。 -/

/-- **顶点集连通**（`SimpleGraph` 上）：`S` 中任意两点可用一条**整条落在 `S` 内**的 walk 相连。

这是 Gusfield 条件 (3)「forms a connected subtree of T」所需的**新词汇**（库内没有）。 -/
def IsConnectedSet {V : Type*} (G : SimpleGraph V) (S : Set V) : Prop :=
  ∀ u ∈ S, ∀ v ∈ S, ∃ p : G.Walk u v, ∀ w ∈ p.support, w ∈ S

/-- **多状态字符的「展示」关系（Gusfield 条件 (3) 的忠实形式化）**：
`χ : X → St` 被 `T` 展示 ⟺ 存在把 `T` **全体顶点**按 `St` 标注的函数 `ℓ`，
使叶上 `ℓ` 与 `χ` 一致、且每个状态的原像在 `T` 中**连通**。

⚠️ 与 `DisplaysBinary`/`IsSideOf` 的关系：对 `|St| = 2` 两者**等价**；
对 `|St| ≥ 3` 「连通」**严格更弱**（`{b,c}` 在毛虫树上连通但非边侧）。 -/
def DisplaysMultiState {St : Type v} (T : Cladogram X) (χ : X → St) : Prop :=
  ∃ ℓ : T.V → St, (∀ x : X, ℓ (T.leaf x) = χ x) ∧
    ∀ s : St, IsConnectedSet T.graph {v | ℓ v = s}

/-- **缺口 G1（未证）**：Gusfield 条件 (3) 的「连通子树」语义对 **r = 2** 与库内
`Cladogram.IsSideOf`（边侧）**一致** —— 即「两个状态类都连通 ⟺ 1-类是某条边的叶侧」。
**缺什么**：`IsConnectedSet` 与 `IsSideOf` 之间的树连通性引理（需 `T - e` 的分量分析）。
**为什么**：库内只有「边侧」，而条件 (3) 用的是「连通」，二者的差别正是多状态反例的所在。 -/
def BinaryConnectedEqualsSideGap : Prop :=
  ∀ (T : Cladogram.{u, u} X) (A : Finset X),
    (∃ ℓ : T.V → Bool, (∀ x : X, ℓ (T.leaf x) = true ↔ x ∈ A) ∧
      ∀ s : Bool, IsConnectedSet T.graph {v | ℓ v = s}) ↔ DisplaysBinary T A

/-- **缺口 G2（未证）**：**多状态时两两相容不充分** —— Fitch–Meacham `F₃`
（5 taxa × 3 字符 × 3 状态：`021, 100, 002, 220, 111`；`LamGusfieldSridhar2009`
1256–1273 行构造、1283–1284 行 `EC1={a0,b2,c1}`/`EC2={a1,b0,c0}`）。

陈述：存在这样的矩阵，使**任意两个**字符都有完美系统发生，而**三个一起**没有。

**文献**：`LamGusfieldSridhar2009` 摘要 48–58 行、**Theorem 2.4**（276–278 行，
`r = 3` 时判据要检查**三元组**而非二元组）、**Theorem 7.1**（1290–1292 行）、Fitch 例（131–140 行）。
**缺什么**：`DisplaysMultiState`（上面已给定义）上的存在/不存在性证明 ——
「不存在」需遍历（同构类下的）全部 `Cladogram`，库内尚无此枚举/不变量。
**为什么**：这正是 two-state（Theorem 1.1）与多状态（Theorem 2.4）的**分界**。 -/
def MultiStatePairwiseInsufficiencyGap : Prop :=
  ∃ M : Fin 3 → Fin 5 → Fin 3,
    (∀ i j : Fin 3, i ≠ j →
      ∃ T : Cladogram.{0, 0} (Fin 5),
        DisplaysMultiState T (M i) ∧ DisplaysMultiState T (M j)) ∧
    ¬ (∃ T : Cladogram.{0, 0} (Fin 5), ∀ i : Fin 3, DisplaysMultiState T (M i))